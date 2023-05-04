#include <mutex>
#include <queue>
#include <thread>

#include <csignal>
#include <cstdio>
#include <fcntl.h>
#include <unistd.h>

struct payload {
  char* data;
  int64_t sz;
};

std::queue<payload> buffer;
std::mutex mtx;

int in = -1;
std::vector<int> out_fds;
std::string id;

void close_fds() {
  if (in != -1) close(in);
  for (int fd : out_fds) {
    close(fd);
  }
}

void fail_open(const char *f) {
  fprintf(stderr, "[%s] Could not open pipe %s: %s\n", id.c_str(), f, strerror(errno));
  exit(1);
}

void fail_read(int line) {
  fprintf(stderr, "[%s] Error on line %d when reading: %s\n", id.c_str(), line, strerror(errno));
  exit(1);
}

void fail_write(int line) {
  fprintf(stderr, "[%s] Error on line %d when writing: %s\n", id.c_str(), line, strerror(errno));
  exit(1);
}

void exit_eof() {
  fprintf(stderr, "[%s] Found EOF when reading, exiting now\n", id.c_str());
  exit(0);
}

void sanity_check(int64_t sz) {
  if (sz > (int64_t)1e9) {
    fprintf(stderr, "[%s] Read unreasonable input size: 0x%llx (%llu)\n", id.c_str(), sz, sz);
    exit(1);
  }
}

int64_t read_size() {
  char buf[sizeof(int64_t)];
  int64_t tot = 0;
  while (tot < sizeof(int64_t)) {
    int count = read(in, (void*)&buf[tot], sizeof(int64_t));
    if (count == 0) exit_eof();
    if (count < 0) fail_read(__LINE__);
    tot += count;
  }
  int64_t sz;
  memcpy((void*)&sz, buf, sizeof(int64_t));
  sanity_check(sz);
  return sz;
}

void read_task() {
  while (true) {
    payload p;
    p.sz = read_size();
    p.data = (char*)malloc(p.sz);
    int64_t tot = 0;
    while (tot < p.sz) {
      int count = read(in, (void*)&p.data[tot], p.sz-tot);
      if (count == 0) exit_eof();
      if (count < 0) fail_read(__LINE__);
      tot += count;
    }
    mtx.lock();
    buffer.push(p);
    mtx.unlock();
  }
}

void write_fd(const payload& p, size_t idx) {
  int out = out_fds[idx];
  int64_t tot = 0;
  while (tot < p.sz) {
    int count = write(out, (void*)&p.data[tot], p.sz-tot);
    if (count == 0) exit_eof();
    if (count < 0) fail_write(__LINE__);
    tot += count;
  }
}

void write_combined(const payload& p) {
  for (int i = 0; i < out_fds.size(); i++) {
    write_fd(p, i);
  }
}

payload combine_payloads(const std::vector<payload>& pls) {
  payload combined;
  combined.sz = 0;
  for (const payload& p : pls) {
    combined.sz += p.sz + sizeof(int64_t);
  }
  combined.data = (char*)malloc(combined.sz);
  size_t pos = 0;
  for (const payload& p : pls) {
    memcpy(&combined.data[pos], (void*)&p.sz, sizeof(int64_t));
    pos += sizeof(int64_t);
    memcpy(&combined.data[pos], p.data, p.sz);
    pos += p.sz;
    free(p.data);
  }
  return combined;
}

void write_task() {
  while (true) {
    if (buffer.empty()) {
      std::this_thread::yield();
      continue;
    }
    std::vector<payload> pls;
    mtx.lock();
    while (!buffer.empty()) {
      pls.emplace_back(buffer.front());
      buffer.pop();
    }
    mtx.unlock();
    const payload& p = combine_payloads(pls);
    write_combined(p);
    free(p.data);
  }
}

void notify_termination(int sig) {
  std::vector<payload> pls;
  while (!buffer.empty()) {
    pls.emplace_back(buffer.front());
    buffer.pop();
  }
  if (!pls.empty()) {
    const payload &p = combine_payloads(pls);
    write_fd(p, out_fds.size()-1);
    free(p.data);
  }
  close_fds();
  exit(0);
}

int main(int argc, char **argv) {
  id = argv[1];
  in = open(id.c_str(), O_RDWR);
  if (in == -1) fail_open(id.c_str());
  for (int i = 2; i < argc; i++) {
    const char *dst = argv[i];
    int out = open(dst, O_RDWR);
    if (out == -1) fail_open(dst);
    out_fds.push_back(out);
  }
  // Also write to an appropriately named file for reproducibility.
  std::string target = id + ".txt";
  if (access(target.c_str(), F_OK) == 0) {
    unlink(target.c_str());
  }
  int out = open(target.c_str(), O_WRONLY | O_CREAT, S_IRUSR | S_IWUSR);
  if (out == -1) fail_open(target.c_str());
  out_fds.push_back(out);
  signal(SIGINT, notify_termination);
  signal(SIGKILL, notify_termination);
  std::thread reader(read_task);
  reader.detach();
  write_task();
  close_fds();
  return 0;
}
