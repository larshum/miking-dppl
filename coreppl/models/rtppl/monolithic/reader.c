#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

int fd;
FILE *out;
int run = 1;
void close_files() {
  close(fd);
  fclose(out);
}

void on_stop(int sig) {
  if (run) {
    run = 0;
  } else {
    close_files();
    exit(0);
  }
}

void fail(int ln) {
  printf("Reader failure on line %d: %s\n", ln, strerror(errno));
  exit(1);
}

int main(int argc, char **argv) {
  signal(SIGINT, on_stop);
  fd = open("pos-posDist", O_RDWR);
  if (fd == -1) fail(__LINE__);
  out = fopen("pos.txt", "wb");
  if (out == NULL) fail(__LINE__);
  while (run) {
    int64_t sz;
    int count = read(fd, (void*)&sz, sizeof(int64_t));
    if (count != sizeof(int64_t)) fail(__LINE__);
    if (fwrite((void*)&sz, sizeof(int64_t), 1, out) == -1) fail(__LINE__);
    char *buf = (char*)malloc(sz);
    int64_t n = 0;
    while (n < sz) {
      count = read(fd, (void*)&buf[n], sz-n);
      if (count > 0) {
        if (fwrite((void*)&buf[n], count, 1, out) == -1) fail(__LINE__);
      } else fail(__LINE__);
      n += count;
    }
  }
  close_files();
  return 0;
}
