#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
#include <unistd.h>
#include <iostream>
#include <vector>

struct payload {
  char *data;
  int64_t size;
};

int min(int a, int b) {
  if (a < b) return a;
  return b;
}

int64_t read_message_size(int fd) {
  char buffer[sizeof(int64_t)];
  int64_t count = 0;
  while (count < sizeof(int64_t)) {
    int bytes = read(fd, (void*)&buffer[count], sizeof(int64_t)-count);
    if (bytes < 0) {
      if (count > 0 && errno == EAGAIN) continue;
      return -1;
    }
    count += bytes;
  }
  int64_t sz;
  memcpy((void*)&sz, buffer, sizeof(int64_t));
  return sz;
}

int64_t read_message(int fd, payload& p) {
  p.size = read_message_size(fd);
  if (p.size == -1) {
    return false;
  }
  p.data = (char*)malloc(p.size);
  int64_t count = 0;
  while (count < p.size) {
    int bytes_read = read(fd, (void*)&p.data[count], p.size - count);
    if (bytes_read <= 0) {
      if (errno == EAGAIN) continue;
      fprintf(stderr, "Error reading message: %s\n", strerror(errno));
      exit(1);
    }
    count += bytes_read;
  }
  return true;
}

std::vector<payload> read_messages(int fd) {
  std::vector<payload> input_seq;
  payload p;
  while (read_message(fd, p)) {
    input_seq.emplace_back(p);
  }
  return input_seq;
}

bool write_message_size(int fd, int64_t sz) {
  char buffer[sizeof(int64_t)];
  memcpy((void*)buffer, (void*)&sz, sizeof(int64_t));
  int64_t count = 0;
  while (count < sizeof(int64_t)) {
    int bytes = write(fd, (void*)&buffer[count], sizeof(int64_t)-count);
    if (bytes < 0) {
      if (errno == EAGAIN) continue;
      return false;
    }
    count += bytes;
  }
  return true;
}

void write_message(int fd, const payload& p) {
  bool res = write_message_size(fd, p.size);
  if (!res) {
    fprintf(stderr, "Error writing message: %s\n", strerror(errno));
    exit(1);
  }
  int64_t count = 0;
  while (count < p.size) {
    int bytes_written = write(fd, (void*)&p.data[count], p.size - count);
    if (bytes_written <= 0) {
      fprintf(stderr, "Error writing message: %s\n", strerror(errno));
      exit(1);
    }
    count += bytes_written;
  }
}

value to_timespec_value(int64_t ts) {
  int64_t sec = ts / (int64_t)1e9;
  int64_t nsec = ts % (int64_t)1e9;
  value timespec = caml_alloc(2, 0);
  Store_field(timespec, 0, Val_long(sec));
  Store_field(timespec, 0, Val_long(nsec));
  return timespec;
}

int64_t timespec_value_to_int64(value ts) {
  int64_t sec = Long_val(Field(ts, 0));
  int64_t nsec = Long_val(Field(ts, 1));
  return sec * (int64_t)1e9 + nsec;
}

value read_float_payload(const payload& p) {
  int64_t ts;
  memcpy(&ts, (char*)p.data, sizeof(int64_t));
  value timespec = to_timespec_value(ts);
  value tsv = caml_alloc(2, 0);
  Store_field(tsv, 0, timespec);
  double val;
  memcpy(&val, (char*)p.data + sizeof(int64_t), sizeof(double));
  Store_field(tsv, 1, caml_copy_double(val));
  free(p.data);
  return tsv;
}

payload write_float_payload(value msg, value ts) {
  payload p;
  p.size = sizeof(int64_t) + sizeof(double);
  p.data = (char*)malloc(p.size);
  int64_t timestamp = timespec_value_to_int64(ts);
  memcpy(p.data, (void*)&timestamp, sizeof(int64_t));
  double data = Double_val(msg);
  memcpy(p.data + sizeof(int64_t), (void*)&data, sizeof(double));
  return p;
}

value read_dist_float_record_payload(const payload& p, int64_t nfields) {
  int64_t nsamples = (p.size - sizeof(int64_t)) / ((nfields + 1) * sizeof(double));
  char *ptr = p.data;
  int64_t timestamp;
  memcpy((void*)&timestamp, ptr, sizeof(int64_t));
  ptr += sizeof(int64_t);
  value ts = to_timespec_value(timestamp);
  value dist_samples = caml_alloc(nsamples, 0);
  for (size_t i = 0; i < nsamples; i++) {
    double weight;
    memcpy((void*)&weight, ptr, sizeof(double));
    value w = caml_copy_double(weight);
    ptr += sizeof(double);
    value s = caml_alloc(nfields, 0);
    for (size_t j = 0; j < nfields; j++) {
      double tmp;
      memcpy((void*)&tmp, ptr, sizeof(double));
      Store_field(s, j, caml_copy_double(tmp));
      ptr += sizeof(double);
    }
    value sample = caml_alloc(2, 0);
    Store_field(sample, 0, w);
    Store_field(sample, 1, s);
    Store_field(dist_samples, i, sample);
  }
  value tsv = caml_alloc(2, 0);
  Store_field(tsv, 0, ts);
  Store_field(tsv, 1, dist_samples);
  return tsv;
}

payload write_dist_float_record_payload(value d, value ts, value nfields_val) {
  value samples = Field(d, 0);
  value log_weights = Field(d, 1);
  int64_t nsamples = Wosize_val(samples);
  int64_t nfields = Long_val(nfields_val);
  payload p;
  // The payload consists of a timestamp, log weights, and sample data
  p.size = sizeof(int64_t) + nsamples * sizeof(double) + nsamples * nfields * sizeof(double);
  p.data = (char*)malloc(p.size);
  char *ptr = p.data;
  int64_t timestamp = timespec_value_to_int64(ts);
  memcpy(ptr, (void*)&timestamp, sizeof(int64_t));
  ptr += sizeof(int64_t);
  for (size_t i = 0; i < nsamples; i++) {
    double tmp = Double_field(log_weights, i);
    memcpy(ptr, (void*)&tmp, sizeof(double));
    ptr += sizeof(double);
    value rec = Field(samples, i);
    for (size_t j = 0; j < nfields; j++) {
      tmp = Double_val(Field(rec, j));
      memcpy(ptr, (void*)&tmp, sizeof(double));
      ptr += sizeof(double);
    }
  }
  return p;
}

int open_pipe(value pipe, int flags) {
  const char *pipe_id = String_val(pipe);
  int fd = open(pipe_id, flags);
  if (fd == -1) {
    fprintf(stderr, "Error: could not open pipe %s\n", pipe_id);
    exit(1);
  }
  return fd;
}

int open_pipe_nonblock(value pipe) {
  return open_pipe(pipe, O_RDWR | O_NONBLOCK);
}

int open_pipe_blocking(value pipe) {
  return open_pipe(pipe, O_RDWR);
}

extern "C" {

  value read_float_named_pipe_stub(value pipe) {
    CAMLparam1(pipe);
    CAMLlocal1(out);

    int fd = open_pipe_nonblock(pipe);
    std::vector<payload> input_seq = read_messages(fd);
    close(fd);

    out = caml_alloc(input_seq.size(), 0);
    for (size_t i = 0; i < input_seq.size(); i++) {
      Store_field(out, i, read_float_payload(input_seq[i]));
    }
    CAMLreturn(out);
  }

  void write_float_named_pipe_stub(value pipe, value msg, value ts) {
    CAMLparam3(pipe, msg, ts);

    int fd = open_pipe_blocking(pipe);
    payload p = write_float_payload(msg, ts);
    write_message(fd, p);
    free(p.data);
    close(fd);

    CAMLreturn0;
  }

  value read_dist_float_record_named_pipe_stub(value pipe, value nfields_val) {
    CAMLparam2(pipe, nfields_val);
    CAMLlocal1(out);

    int fd = open_pipe_nonblock(pipe);
    std::vector<payload> input_seq = read_messages(fd);
    close(fd);

    int64_t nfields = Long_val(nfields_val);
    out = caml_alloc(input_seq.size(), 0);
    for (size_t i = 0; i < input_seq.size(); i++) {
      Store_field(out, i, read_dist_float_record_payload(input_seq[i], nfields));
    }
    CAMLreturn(out);
  }

  void write_dist_float_record_named_pipe_stub(value pipe, value msg, value ts, value nfields) {
    CAMLparam3(pipe, msg, ts);

    int fd = open_pipe_blocking(pipe);
    payload p = write_dist_float_record_payload(msg, ts, nfields);
    write_message(fd, p);
    free(p.data);
    close(fd);

    CAMLreturn0;
  }

}
