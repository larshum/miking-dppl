#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
#include <unistd.h>
#include <iostream>
#include <vector>

template <typename T>
struct payload {
  int64_t ts;
  T val;
};

template <typename T>
std::vector<payload<T>> read_messages(int fd) {
  std::vector<payload<T>> input_seq;
  while (true) {
    payload<T> msg;
    int elems = read(fd, (void*)&msg, sizeof(payload<T>));
    if (elems > 0) {
      input_seq.push_back(msg);
    } else {
      break;
    }
  }
  return input_seq;
}

extern "C" {

  typedef payload<double> float_data_t;

  int open_pipe_file(value pipe) {
    const char *pipe_id = String_val(pipe);
    int fd = open(pipe_id, O_RDWR | O_NONBLOCK);
    if (fd == -1) {
      fprintf(stderr, "Error: could not open pipe %s\n", pipe_id);
      exit(1);
    }
    return fd;
  }

  value read_float_named_pipe_stub(value pipe) {
    CAMLparam1(pipe);
    CAMLlocal1(out);

    int fd = open_pipe_file(pipe);
    std::vector<float_data_t> input_seq = read_messages<double>(fd);
    close(fd);

    out = caml_alloc(input_seq.size(), 0);
    for (size_t i = 0; i < input_seq.size(); i++) {
      value tsv = caml_alloc(2, 0);
      Store_field(tsv, 0, Val_long(input_seq[i].ts));
      Store_field(tsv, 1, caml_copy_double(input_seq[i].val));
      Store_field(out, i, tsv);
    }
    CAMLreturn(out);
  }

  void write_float_named_pipe_stub(value pipe, value msg, value ts) {
    CAMLparam3(pipe, msg, ts);

    int fd = open_pipe_file(pipe);
    float_data_t message;
    int64_t sec = Long_val(Field(ts, 0));
    int64_t nsec = Long_val(Field(ts, 1));
    message.ts = sec * 1000000000 + nsec;
    message.val = Double_val(msg);
    write(fd, (void*)&message, sizeof(float_data_t));
    close(fd);

    CAMLreturn0;
  }

}
