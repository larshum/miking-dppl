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

struct dist {
  int64_t nsamples;
  bool degenerate;
  double normConst;
  std::vector<double> log_weights;
  std::vector<double> samples;
  std::vector<double> weights;
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

std::vector<payload<dist>> read_dist_messages(int fd, int64_t nfields) {
  std::vector<payload<dist>> input_seq;
  while (true) {
    payload<dist> input;
    int elems = read(fd, (void*)&input.ts, sizeof(int64_t));
    if (elems == 0) break;
    elems = read(fd, (void*)&input.val.nsamples, sizeof(int64_t));
    if (elems == 0) break;
    elems = read(fd, (void*)&input.val.degenerate, sizeof(int64_t));
    if (elems == 0) break;
    elems = read(fd, (void*)&input.val.normConst, sizeof(double));
    if (elems == 0) break;
    // For each sample of a distribution, we have one log-weight and one
    // weight, as well as one float for each element in the record.
    int64_t n = (nfields + 2) * input.val.nsamples;
    double buffer[n];
    elems = read(fd, (void*)&buffer, sizeof(buffer));
    if (elems != n) break;
    double *samples_offset = buffer + input.val.nsamples;
    double *weights_offset = samples_offset + nfields * input.val.nsamples;
    input.val.log_weights = std::vector<double>(buffer, samples_offset);
    input.val.weights = std::vector<double>(samples_offset, weights_offset);
    input.val.samples = std::vector<double>(weights_offset, buffer + n);
    input_seq.emplace_back(input);
  }
  return input_seq;
}

int64_t write_dist_float_record_buffer(value d, char *buffer, int64_t nfields) {
  value degen = Field(d, 0);
  value norm_const = Field(Field(d, 1), 0);
  value log_weights = Field(d, 2);
  value samples = Field(d, 3);
  value weights = Field(d, 4);
  int64_t nsamples = Wosize_val(log_weights);
  // The buffer contains the timestamp plus all fields required to encode a
  // distribution.
  size_t sz = (nfields + 2) * nsamples + 3 * sizeof(int64_t) + sizeof(double);
  buffer = (char*)malloc(sz);
  char *nsamples_offset = buffer + sizeof(int64_t);
  char *degen_offset = nsamples_offset + sizeof(int64_t);
  char *nc_offset = degen_offset + sizeof(int64_t);
  memcpy(buffer, &nsamples, sizeof(int64_t));
  int64_t degen_tmp = Bool_val(degen);
  memcpy(degen_offset, &degen_tmp, sizeof(int64_t));
  double nc_tmp = Double_val(norm_const);
  memcpy(nc_offset, &nc_tmp, sizeof(double));
  char *ptr = nc_offset + sizeof(double);
  double tmp;
  for (size_t i = 0; i < nsamples; i++) {
    tmp = Double_val(Field(log_weights, i));
    memcpy(ptr, &tmp, sizeof(double));
    ptr += sizeof(double);
  }
  for (size_t i = 0; i < nsamples; i++) {
    tmp = Double_val(Field(weights, i));
    memcpy(ptr, &tmp, sizeof(double));
    ptr += sizeof(double);
  }
  for (size_t i = 0; i < nsamples; i++) {
    value rec = Field(samples, i);
    for (size_t j = 0; j < nfields; j++) {
      tmp = Double_val(Field(rec, j));
      memcpy(ptr, &tmp, sizeof(double));
      ptr += sizeof(double);
    }
  }
  return sz;
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

value to_float_array_value(const std::vector<double>& v) {
  value rec = caml_alloc(v.size(), 0);
  for (size_t i = 0; i < v.size(); i++) {
    Store_field(rec, i, caml_copy_double(v[i]));
  }
  return rec;
}

value to_dist_float_record_value(const dist& d) {
  // TODO(larshum, 2023-04-16): This will break if more distributions are added
  // in DPPL. Can we figure out the value of this tag in a safe way?
  const int EMPIRICAL_DIST_TAG = 11;
  value dist = caml_alloc(5, EMPIRICAL_DIST_TAG);
  Store_field(dist, 0, Val_bool(d.degenerate));
  // TODO(larshum, 2023-04-16): This breaks if using an inference algorithm
  // that does not contain a single double argument.
  value emp_norm = caml_alloc(1, 0);
  Store_field(emp_norm, 0, caml_copy_double(d.normConst));
  Store_field(dist, 1, emp_norm);
  Store_field(dist, 2, to_float_array_value(d.log_weights));
  Store_field(dist, 3, to_float_array_value(d.samples));
  Store_field(dist, 4, to_float_array_value(d.weights));
  return dist;
}

extern "C" {

  typedef payload<double> float_data_t;
  typedef payload<dist> dist_record_float_data_t;

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
      value timespec = to_timespec_value(input_seq[i].ts);
      value tsv = caml_alloc(2, 0);
      Store_field(tsv, 0, timespec);
      Store_field(tsv, 1, caml_copy_double(input_seq[i].val));
      Store_field(out, i, tsv);
    }
    CAMLreturn(out);
  }

  value read_dist_float_record_named_pipe_stub(value pipe, value nfields) {
    CAMLparam2(pipe, nfields);
    CAMLlocal1(out);

    int fd = open_pipe_file(pipe);
    int64_t fields = Long_val(nfields);
    std::vector<dist_record_float_data_t> input_seq = read_dist_messages(fd, fields);
    close(fd);

    out = caml_alloc(input_seq.size(), 0);
    for (size_t i = 0; i < input_seq.size(); i++) {
      value timespec = to_timespec_value(input_seq[i].ts);
      value tsv = caml_alloc(2, 0);
      Store_field(tsv, 0, timespec);
      Store_field(tsv, 1, to_dist_float_record_value(input_seq[i].val));
      Store_field(out, i, tsv);
    }

    CAMLreturn(out);
  }

  void write_float_named_pipe_stub(value pipe, value msg, value ts) {
    CAMLparam3(pipe, msg, ts);

    int fd = open_pipe_file(pipe);
    float_data_t message;
    message.ts = timespec_value_to_int64(ts);
    message.val = Double_val(msg);
    write(fd, (void*)&message, sizeof(float_data_t));
    close(fd);

    CAMLreturn0;
  }

  void write_dist_float_record_named_pipe_stub(value pipe, value msg, value ts, value nfields) {
    CAMLparam3(pipe, msg, ts);

    int fd = open_pipe_file(pipe);
    char *buffer;
    int64_t n = write_dist_float_record_buffer(msg, buffer, Long_val(nfields));
    int64_t t = timespec_value_to_int64(ts);
    memcpy(buffer, &t, sizeof(int64_t));
    write(fd, (void*)&buffer, n);
    free(buffer);
    close(fd);

    CAMLreturn0;
  }

}
