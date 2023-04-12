#include <errno.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

#include "shared_mem.h"       // shared memory definitions file
#include "shared_mem_conf.h"

static int initialized = 0;

static sensor_val_t sensor_data[SM_OBJECT_COUNT];

void initIfNeeded() {
  if (initialized != 1) {
    sm_open_all();
    initialized = 1;
  }
}

value lv_read_helper(value ocamlPort, value tsv, bool isFloat) {
  int port = Long_val(ocamlPort);
  initIfNeeded();
  tsv = caml_alloc_tuple(2);
  if (isFloat) {
    sm_read(&sm_regs[port], &sensor_data[port]);
    Store_field(tsv, 0, Val_long(sensor_data[port].ts));
    Store_field(tsv, 1, caml_copy_double(sensor_data[port].val));
  } else {
    shared_mem_t *sm = &sm_regs[port];

    // Take the mutex
    if (sem_wait(sm->mgmt->mutex) == -1) {
      SM_PRINT_ERROR("waiting for mutex %s -> %s", sm->mgmt->mutexName, strerror(errno));
    } else {
      SM_PRINT_INFO("Successfully took mutex %s!", sm->mgmt->mutexName);
    }

    // Copy the content from the shared memory
    long long l;
    memcpy((void*)&l, sm->data_p, sizeof(long long));
    Store_field(tsv, 0, Val_long(l));
    Store_field(tsv, 1, caml_copy_string(sm->data_p+sizeof(long long)));

    // Give the mutex back
    if (sem_post(sm->mgmt->mutex) == -1) {
      SM_PRINT_ERROR("returning mutex %s -> %s", sm->mgmt->mutexName, strerror(errno));
    } else {
      SM_PRINT_INFO("Successfully returned mutex %s!", sm->mgmt->mutexName);
    }
  }
  return tsv;
}

void lv_write_helper(value ocamlPort, value tsv, bool isFloat) {
  int port = Int_val(ocamlPort);
  initIfNeeded();
  if (isFloat) {
    sensor_data[port].ts = Long_val(Field(tsv, 0));
    sensor_data[port].val = Double_val(Field(tsv, 1));
    sm_write(&sm_regs[port], &sensor_data[port]);
  } else {
    shared_mem_t *sm = &sm_regs[port];

    // Take the mutex
    if (sem_wait(sm->mgmt->mutex) == -1) {
      SM_PRINT_ERROR("waiting for mutex %s -> %s", sm->mgmt->mutexName, strerror(errno));
    } else {
      SM_PRINT_INFO("Successfully took mutex %s!", sm->mgmt->mutexName);
    }

    // Copy the content to the shared memory
    long long l = Long_val(Field(tsv, 0));
    memcpy(sm->data_p, (void*)&l, sizeof(long long));
    int n = caml_string_length(Field(tsv, 1));
    memcpy(sm->data_p+sizeof(long long), Bytes_val(Field(tsv, 1)), n);

    // Give the mutex back
    if (sem_post(sm->mgmt->mutex) == -1) {
      SM_PRINT_ERROR("returning mutex %s -> %s", sm->mgmt->mutexName, strerror(errno));
    } else {
      SM_PRINT_INFO("Successfully returned mutex %s!", sm->mgmt->mutexName);
    }
  }
}

value lv_read_stub(value ocamlPort) {
  CAMLparam1(ocamlPort);
  CAMLlocal1(tsv);
  tsv = lv_read_helper(ocamlPort, tsv, false);
  CAMLreturn(tsv);
}

value lv_read_float_stub(value ocamlPort) {
  CAMLparam1(ocamlPort);
  CAMLlocal1(tsv);
  tsv = lv_read_helper(ocamlPort, tsv, true);
  CAMLreturn(tsv);
}

void lv_write_stub(value ocamlPort, value tsv) {
  CAMLparam2(ocamlPort, tsv);
  lv_write_helper(ocamlPort, tsv, false);
  CAMLreturn0;
}

void lv_write_float_stub(value ocamlPort, value tsv) {
  CAMLparam2(ocamlPort, tsv);
  lv_write_helper(ocamlPort, tsv, true);
  CAMLreturn0;
}
