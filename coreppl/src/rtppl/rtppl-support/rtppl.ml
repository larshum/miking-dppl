type time_stamped_value = int * Obj.t

external lv_read_stub : int -> time_stamped_value = "lv_read_stub"
external lv_write_stub : int -> time_stamped_value -> unit = "lv_write_stub"
external lv_read_float_stub : int -> time_stamped_value = "lv_read_float_stub"
external lv_write_float_stub : int -> time_stamped_value -> unit = "lv_write_float_stub"

let lv_read (id : int) : time_stamped_value =
  let (ts, value) = lv_read_stub id in
  (ts, Marshal.from_bytes (Obj.obj value) 0)

let lv_read_float (id : int) : time_stamped_value = lv_read_float_stub id

let lv_write (id : int) (tsv : time_stamped_value) : unit =
  let (ts, value) = tsv in
  lv_write_stub id (ts, Obj.repr (Marshal.to_bytes value []))

let lv_write_float (id : int) (tsv : time_stamped_value) : unit =
  lv_write_float_stub id tsv

let read_binary (ch : in_channel) : Obj.t =
  Obj.repr (input_value ch)

let write_binary (ch : out_channel) (data : Obj.t) : unit =
  output_value ch (Obj.obj data)

type signal = int

let set_signal_handler (x : signal) (f : signal -> unit) : unit =
  Sys.set_signal x (Sys.Signal_handle f)

external clock_get_time : unit -> int * int = "clock_get_time_stub"
external clock_nanosleep : int * int -> unit = "clock_nanosleep_stub"

external set_priority : int -> int = "set_priority_stub"

let set_max_priority (_ : unit) : int = set_priority 255

external read_float_named_pipe : string -> (int * float) array = "read_float_named_pipe_stub"
external write_float_named_pipe : string -> float -> int * int -> unit = "write_float_named_pipe_stub"
