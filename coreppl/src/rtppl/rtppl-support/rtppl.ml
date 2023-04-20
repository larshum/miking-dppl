type signal = int

let set_signal_handler (x : signal) (f : signal -> unit) : unit =
  Sys.set_signal x (Sys.Signal_handle f)

type timespec = int * int
type 'a tsv = timespec * 'a
type opaque

external clock_get_time : unit -> timespec = "clock_get_time_stub"
external clock_nanosleep : timespec -> unit = "clock_nanosleep_stub"

external set_priority : int -> int = "set_priority_stub"

let set_max_priority (_ : unit) : int = set_priority 255

external read_float_named_pipe : string -> (float tsv) array = "read_float_named_pipe_stub"
external write_float_named_pipe : string -> float -> timespec -> unit = "write_float_named_pipe_stub"
external read_dist_float_record_named_pipe
  : string -> int -> ((float * opaque) array tsv) array
  = "read_dist_float_record_named_pipe_stub"
external write_dist_float_record_named_pipe
  : string -> opaque array * float array -> timespec -> int -> unit
  = "write_dist_float_record_named_pipe_stub"
