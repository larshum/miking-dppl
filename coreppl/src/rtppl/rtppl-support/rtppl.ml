type signal = int

let set_signal_handler (x : signal) (f : signal -> unit) : unit =
  Sys.set_signal x (Sys.Signal_handle f)

type timespec = int * int
type 'a tsv = timespec * 'a
type opaque

external get_monotonic_time : unit -> timespec = "clock_monotonic_time_stub"
external get_wall_clock_time : unit -> timespec = "clock_wall_time_stub"
external clock_nanosleep : timespec -> unit = "clock_nanosleep_stub"

external set_priority : int -> int = "set_priority_stub"
let set_max_priority (_ : unit) : int = set_priority 255

external open_file_nonblocking : string -> int = "open_file_nonblocking_stub"
external close_file_descriptor : int -> unit = "close_file_descriptor_stub"

external read_float_named_pipe : int -> (float tsv) array = "read_float_named_pipe_stub"
external write_float_named_pipe : int -> float tsv -> unit = "write_float_named_pipe_stub"
external read_dist_float_record_named_pipe
  : int -> int -> ((float * opaque) array tsv) array
  = "read_dist_float_record_named_pipe_stub"
external write_dist_float_record_named_pipe
  : int -> int -> (opaque array * float array) tsv -> unit
  = "write_dist_float_record_named_pipe_stub"
