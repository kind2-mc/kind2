
val generate_uid : unit -> string

type running_job_info =

    {

      (* PID of process *)
      job_pid : int;

      (* Timestamp of job start *)
      job_start_timestamp : int;

      (* Name of file to be fed to standard input *)
      job_stdin_fn : string;

      (* Name of file to write standard output to *)
      job_stdout_fn : string;

      (* Name of file to write standard error to *)
      job_stderr_fn : string;

      (* Last read position in stardard output file *)
      mutable job_stdout_pos : int
      
    }

(** [create_job c a f] executes the command [c] with arguments [a] on
    the given file [f] and returns a tuple of an XML response, the job
    ID, and a record with information about the created job, if it was
    successfully started, [None] otherwise. *)

val create_job : string -> string list -> string -> string * string * running_job_info option

  (* val cancel_job : string  -> string *)
val retrieve_job : string -> running_job_info -> job_info

