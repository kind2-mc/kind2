(* 
  can test in toplevel with "ocaml -I +threads unix.cma ZMQ.cma"
  and then just #use "server.ml". (need to uncomment the load for threads.cma)

  to compile (from directory containing ZMQ module/libraries):
    ocamlopt.opt /usr/local/lib/ocaml/unix.cmxa ZMQ.cmxa -ccopt -L. server.ml server.mli -o kind2server
*)

(*#load "threads.cma"*)
open ZMQ

exception Checksum_failure

(* ********************************************************************** *)
(* Defaults                                                               *)
(* ********************************************************************** *)

let helpmessage = "usage: kind2_server -[p] [port]"

(* Default port for the server *)
let default_port = 5558

(* ********************************************************************** *)
(* Helper functions                                                       *)
(* ********************************************************************** *)

(* Get base l string representation of integer n *)
let base10tol n =

  (* Characters to use *)
  let digits = 
    [|
      '0';'1';'2';'3';'4';'5';'6';'7';'8';'9';
      'A';'B';'C';'D';'E';'F';'G';'H';'I';'J';'K';'L';'M';
      'N';'O';'P';'Q';'R';'S';'T';'U';'V';'W';'X';'Y';'Z';
      'a';'b';'c';'d';'e';'f';'g';'h';'i';'j';'k';'l';'m';
      'n';'o';'p';'q';'r';'s';'t';'u';'v';'w';'x';'y';'z'
    |] 
  in

  (* l is number of characters *)
  let base = Array.length digits in

  (* Convert to base l *)
  let rec base_iter acc = function
    | 0 -> acc
    | n ->
      base_iter 
        ((String.make 1 (Array.get digits (n mod base))) ^ acc)
        (n / base) 
  in  

  (* Conver n to a base l string *)
  base_iter "" n

(* Generate unique identifier from current Unix time *)
let generate_uid () = 

  (* use current unix time to the 100th of a second, in GMT, hash to
     make it look random *)
  base10tol (Hashtbl.hash (int_of_float (Unix.gettimeofday () *. 100.)))


(* String representation of time *)
let string_of_tm t =

  Format.sprintf 
    "%d:%02d GMT on %02d/%02d/%04d"
    t.Unix.tm_hour
    t.Unix.tm_min
    (t.Unix.tm_mon + 1)
    t.Unix.tm_mday
    ((t.Unix.tm_year) + 1900)


(* Sleep for sec seconds *)
let minisleep sec =
  ignore (Unix.select [] [] [] sec)

(* ********************************************************************** *)
(* State of the server                                                    *)
(* ********************************************************************** *)

(* on which port does the server run? *)
let port = 
  match (Array.length Sys.argv) with 
  | 1 -> default_port
  | 3 -> 
    if ((Array.get Sys.argv 1) = "-P" || (Array.get Sys.argv 1 = "-p")) then (
      (try (
        (int_of_string (Array.get Sys.argv 2));
      ) with _ ->  
        print_endline "bad port number";
        exit 1
      );
    ) else (
      print_endline helpmessage;
      exit 1
    )
  | _ -> print_endline helpmessage;
         exit 1


(* print_endline ("launching Kind 2 server on port " ^ (string_of_int port)) *)

(* running_jobs: a Hashtbl of ID -> ( pid * stdin_file * stdout_file *
   stderr_file ) *)

let running_jobs = (Hashtbl.create 50)

(* completed_jobs: a Hashtbl of ID -> completion_time *)
let completed_jobs = (Hashtbl.create 50)

(* how long (in seconds) should a job remain before being purged? *)
let job_lifespan = 2629740 (* about one month *)

(* command to invoke kind *)
let kind_command = "/usr/local/bin/pkind";;
let kind_default_args = [| "-xml"; "-xml-to-stdout" |]

(* location of kind temporary directory *)
let tmpdir = ("/tmp/kind2-" ^ generate_uid ());;



let write_bytes_to_file data filename = 

  (* write contents of byte array 'data' to a file with name 'filename' *)
  let oc = open_out_bin filename in

  for i = 0 to ((Array.length data) - 1) do

    (* not using output_string for now, need to test results with binary data *)
    output_char oc (Array.get data i);

  done;

  close_out oc


let read_bytes filename =
  let ic = open_in_bin filename in
  let n = in_channel_length ic in
  let s = String.create n in
  really_input ic s 0 n;
  close_in ic;
  s


let create_job sock server_flags payload checksum kind_args =
  (* create new kind job using flags 'server_flags',
    and the content of 'payload'. send results over 'sock' *)
  
  (* generate a unique job ID *)
  let job_id = generate_uid () in 

  (* Create temporary files for input, output and error output *)
  let stdin_fn = ("kind_job_" ^ job_id ^ "_input") in
  let stdout_fn = ("kind_job_" ^ job_id ^ "_output") in

  (* write data from client to stdin of new kind process *)
  write_bytes_to_file (zframe_getbytes payload) stdin_fn;

  let kind_stdin_in = 
    Unix.openfile stdin_fn [Unix.O_CREAT; Unix.O_RDONLY; Unix.O_NONBLOCK] 0o600 
  in
  let kind_stdout_out = 
    Unix.openfile stdout_fn [Unix.O_CREAT; Unix.O_RDWR; Unix.O_NONBLOCK] 0o600 
  in
  
  (* do the server flags indicate that stdout and stderr should be seperated? *)
  let stderr_fn, kind_stderr_out = 
    if (String.contains server_flags 's') then 
      (
        (* seperate stderr and stdout *)
        ("kind_job_" ^ job_id ^ "_error"),
        Unix.openfile 
          ("kind_job_" ^ job_id ^ "_error") 
          [Unix.O_CREAT; Unix.O_RDWR; Unix.O_NONBLOCK] 0o600
      ) 
    else 
      (
        (* by default merge stdout and stderr *)
        stdout_fn, kind_stdout_out
      )
  in

  (* verify payload *)
  let s = zframe_strdup payload in
  let s' = Digest.string s in
  if (s' <> checksum) then (
    print_endline "Received file with bad MD5sum";
    print_endline ("Expected MD5sum: " ^ checksum); 
    print_endline ("Actual MD5sum: " ^ s'); 
    raise Checksum_failure
  );
  
  (* Create kind process *)
  let kind_pid = 
    Unix.create_process 
      kind_command
      (Array.append 
         (Array.append [|kind_command|] kind_default_args) 
         kind_args)
      kind_stdin_in
      kind_stdout_out
      kind_stderr_out
  in
  
  (* Close our end of the pipe which has been duplicated by the
     process *)
  if (not (kind_stderr_out == kind_stdout_out)) then 
    (Unix.close kind_stderr_out); 

  Unix.close kind_stdin_in;
  Unix.close kind_stdout_out; 
  
  (* add job to Hashtbl of running jobs and associated files *)
  Hashtbl.add 
    running_jobs job_id 
    (kind_pid, (int_of_float (Unix.time ())), stdin_fn, stdout_fn, stderr_fn);

  (* send job ID to client *)
  let msg = zmsg_new () in
  ignore(zmsg_pushstr msg job_id);
  ignore(zmsg_send msg sock);
  
  print_endline ("job created with ID " ^ job_id);

  (* guarantee that next generated ID is unique *)
  minisleep 0.01



let retrieve_job sock server_flags job_id = 

  (* retrieve job with ID 'job_id' using flags 'server_flags'.
       send results over 'sock' *)
  
  let status = zmsg_new () in
  
  (try 

     (
       
       (* try to retrieve the job *)
       let job_pid, timestamp, stdin_fn, stdout_fn, stderr_fn = 
         Hashtbl.find running_jobs job_id in
       
       (* check on status of job *)
       let job_pid, job_exitcode = Unix.waitpid [Unix.WNOHANG] job_pid in 
       
       if (job_pid = 0) then 

         (                        
           (* inform client that job is still running *)
           ignore(
             zmsg_pushstr status 
               (Format.sprintf 
                  "<Jobstatus msg=\"inprogress\">\
                   Job with ID %s is in progress.\
                   </Jobstatus>"
                  job_id);
           )

         ) 

       else
         
         (match job_exitcode with
      
             Unix.WSIGNALED code -> 
             
             (* JOB TERMINATED *)
             
             (* inform client *)
             let errors = read_bytes stderr_fn in
             ignore
               (zmsg_pushstr 
                  status 
                  (Format.sprintf 
                     "<Jobstatus msg=\"aborted\">\
                      Job with ID %s aborted before completion.\
                      Contents of stderr:@\n\
                      %s
                 </Jobstatus>"
                     job_id
                     errors));
             
             (* remove job from table of working jobs *)
             Hashtbl.remove running_jobs job_id
             
           | Unix.WSTOPPED code -> 
             
             (* JOB TERMINATED *)
             
             (* inform client *)
             let errors = read_bytes stderr_fn in
             ignore
               (zmsg_pushstr 
                  status 
                  (Format.sprintf 
                     "<Jobstatus msg=\"aborted\">\
                      Job with ID %s aborted before completion.\
                      Contents of stderr:@\n\
                      %s
                      </Jobstatus>"
                     job_id
                     errors));
             
             (* remove job from table of working jobs *)
             Hashtbl.remove running_jobs job_id
             

           | Unix.WEXITED code ->
             
             (* JOB COMPLETED *)
             
             (* get results *)
             let output_string = (read_bytes stdout_fn) in
             
             (* compute checksum of results *)
             let output_string' = Digest.string output_string in
             
             (* push output and checksum to zmsg *)
             let bytes_frame = 
               zframe_new output_string (String.length output_string) 
             in

             let checksum_frame = 
               zframe_new output_string' (String.length output_string') 
             in

             ignore(zmsg_push status checksum_frame);
             ignore(zmsg_push status bytes_frame);

             (* remove job from table of working jobs, add to table of completed jobs *)
             Hashtbl.remove running_jobs job_id;
             Hashtbl.add completed_jobs job_id (Unix.gmtime (Unix.time ()));

             print_endline ("retrieved job " ^ job_id)

         );

       (* clean up *)
       (* delete temp files for process *)
       (try (Sys.remove stdin_fn) with _ -> ());
       (try (Sys.remove stdout_fn) with _ -> ());
       (try (Sys.remove stderr_fn) with _ -> ());
       
     ) 

   with Not_found -> 
   
     (try 

        (
          (* didn't find job in table of working jobs. has it already been retrieved? *)
          let job_tm = Hashtbl.find completed_jobs job_id in
          ignore
            (let sstr = 
              Format.sprintf 
                "<Jobstatus msg=\"completed\">\
                 Job with ID %s has completed and was retrieved at %s\
                 </Jobstatus>"
                job_id
                (string_of_tm job_tm)
             in

             zmsg_pushstr status (sstr))

        ) 

      with Not_found ->
      
        print_endline ("failed to retrieve job " ^ job_id);
        ignore
          (zmsg_pushstr 
             status 
             (Format.sprintf
                "<Jobstatus msg=\"notfound\">\
                 Job with ID %s not found.\
                 </Jobstatus>"
                job_id));
     ); 
  );

  (* finally, send message to client *)
  ignore(zmsg_send status sock)
    

let purge_jobs () =
  print_endline "purging any old jobs";
  let purge_if_old job_id details = 
    let pid, timestamp, stdin_fn, stdout_fn, stderr_fn = details in
    if ( ((int_of_float (Unix.time ())) - timestamp) > job_lifespan ) then 

      (
        (* job is old *)
        print_endline ("purging old job " ^ job_id);
        (* remove job from table of working jobs *)
        Hashtbl.remove running_jobs job_id;
        (* delete job's temp files *)
        (try (Sys.remove stdin_fn) with _ -> ());
        (try (Sys.remove stdout_fn) with _ -> ());
        (try (Sys.remove stderr_fn) with _ -> ());
      );

  in

  Hashtbl.iter purge_if_old running_jobs


let collect_args msg =
  (* collect remaining string from msg into a string array *)
  let rec iter argument argv =
    match argument with
        "" -> argv;
      | _  -> iter (zmsg_popstr msg) (Array.append [|argument|] argv);
  in
  iter (zmsg_popstr msg) [||]
  

let get_requests sock =
  
  let last_purge = ref (int_of_float (Unix.time ())) in
  
  (try 

     (
       
       while true do (* should disconnect socket on interrupt *)
         let msg = zmsg_recv sock in
         let server_flags = zmsg_popstr msg in
         let payload = zmsg_pop msg in
         if (String.contains server_flags 'r') then 

           (try 

              (

                retrieve_job sock server_flags (zframe_strdup payload)
              ) 

            with e -> ()

           ) 
         
         else if (String.contains server_flags 'c') then 

           (

             (let checksum  = zmsg_popstr msg in
              let kind_args = collect_args(msg) in (* collect array of 
                                                      arguments to kind *)
              try 
                (
                  create_job sock server_flags payload checksum kind_args;
                ) 
              with Checksum_failure -> 
                let error_msg = zmsg_new () in
                ignore(zmsg_pushstr error_msg "checksum match failure.");
                ignore(zmsg_send error_msg sock);
             );
           ) 
         else 
           (
             (* ignoring bad message *)
             ();
           );

         (* purge old jobs once a day (864000 seconds) or so *)
         if (((int_of_float (Unix.time ())) - !last_purge) > 864000) then 
           (
             last_purge := (int_of_float (Unix.time ()));
             purge_jobs ();
           ); 

       done; 

     ) 
   with _ ->
     print_endline "server interrupted. cleaning up";
     (* clean up temp files *)
     let files = Sys.readdir "." in
     Array.iter (Sys.remove) files;
     Sys.chdir "..";
     Unix.rmdir tmpdir;
     exit 0
  )

;;

(* The "double fork" trick, starts server as daemon *)
(match Unix.fork() with
   0 -> if Unix.fork() <> 0 then exit 0; (* The son exits, the grandson works *)

    (* ENTRY POINT of daemon process *)

    (* set up the socket *)
    let ctx = zctx_new () in
    let rep_sock = (zsocket_new ctx ZMQ_REP) in
    let rc = zsocket_bind rep_sock ("tcp://*:" ^ (string_of_int port)) in
    if rc < 0 then ( 
      print_endline ("could not bind to port " ^ (string_of_int port) ^ ", aborting"); 
      exit 1;
    ) else (
      (* initialize temporary directory *)
      (try (
        Unix.mkdir tmpdir 0o700; 
        Sys.chdir tmpdir; 
      ) with _ ->
        print_endline ("could not create temporary directory " ^ tmpdir ^ ", aborting");
        exit 1;
      );

      (* redirect stdin/out/err *)
      let fd = Unix.openfile "/dev/null" [Unix.O_RDONLY] 0 in
      Unix.dup2 fd Unix.stdin;
      Unix.close fd;
      let fd = Unix.openfile "/dev/null" [Unix.O_WRONLY] 0 in
      Unix.dup2 fd Unix.stdout;
      Unix.close fd;
      let fd = Unix.openfile "/dev/null" [Unix.O_WRONLY] 0 in
      Unix.dup2 fd Unix.stderr;
      Unix.close fd;
      
      (* enter main loop *)
      get_requests rep_sock;
    );

    exit 0;
| id -> ignore(Unix.waitpid [] id); (* Reclaim the son *)
)


