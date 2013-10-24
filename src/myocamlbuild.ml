open Ocamlbuild_plugin;;
open Command;;
open Ocamlbuild_pack;;

(*
(* Configuration section *)
let glib_lib = "@GLIB_CONF_LIBS@"
let glib_include = "@GLIB_CONF_CFLAGS@";; 
*)

let ocamlfind_query pkg =
  let cmd = Printf.sprintf "ocamlfind query %s" (Filename.quote pkg) in
  My_unix.run_and_open cmd (fun ic ->
    Log.dprintf 5 "Getting Ocaml directory from command %s" cmd;
    input_line ic);;

dispatch begin function

  | After_rules ->
    ocaml_lib ~extern:true ~dir:"../../ocamlczmq/lib" "ZMQ";
         
(*

| After_rules -> 
    flag ["link"; "ocaml"; "use_stub"] (S[A"util_glib_stubs.o"]);
    (* Link flag for GLIB *)
    flag ["link"; "ocaml"; "use_glib"] (S[A"-cclib"; A glib_lib]);

    (* Compile flag for GLIB *)
    flag ["c"; "compile"; "include_glib"] (S[A"-cc"; A "cc"; A"-ccopt"; A glib_include; A"-ccopt"; A"-DNATIVE"]);

*)
 
| _ -> ()
end
