open Ocamlbuild_plugin;;
open Command;;
open Ocamlbuild_pack;;

let rec pp_print_list pp sep ppf = function 

  (* Output nothing for the empty list *) 
  | [] -> ()

  (* Output a single element in the list  *) 
  | e :: [] -> 
    pp ppf e

  (* Output a single element and a space *) 
  | e :: tl -> 

    (* Output one element *)
    pp_print_list pp sep ppf [e]; 

    (* Output separator *)
    Format.fprintf ppf sep; 

    (* Output the rest of the list *)
    pp_print_list pp sep ppf tl
;;

dispatch begin function

  | After_rules ->
    
    (* Include ocamlczmq for tag use_ZMQ *)
    ocaml_lib ~extern:true ~dir:"../../ocamlczmq/lib" "ZMQ";

    (* Index page for documentation *)
    dep 
      ["ocaml"; "doc"]
      [ (* "kind2.docdir/includes"; *)
       "doc/doc_intro.txt";
       "doc/style.css"];

    flag
      ["ocaml"; "doc"] 
      (S [A"-intro"; A"doc/doc_intro.txt"; 
          A"-css-style"; A"doc/style.css";
          A"-colorize-code"]);

(*
    rule
      "ocamldoc: copy included files"
      ~deps:[ ]
      ~prods:[ "%.docdir/includes" ]
      ~stamp:"%.docdir/includes.stamp"
      ~insert:`top
      (fun env builder -> 
         Log.eprintf
           "Copying files from %s to %s"
           "doc/includes"
           (env "%.docdir/includes" |> Pathname.to_string);

         Seq
           [Nop]
      )
*)

  | _ -> ()

end
