(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

 *)

(** encapsulate identifier details.
    This represents a qualified name.

    eg. M::N::t is represented as PIdent (M, PIdent (N, (UIdent t))) 
  
  @author Apoorv Ingle *)

module Ident = struct 
  type t = UIdent of string | PIdent of t * string

  let rec equal: t -> t -> bool =  fun i1 i2 ->
    match (i1, i2) with
    | UIdent s1, UIdent s2 -> s1 = s2
    | PIdent (p1, s1), PIdent (p2, s2) ->
       if (s1 = s2)
       then equal p1 p2
       else false
    | _, _ -> false

  let rec compare: t -> t -> int = fun i1 i2 ->
    match i1, i2 with
    | UIdent s1, UIdent s2 -> Stdlib.compare s1 s2
    | PIdent (p1, s1), PIdent (p2, s2) ->
       if (Stdlib.compare s1 s2 = 0) then compare p1 p2
       else Stdlib.compare s1 s2
    | PIdent _, UIdent _ -> 1
    | UIdent _, PIdent _ -> -1
                          
                          
  let rec to_list: t -> string list =
    function
    | UIdent s -> [s]
    | PIdent (p, s) -> s :: (to_list p)

  let rec from_list: string list -> t =
    function
    | [] -> failwith "Cannot have empty list for identifer"
    | [s] -> UIdent s
    | a :: t -> PIdent ((from_list t), a) 

  let rec to_string: t -> string =
    function
    | UIdent s -> s
    | PIdent (p, s) -> s ^ "::" ^ to_string p


  let from_string: string -> t = fun s ->
    let ss = String.split_on_char ':' s |> List.filter (fun s -> s <> "") in
    from_list ss

  let rec add_prefix: string -> t -> t = fun prefix ->
    function
    | UIdent s -> UIdent (prefix ^ s)
    | PIdent (p, s) -> PIdent (add_prefix prefix p, s) 

  let rec add_suffix: string -> t -> t = fun suffix ->
    function
    | UIdent s -> UIdent (s ^ suffix)
    | PIdent (p, s) -> PIdent (add_suffix suffix p, s) 
                     
  let add_qualified_prefix: string -> t -> t = fun p i ->
    PIdent (i, p)  
      
  let rec pp_print_ident ppf =
    function
    | UIdent s ->
       Format.fprintf ppf "%a"
         Format.pp_print_string s
    | PIdent (p, s) ->
       Format.fprintf ppf "%a::%a"
         Format.pp_print_string s
         pp_print_ident p

end                               

include Ident

module IdentSet = struct
  include Set.Make (Ident)
  let flatten: t list -> t = fun sets ->
    List.fold_left union empty sets
end 

module IdentMap = struct
  include Map.Make (Ident)
  let keys: 'a t -> key list = fun m -> List.map fst (bindings m)
end
