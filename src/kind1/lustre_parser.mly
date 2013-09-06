%{
(*
This file is part of the Kind verifier

* Copyright (c) 2007-2012 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)


  open Types
  open Exceptions
  open Lus_convert

  exception ForwardReference of string
  exception ParseMismatch


  let toss x = () (* toss outputs *)

  (* from (node,var) to varid *)
  let symidhash = (Hashtbl.create 100 : ((Types.node_id_t*string),int)Hashtbl.t)
  (* from varid to type *)
  let idtypehash = (Hashtbl.create 100 : (int,lustre_type)Hashtbl.t)
  (* from varid to varclass *)
  let idclasshash = (Hashtbl.create 100 : (int,varclass)Hashtbl.t)
  (* from id to the S_DEF *)
  let additional_constraints = (Hashtbl.create 1: (int,typed_stream)Hashtbl.t)
  (* from node name to id *)
  let nodeidhash = (Hashtbl.create 100: (string,int)Hashtbl.t)
  (* from sym to const *)
  let symconsthash = (Hashtbl.create 10: (string, Types.streamterm * Types.lustre_type)Hashtbl.t)
  (* from type name to type *)
  let typenamehash = (Hashtbl.create 100 : (string,lustre_type)Hashtbl.t)


  let idcounter = Lus_convert.idcounter

  (* set whenever we enter a new node definition *)
  let current_node = ref ""
  let current_node_id = ref 0
  let main_node = ref (None:int option)

  (* set whenever we enter a new classification scope *)
  let current_class = ref LOCAL
 
  (* List of properties *)
  let property_list = ref (S_TRUE,L_BOOL)
  let multi_property_list = ref []
  let nodes_property_list =   
    (Hashtbl.create 10: (node_id_t, typed_stream) Hashtbl.t) 
      
  (*List of assertions *)
  let assert_list = ref (S_TRUE,L_BOOL)
  let nodes_assert_list = 
    (Hashtbl.create 10: (node_id_t, typed_stream) Hashtbl.t) 
   
      
  let generate_eq (id, x_type) =
      (S_EQ ( ( (S_VAR ("ABC",id)), x_type), ((S_VAR("ABS",id)), x_type)) ) , L_BOOL
 


(*By Teme *)

(* This should return a list of default properties.*)
 let generate_default_property node_it = 
    let vars = 
      (Tables.get_node_inputs node_it) @ (Tables.get_node_outputs node_it)
    in
      List.fold_right
	(fun x y ->  ((S_AND ((generate_eq x), y)),L_BOOL ))
	vars
	(S_TRUE,L_BOOL)

    
  let cvcl_property = ref F_TRUE

  let safe_find = Tables.safe_find

  let var_def_gen () =
    Hashtbl.iter (fun (nid,var) id ->
		    let t = safe_find idtypehash id "var_def_gen" in
		    let c = safe_find idclasshash id "var_def_gen" in
		      Tables.update_varinfo id (nid,var,t,c)
		 ) symidhash ;;
  
  (* adding constants *)
  let add_const =
    Hashtbl.replace symconsthash

  let resolve_type x =
    try
      safe_find typenamehash x ("resolve_type:"^x) 
    with _ -> 
      let org_name = Tables.internal_name_to_original_name x in
      let line = !Lus_convert.linenum in
      let err_msg = "Type: '" ^ org_name ^ "' is not defined in line " ^ (string_of_int line) ^ "." in
    failwith err_msg
  let add_type x y =
    Hashtbl.replace typenamehash x y;;

  (* setting up some predefined type names *)

  add_type "int" L_INT;;
  add_type "real" L_REAL;;
  add_type "bool" L_BOOL;;  

  (* set up a true var for assertions *) 
  (* true is 1 *)
  (* false is 0 *)
  idcounter#set 100;; (* the first 100 "vars" are reserved for index vars *)

  let append_additional_constraints =
    Hashtbl.fold (fun i x y -> x::y) additional_constraints

  (* returns the triple node call name, line#, position#*)
  let node_pos target =
    (target,(!Lus_convert.linenum),
      Parsing.symbol_start()-(!Lus_convert.linepos))

%}
%token TYPE
%token SEMICOLON
%token EQUALS
%token LSQBRACKET
%token RSQBRACKET
%token FUNCTION
%token RETURNS
%token LPAREN
%token RPAREN
%token COLON
%token COMMA
%token INT
%token REAL
%token BOOL
%token NODE
%token LET
%token TEL
%token MINUS
%token UMINUS
%token PLUS
%token MULT 
%token DIV
%token INTDIV
%token MOD
%token TRUE
%token FALSE
%token NOT
%token AND
%token OR
%token XOR
%token IMPL
%token LT
%token GT
%token LTE
%token GTE
%token NEQ
%token IF
%token THEN
%token ELSE
%token WHEN
%token CURRENT
%token PRE
%token FBY
%token CONDACT
%token ARROW
%token PROPERTY
%token SUBRANGE
%token OF
%token ASSERT
%token <string>METAPROPERTY
%token MAIN_NODE
%token VAR
%token CONST
%token DOT
%token TO_TOK
%token <string> CONVERT_TO
%token <string> CONVERT_FROM
%token <string> NUM
%token <string> FLOAT
%token <string> SYM
%token EOF_TOK

%right ARROW
%left IMPL
%left OR XOR
%left AND
%left NOT
%nonassoc EQUALS LT GT LTE GTE NEQ
%left MINUS PLUS
%left MULT DIV INTDIV MOD
%left UMINUS
%left PRE FBY

%start main
%type <Types.il_formula * Types.typed_stream * Types.typed_stream list * Types.node_id_t> main
%%

main:
  lustre_main EOF_TOK
  { 
    let top_node = 
      if  "" = !OldFlags.user_specified_main_node_name 
      then 
	match !main_node with
	    Some n -> n
	  | None -> !current_node_id
      else 
	let main_node_name = !OldFlags.user_specified_main_node_name in 
	  try Hashtbl.find nodeidhash 
	    (Tables.LongStringHash.find Tables.sym_truenaming_table main_node_name) 
	  with Not_found -> 
	    let default_node_id =
 	      match !main_node with
		  Some n -> n
		| None -> !current_node_id
	    in
	    let default_node_name = 
	      (Tables.nodeid_to_original_name default_node_id) ^":"^
	      (Tables.get_nodename default_node_id) in 
	    let warning_msg = (
	      "Warning: Cannot the specified node: " ^ 
		main_node_name ^ ". \nUse default node " ^ default_node_name
	      ^ "\n" )
	    in
	      print_string warning_msg;
	      default_node_id
    in


    let default_property_list = 
	try Hashtbl.find nodes_property_list top_node 
	with Not_found -> 
	  failwith "NO PROPERTY SPECIFIED."
	  (* let node_name = (Tables.nodeid_to_original_name top_node  ) 
	    ^ " :" ^ (Tables.get_nodename top_node) 
	  in
	  let warning_msg = ("Warning: No property found in specified node: " ^ "\n"
				^ " KIND will assume :" ^ (node_name) ^ " as a default property.\n") in
	    print_string warning_msg;
	    generate_default_property top_node
	  *)
    in
      property_list := default_property_list;
      var_def_gen();
      (!cvcl_property, !property_list, !multi_property_list, top_node)
  }


lustre_main:
  type_blocks node_blocks
  {  }
| node_blocks
  {  }

node_blocks:
  node_decl
  { }
| node_decl type_blocks node_blocks
  { }
| node_decl node_blocks
  { }

type_blocks:
  type_block
  {}
| type_block type_blocks
  {}

type_block:
  TYPE type_decls SEMICOLON 
  { (* return nothing *) }
| const_block
  {}

type_decls:
  type_decl 
  { (* return nothing *)}
| type_decls SEMICOLON type_decl 
  { (* return nothing*) }

type_decl:
| sym_name EQUALS type_def
  { add_type $1 $3 }

const_block:
  CONST const_decls SEMICOLON
  {}

const_decls:
  const_decl
  {}
| const_decls SEMICOLON const_decl
  {}

const_decl:
  sym_name EQUALS integer
  { add_const $1 (S_INT($3),L_INT) }
| sym_name EQUALS real
  { 
    let i,n,d = $3 in
    add_const $1 (S_REAL(i,n,d),L_REAL)
  }

rec_fields:
| sym_name COLON type_def 
  { [($1,$3)] }
| sym_name COLON type_def COMMA rec_fields
  { ($1,$3) :: $5 }

tuple_fields:
| type_def
  { [$1] }
| type_def COMMA tuple_fields
  { $1 :: $3 }

type_def:
| REAL
  { L_REAL }
| BOOL
  { L_BOOL }
| INT
  { L_INT }
| SUBRANGE LSQBRACKET integer COMMA integer RSQBRACKET OF INT
  {
    Globals.is_inter := true;
    L_INT_RANGE($3,$5)
    ;
(*   L_INT*)
  }
| sym_name
  {

    resolve_type $1

  }
| LSQBRACKET rec_fields RSQBRACKET 
  {
    let rt = List.sort (compare) $2 in
    L_RECORD rt
  }
| LSQBRACKET tuple_fields RSQBRACKET
  {
    L_TUPLE $2
  }

var_block:
  VAR varlist SEMICOLON
  {
    Tables.add_node_locals !current_node_id $2;
  }

varlist:
| param 
  {
    $1
  }
| varlist SEMICOLON param
  { $1 @ $3 }

param_list:
| LPAREN RPAREN
  { [] }
| LPAREN params RPAREN
  { 
    $2 
  }

params:
| param
  { 
    $1 
  }
| param SEMICOLON params
  { 
    $1 @ $3
  }

param:
  sym_name COLON type_def
  { let next_id = idcounter#next in
    Hashtbl.replace symidhash (!current_node_id,$1) next_id;
    Hashtbl.replace idtypehash next_id $3;
    (* current_class set previously in parse *)
    Hashtbl.replace idclasshash next_id !current_class;
    [(next_id,$3)]
  }
| sym_list COLON type_def
  {
    List.map (fun x ->
      let next_id = idcounter#next in
      Hashtbl.replace symidhash (!current_node_id,x) next_id;
      Hashtbl.replace idtypehash next_id $3;
      (* current_class set previously in parse *)
      Hashtbl.replace idclasshash next_id !current_class;
      (next_id,$3)
    ) (List.rev $1)
  }

sym_list:
  sym_name
  { [$1] }
| sym_list COMMA sym_name
  { $3::$1 }

node_decl:
  node_header var_block let_block
  { 
    Tables.add_node_defs $1 $3
  }
| node_header let_block
  { 
    Tables.add_node_defs $1 $2
  }

semicolon_or_not:
  SEMICOLON { [] }
  | { [] }


node_header: 
   NODE node_name param_list node_out param_list semicolon_or_not
  {
    current_class := LOCAL;
    Tables.add_node_inputs $2 $3;
    Tables.add_node_outputs $2 $5;
    $2
  }

node_out:
  RETURNS
  { 
    current_class := OUTPUT;
  }

node_name:
  sym_name
  {
   (* set the current_node to this node's name *)
   current_node := $1;
   let next_id = idcounter#next in
   Hashtbl.replace nodeidhash $1 next_id;
   Tables.add_nodename next_id $1;
   current_node_id := next_id;
   current_class := INPUT;
   next_id
  }

tel_and_punctuation:
  TEL { [] }
| TEL SEMICOLON { [] }
| TEL DOT { [] }


let_block:
/*
  LET flow_decls TEL SEMICOLON
  { 
    let out = append_additional_constraints $2 in
    Hashtbl.clear additional_constraints;
    out
  }
| LET flow_decls TEL
  { 
*/
| LET flow_decls tel_and_punctuation
  { 
    let out = append_additional_constraints $2 in
    Hashtbl.clear additional_constraints;
    out
  }
| LET TEL tel_and_punctuation
  {
    []
  }

property:
| PROPERTY expr SEMICOLON
  { 
 (*   let stored_property = 
      try Hashtbl.find nodes_property_list !current_node_id 
      with Not_found -> (S_TRUE,L_BOOL) in
    let new_property = (S_AND ($2,stored_property),L_BOOL) in
      Hashtbl.replace nodes_property_list !current_node_id new_property;
      () 
 *) 
(* Teme *)
  
  let stored_property = 
      try Hashtbl.find nodes_property_list !current_node_id;
      with Not_found -> (S_TRUE,L_BOOL)  in
    Globals.prop_typed_stream := $2;
    let new_property =  (S_AND ($2,stored_property),L_BOOL)  in
      Hashtbl.replace nodes_property_list !current_node_id new_property;
     multi_property_list := ($2 :: !multi_property_list); 
    ()
   
    
}
| METAPROPERTY SEMICOLON
  {
    let regex = Str.regexp "_x" in
    let index = 
      try Str.search_forward regex $1 0
      with Not_found -> -1
    in
    if index >= 0 then OldFlags.set_use_x();
    cvcl_property := Lus_convert.f_and !cvcl_property (F_STR $1);
    ()
  }
| MAIN_NODE
  {
    main_node := Some !current_node_id
  }

flow_decls:
| flow_decl flow_decls
  { 
    List.rev_append $1 $2
  }
| flow_decl
  { 
    $1
  }
| property flow_decls
  { 
    $2
  }
| property
  { 
    [] 
  }

flow_decl:
  sym_name EQUALS expr SEMICOLON
  {
   (* here we try to simplify the condact expressions *)
   (* returns S_DEF(-1,_,_) to indicate an ignorable equation *)
   try
    let id = Hashtbl.find symidhash (!current_node_id,$1) in
    let lhs = S_VAR((!current_node)^"_$1$_"^($1),id),safe_find idtypehash id "flow_decl1" in
    let nid = !current_node_id in
    (* try to compress condact variables *)
    match $3 with
        S_VAR(sym,id),_ -> 
           begin
             try 
               let nid,x,y,z,t =
                  match Hashtbl.find additional_constraints id with
                    (S_DEF(nid,_,(S_CONDACT(x,y,z,_),t)),L_BOOL) -> nid,x,y,z,t
                   | _ -> raise ParseMismatch
               in
               Hashtbl.remove additional_constraints id;
               Hashtbl.remove symidhash (!current_node_id,sym);
               let cond = S_CONDACT(x,y,z,lhs),t in
               [S_DEF(nid,lhs,cond),L_BOOL]
             with Not_found ->
               [S_DEF(nid,lhs,$3),L_BOOL] 
           end
      | _ -> 
             [S_DEF(nid,lhs,$3),L_BOOL]
   with Not_found ->
     []
  }
| symlist EQUALS expr SEMICOLON
  {
   try 
     let vlist = List.map (fun e ->
         let id = Hashtbl.find symidhash (!current_node_id,e) in
         S_VAR((!current_node)^"_$2$_"^e,id),safe_find idtypehash id "flow_decl2"
       ) $1 
     in
     let tlist = List.map (fun (_,t1) -> t1) vlist in
     let nid = !current_node_id in
     let lhs = S_TUPLELIT(vlist), L_TUPLE(tlist) in
     match $3 with
         S_VAR(sym,id),_ -> 
           begin
             try 
               let nid,x,y,z,t =
                  match Hashtbl.find additional_constraints id with
                    (S_DEF(nid,_,(S_CONDACT(x,y,z,_),t)),L_BOOL) -> nid,x,y,z,t
                   | _ -> raise ParseMismatch
               in
               Hashtbl.remove additional_constraints id;
               Hashtbl.remove symidhash (!current_node_id,sym);
               let cond = S_CONDACT(x,y,z,lhs),t in
               [S_DEF(nid,lhs,cond),L_BOOL]
             with Not_found ->
               [S_DEF(nid,lhs,$3),L_BOOL] 
           end
       | _ -> [S_DEF(nid,lhs,$3),L_BOOL]
   with Not_found -> []
  }
| ASSERT expr SEMICOLON
  {
   (* here we assert that the expr is TRUE *)
    
     let nid = !current_node_id in
      [S_ASSERT(nid,$2),L_BOOL] 
   

    (*let assertion = 
      try Hashtbl.find nodes_assert_list !current_node_id 
      with Not_found -> (S_TRUE,L_BOOL) in
    let new_assertion = (S_AND ($2,assertion),L_BOOL) in
      Hashtbl.replace nodes_assert_list !current_node_id new_assertion
    *)
  }

expr:
  sym_name
  {
    try
      (* replace var with const expression *)
      Hashtbl.find symconsthash $1
    with Not_found ->
begin 
    try
      let id = Hashtbl.find symidhash (!current_node_id,$1) in
        let t = match Hashtbl.find idtypehash id with
           L_INT_RANGE(_,_) -> L_INT
        | x -> x
      in
      S_VAR((!current_node)^"_$3$_"^($1),id),t
    with Not_found ->
      Printf.printf "symbol %s not found in node %s\n" (Tables.resolve_var_name $1) (Tables.resolve_var_name !current_node);
      raise Not_found
end
  }
| integer
  { 
    S_INT($1),L_INT 
  }
| real
  { 
    let i,n,d = $1 in
    S_REAL(i,n,d),L_REAL 
  }
| sym_name LPAREN RPAREN
  {
    (* node or function call *)
    let nid = safe_find nodeidhash $1 ("expr:node "^$1) in
    let rtl = try
      List.map (fun (_,y) -> y) 
         (Tables.get_node_outputs nid)
      with Not_found ->
        raise (ForwardReference $1)
    in
    let rettype = match rtl with
          [x] -> x
        | x -> L_TUPLE(x)
    in
    toss(Lus_types.match_types_list [] (Tables.get_node_inputs nid));
    let (a,b,c) = node_pos nid in
    S_NODE(a,b,c,[]),rettype
  }
| sym_name LPAREN exprlist RPAREN
  {
    (* node or function call *)
    let nid = safe_find nodeidhash $1 ("expr:node "^$1) in
    let elist = List.rev $3 in
    let rtl = try
      List.map (fun (_,y) -> y) 
         (Tables.get_node_outputs nid)
      with Not_found ->
        raise (ForwardReference $1)
    in
    let rettype = match rtl with
          [x] -> x
        | x -> L_TUPLE(x)
    in
    toss(Lus_types.match_types_list elist (Tables.get_node_inputs nid));
    let (a,b,c) = node_pos nid in
    S_NODE(a,b,c,elist),rettype
  }
| expr MULT expr
  { 
    S_MULT($1,$3), Lus_types.match_types $1 $3
  }
| expr DIV expr
  { 
(*    S_DIV($1,$3), Lus_types.match_types $1 $3 Yeting. The type should be real*)
    S_DIV($1,$3), (Lus_types.match_types $1 $3; L_REAL) 
  }
| MINUS expr %prec UMINUS
  { 
    S_UMINUS($2), Lus_types.match_type_is_numeric $2
  }
| expr PLUS expr
  { 
    S_PLUS($1,$3), Lus_types.match_types $1 $3
  }
| expr MINUS expr
  { 
    S_MINUS($1,$3), Lus_types.match_types $1 $3 
  }
| expr INTDIV expr
  { 
    S_INTDIV($1,$3),Lus_types.match_types_int $1 $3
  }
| expr MOD expr
  { 
    S_MOD($1,$3),Lus_types.match_types_int $1 $3
  }
| TRUE
  { S_TRUE,L_BOOL }
| FALSE
  { S_FALSE,L_BOOL }
| NOT expr
  {
      S_NOT($2), Lus_types.match_types_bool $2 (S_TRUE,L_BOOL)
  }
| expr AND expr
  {
      S_AND($1,$3),Lus_types.match_types_bool $1 $3
  }
| expr OR expr
  { 
      S_OR($1,$3),Lus_types.match_types_bool $1 $3
  }
| expr XOR expr
  { 
      S_XOR($1,$3),Lus_types.match_types_bool $1 $3
  }
| expr IMPL expr
  {
      S_IMPL($1,$3),Lus_types.match_types_bool $1 $3
  }
| expr EQUALS expr
  { 
    toss(Lus_types.match_types $1 $3);
    S_EQ($1,$3),L_BOOL
  }
| expr LT expr
  { 
    S_LT($1,$3),Lus_types.match_types_nrel $1 $3
  }
| expr GT expr
  { 
    S_GT($1,$3),Lus_types.match_types_nrel $1 $3
  }
| expr LTE expr
  { 
    S_LTE($1,$3),Lus_types.match_types_nrel $1 $3
  }
| expr GTE expr
  { 
    S_GTE($1,$3),Lus_types.match_types_nrel $1 $3
  }
| expr NEQ expr
  {
    S_NOT (S_EQ($1,$3),Lus_types.match_types_nrel $1 $3), L_BOOL
  }
| INT expr
  { 
    S_COERCE_TO_INT ($2),L_INT 
  }
| REAL expr
  { 
    S_COERCE_TO_REAL ($2),L_REAL 
  }
| BOOL expr
  {
    S_ITE((S_EQ($2,(S_INT(0),L_INT)),L_BOOL),(S_FALSE,L_BOOL),(S_TRUE,L_BOOL)),L_BOOL
  }
| IF expr THEN expr ELSE expr
  { 
      S_ITE($2,$4,$6), Lus_types.match_types_ite $2 $4 $6
  }
| PRE expr 
  { 
    S_PRE($2), Lus_types.gettype $2
  }
| FBY LPAREN expr COMMA integer COMMA expr RPAREN
  {
    S_FBY($3,$5,$7), Lus_types.gettype $3
  }
| expr ARROW expr
  { 
    S_FOLLOWEDBY($1,$3), Lus_types.match_types $1 $3
  }
| expr WHEN expr
  {
    S_WHEN($1,$3), Lus_types.match_types_ite $3 $1 $1
  }
| CURRENT expr
  {
    S_CURRENT($2), Lus_types.gettype $2
  }
| CONDACT LPAREN expr COMMA expr COMMA expr RPAREN
  {
    (* this is actually a SCADE macro *)
    (* clock,expr,defaults *)
    (* we generate a fresh variable for this, and may then compress it later
       in the parsing *)
    let next_id = idcounter#next in
    let name = "_tmp_"^(string_of_int next_id) in
    let t = Lus_types.gettype $5 in
    Hashtbl.replace symidhash (!current_node_id,name) next_id;
    Hashtbl.replace idtypehash next_id t;
    Hashtbl.replace idclasshash next_id LOCAL;
    let e = S_VAR((*(!current_node)^"_"^*)name,next_id),t in
    let cond = S_CONDACT($3,$5,$7,e),t in
    let nid = !current_node_id in
    Hashtbl.replace additional_constraints next_id 
        (S_DEF(nid,e,cond),L_BOOL);
    e
  }
| expr LSQBRACKET integer RSQBRACKET
  {
    (* tuple deref placeholder *)
    S_TUPLEREF($1,$3),(Lus_types.is_tuple_type $1 $3)
  }
| LSQBRACKET record_literal_fields RSQBRACKET
  {
    let r = List.sort (compare) $2 in
    let t1 = List.map (fun (f,(_,t)) -> (f,t)) r in
    let t2 = List.sort (compare) t1 in
    S_RECORDLIT(r),L_RECORD(t2)
  }
| expr DOT sym_name 
  {
    (* record deref placeholder *)
    let t1 = match $1 with
      (_,L_RECORD t1) -> t1
      | _ -> raise ParseMismatch
    in
    let rec getftype fl = 
      match fl with
        (fn,ft)::x -> if fn = $3 then ft else getftype x
       | [] -> raise (IdNotFound "getftype")
    in
    let t = getftype t1 in
    S_RECORDREF($1,$3), t
  }
| CONVERT_TO LPAREN expr RPAREN
  { 
    (* placeholder *)
    $3 
  }
| CONVERT_FROM LPAREN expr RPAREN
  { 
    (* placeholder *)
    $3 
  }
| LSQBRACKET exprlist RSQBRACKET
  { 
    let elist = List.rev $2 in
    let tlist = List.map (fun (_,x) -> x) elist in
    S_TUPLELIT(elist),L_TUPLE(tlist)
  }
| LPAREN exprlist RPAREN
  { 
    let elist = List.rev $2 in
    let tlist = List.map (fun (_,x) -> x) elist in
    S_TUPLELIT(elist),L_TUPLE(tlist)
  }
| LPAREN expr RPAREN
  { $2 }

exprlist:
  exprlist COMMA expr
  { 
    (* returns a revered list! *)
    $3::$1 
  }
| expr
  { [$1] }

symlist:
  syms
  { $1 }
| LPAREN syms RPAREN
  { $2 }

syms:
  sym_name COMMA syms
  { $1::$3 }
| sym_name COMMA sym_name
  { [$1;$3] }


integer:
  NUM { 
    if (String.length $1) > Globals.max_num_digits
    then 
      failwith ("Number " ^ $1 ^ " out of range.")
    else 
      int_of_string $1 
  }

real:
  FLOAT 
  { 
    if (String.contains $1 'E')  
    then (
      let rec n_0 n =
	if n = 1 then "0"
	else ("0" ^ (n_0 (n-1))) 
      in
      let last_ch str = 
	let len = String.length str in
	  if len > 0 
	  then String.get str (len - 1 ) 
	  else failwith "last_ch" 
      in 
      let rec cut_0 str =
	if String.length str <= 1 
	then str (*keep the last 0 *) 
	else if '0' = last_ch str 
	then cut_0 (String.sub str 0 ((String.length str) - 1))
	else str 
      in (*
      print_string $1 ; 
      print_string "\n";*)
      let e_pos = String.index $1 'E' in
      let dot_pos = String.index $1 '.' in
	assert (dot_pos = 1);
	assert (e_pos + 4 = String.length $1);
      let e_sign =  String.get  $1 (e_pos+1) in
	assert ('-' = e_sign || '+' = e_sign );
      let e_str = String.sub $1 (e_pos+2) 2 in 
      let shift_value =  
	let v = (int_of_string e_str) in
	  if '-' = e_sign then -v
	  else v 
      in
      let v1_str = String.sub $1 0 1 in
      let v2_str = String.sub $1 (dot_pos + 1 ) (e_pos - dot_pos - 1) in
      let v_str = v1_str ^ v2_str in
      let cut_pos, value = 
	if (shift_value < 0) then 1, (cut_0 ((n_0 (abs shift_value)) ^ v_str ))
	else if (shift_value + 2) > String.length v_str
	then (shift_value + 1), (v_str ^ (n_0 (shift_value + 1 + 1 - (String.length v_str)))) 
	else (shift_value + 1), v_str 
      in
      let n = int_of_string (String.sub value 0 cut_pos) in
      let p_len = (String.length value) - cut_pos in
      let d_str = cut_0 (String.sub value cut_pos p_len) in
      let d = int_of_string d_str in
      let p = int_of_string ("1" ^ (n_0 (String.length d_str))) in
	(n,d,p)
    )
    else 
      let pos = String.index $1 '.' in
      if pos > Globals.max_num_digits then
	failwith  ("Number " ^ $1 ^ "out of range.") ;
      let len = 
	let act_len = (String.length $1)-pos-1 in
	  if act_len <= Globals.max_num_digits 
	  then act_len
	  else 
	    let warn_msg = "Warning: " ^ $1 ^ " too long, truncated into " ^
	      (String.sub $1 0 (pos + Globals.max_num_digits + 1)) in
	      print_string warn_msg;
	      print_newline();
	      Globals.max_num_digits 
      in
      let n = String.sub $1 0 (pos) in
      let d = String.sub $1 (pos+1) len in
	(* Yeting. 1.03 --> 1, 03, 100 --> 1 + (03/100) *)
	(int_of_string(n),int_of_string(d),int_of_float(10.0**float_of_int(len))) 
  }

sym_name:
  SYM { Tables.rename_sym $1 }

record_literal_fields:
  record_literal_field
  { [$1] }
| record_literal_fields COMMA record_literal_field
  { $3::$1 }


record_literal_field:
  sym_name COLON expr
  { ($1,$3) }
