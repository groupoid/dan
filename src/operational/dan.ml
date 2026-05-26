(* Groupoid Infinity Simplicity HoTT as Rezk/GAP replacement called Dan Kan

   $ ocamlopt -o dan dan.ml

   Copyright (c) 2025 Groupoid Infinity

   STATUS: early bird prototype (achieved 20 rewrites)
*)

open Dan_syntax

(* Helpers *)

let check_str s = 
  try int_of_string s |> ignore; true
  with Failure _ ->
    s = "x" ||
    (String.length s >= 2 && s.[0] = 'Z')

let rec check_term defn env t allowed_types =
  match t with
  | Id id -> 
        if (check_str id) then () else
        if not (Hashtbl.mem env id) then failwith ("Undeclared term: " ^ id)
  | Comp (t1, t2) -> check_term defn env t1 allowed_types; check_term defn env t2 allowed_types
  | Inv t -> check_term defn env t allowed_types
  | Pow (t, _) -> check_term defn env t allowed_types
  | PowInt (t, _) -> check_term defn env t allowed_types
  | Conj (t1, t2) | Comm (t1, t2) | Act (t1, t2) | Hom (t1, t2) | RelEq (t1, t2) ->
      check_term defn env t1 allowed_types; check_term defn env t2 allowed_types
  | E -> ()
  | Matrix m ->
      if not (List.mem defn.typ allowed_types) then failwith "Matrix only allowed in Group, Monoid, Ring, Category, Field, MatGroup"
      else List.iter (fun row -> List.iter (fun _ -> ()) row) m
  | Add (t1, t2) | Mul (t1, t2) ->
      if not (List.mem defn.typ [Ring; Field]) then failwith "Add/Mul only allowed in Ring, Field"
      else check_term defn env t1 allowed_types; check_term defn env t2 allowed_types
  | Div (t1, t2) ->
      if defn.typ <> Field then failwith "Div only allowed in Field"
      else check_term defn env t1 allowed_types; check_term defn env t2 allowed_types;
           if t2 = E then failwith "Division by zero"
  | Scalar _ -> ()
  | Perm p ->
      (* Validate permutation list *)
      let n = List.length p in
      let sorted = List.sort compare p in
      let rec check_consec i = function
        | [] -> ()
        | x :: xs -> if x <> i then failwith "Permutation indices must form a bijection" else check_consec (i + 1) xs
      in
      (* Permutations can be 0-indexed or 1-indexed; standard is 1..n *)
      if n > 0 then (
        let start = List.hd sorted in
        check_consec start sorted
      )
  | Cycle c ->
      (* Validate cycle decomposition *)
      List.iter (fun cyc ->
        if List.length cyc < 2 then failwith "Cycle must contain at least 2 elements"
      ) c
  | PermGroup gens ->
      List.iter (fun gen -> check_term defn env gen allowed_types) gens
  | MatGroup (gens, q, n) ->
      if q <= 1 || n <= 0 then failwith "Invalid MatGroup parameters";
      List.iter (fun gen -> check_term defn env gen allowed_types) gens
  | FpGroup (gens, rels) ->
      let local_env = Hashtbl.copy env in
      List.iter (fun gen -> Hashtbl.add local_env gen Simplex) gens;
      List.iter (fun rel -> check_term defn local_env rel allowed_types) rels
  | PcGroup (gens, rels) ->
      let local_env = Hashtbl.copy env in
      List.iter (fun gen -> Hashtbl.add local_env gen Simplex) gens;
      List.iter (fun rel -> check_term defn local_env rel allowed_types) rels
  | Face (_, t) | Deg (_, t) | Boundary t ->
      check_term defn env t allowed_types

let check_type_def defn =
  let env = Hashtbl.create 10 in

  (* Context check *)
  List.iter (fun h ->
    match h with
    | Decl (ids, typ) -> List.iter (fun id ->
        if Hashtbl.mem env id then (
          if Hashtbl.find env id <> typ then
            failwith ("Duplicate declaration with different type: " ^ id)
        ) else
          Hashtbl.add env id typ
      ) ids
    | Equality (id, t1, t2) ->
        (match t1 with
         | Id lhs_id -> if not (Hashtbl.mem env lhs_id) then Hashtbl.add env lhs_id Simplex
         | _ -> ());
        check_term defn env t1 [Group; Monoid; Ring; Category; Field; PermGroup; MatGroup; FpGroup; PcGroup];
        check_term defn env t2 [Group; Monoid; Ring; Category; Field; PermGroup; MatGroup; FpGroup; PcGroup];
        Hashtbl.add env id Simplex
    | Mapping (id, t1, t2) ->
        (match t1 with
         | Id lhs_id -> if not (Hashtbl.mem env lhs_id) then Hashtbl.add env lhs_id Simplex
         | _ -> ());
        check_term defn env t1 [Group; Monoid; Ring; Category; Field; PermGroup; MatGroup; FpGroup; PcGroup];
        check_term defn env t2 [Group; Monoid; Ring; Category; Field; PermGroup; MatGroup; FpGroup; PcGroup];
        Hashtbl.add env id Simplex
    | Presentation (id, t) ->
        check_term defn env t [Group; PermGroup; MatGroup; FpGroup; PcGroup];
        Hashtbl.add env id FpGroup
    | Relation t ->
        check_term defn env t [Group; PermGroup; MatGroup; FpGroup; PcGroup]
    | Action (id, t1, t2) ->
        check_term defn env t1 [Group; PermGroup; MatGroup; FpGroup; PcGroup];
        check_term defn env t2 [GSet; Set; Simplex];
        Hashtbl.add env id Simplex
    | Orbit (t1, t2, elements) ->
        List.iter (fun el ->
          match el with
          | Id id -> if not (Hashtbl.mem env id) then Hashtbl.add env id Simplex
          | _ -> ()
        ) elements;
        check_term defn env t1 [Group; PermGroup; MatGroup; FpGroup; PcGroup];
        check_term defn env t2 [GSet; Set; Simplex];
        List.iter (fun el -> check_term defn env el [GSet; Set; Simplex]) elements
    | Stabilizer (t1, t2, t3) ->
        (match t3 with
         | Id id -> if not (Hashtbl.mem env id) then Hashtbl.add env id Group
         | _ -> ());
        check_term defn env t1 [Group; PermGroup; MatGroup; FpGroup; PcGroup];
        check_term defn env t2 [GSet; Set; Simplex];
        check_term defn env t3 [Group; PermGroup; MatGroup; FpGroup; PcGroup]
  ) defn.context;

  (* Check specs *)
  List.iter (fun spec ->
    (* Check elements *)
    List.iter (fun el ->
      if not (Hashtbl.mem env el) then
        failwith (Printf.sprintf "Undeclared element: %s in spec of %s" el defn.name)
    ) spec.spec_elements;

    (* Check faces *)
    List.iter (fun f ->
      if not (Hashtbl.mem env f) then
        failwith (Printf.sprintf "Undeclared face: %s in spec of %s" f defn.name)
    ) spec.spec_faces;

    (* Check constraints *)
    List.iter (fun c ->
      match c with
      | Eq (t1, t2) ->
          check_term defn env t1 [Group; Monoid; Ring; Category; Field; PermGroup; MatGroup; FpGroup; PcGroup];
          check_term defn env t2 [Group; Monoid; Ring; Category; Field; PermGroup; MatGroup; FpGroup; PcGroup]
      | Neq (t1, t2) ->
          check_term defn env t1 [Group; Monoid; Ring; Category; Field; PermGroup; MatGroup; FpGroup; PcGroup];
          check_term defn env t2 [Group; Monoid; Ring; Category; Field; PermGroup; MatGroup; FpGroup; PcGroup]
      | In (t1, t2) ->
          check_term defn env t1 [Group; PermGroup; MatGroup; FpGroup; PcGroup];
          check_term defn env t2 [Group; PermGroup; MatGroup; FpGroup; PcGroup]
      | Order (t, _) ->
          check_term defn env t [Group; PermGroup; MatGroup; FpGroup; PcGroup]
      | Rel terms ->
          List.iter (fun t -> check_term defn env t [Group; PermGroup; MatGroup; FpGroup; PcGroup]) terms
      | Map (id1, ids2) ->
          if not (Hashtbl.mem env id1) then failwith ("Undeclared map source: " ^ id1);
          List.iter (fun id2 -> if not (Hashtbl.mem env id2) then failwith ("Undeclared map target: " ^ id2)) ids2
    ) spec.spec_constraints;

    (* Rank checking *)
    match defn.typ, spec.spec_rank with
    | Ring, Finite n -> if n < 0 then failwith "Ring rank must be non-negative"
    | Ring, Infinite -> failwith "Ring rank cannot be infinite"
    | Field, Finite n -> if n < 0 then failwith "Field rank must be non-negative"
    | Field, Infinite -> failwith "Field rank cannot be infinite"
    | Group, Finite n | Monoid, Finite n ->
        if List.length spec.spec_elements <> n then
          failwith "Group/Monoid rank mismatch (n = generator count)"
    | Group, Infinite | Monoid, Infinite -> failwith "Group/Monoid cannot have infinite rank"
    | PermGroup, Finite n | MatGroup, Finite n | FpGroup, Finite n | PcGroup, Finite n ->
        if n < 0 then failwith "Rank must be non-negative"
    | Module, Finite n | Set, Finite n | GSet, Finite n ->
        if n < 0 then failwith "Rank must be non-negative"
    | PermGroup, Infinite | MatGroup, Infinite | FpGroup, Infinite | PcGroup, Infinite
    | Module, Infinite | Set, Infinite | GSet, Infinite -> ()
    | Simplicial, Finite n | Chain, Finite n | Category, Finite n ->
        if n < 0 then failwith "Simplicial/Chain/Category rank must be non-negative"
    | Simplicial, Infinite | Chain, Infinite | Category, Infinite -> ()
    | Simplex, Infinite -> failwith "Simplex cannot have infinite rank (use Simplicial)"
    | Simplex, Finite n ->
        if List.length spec.spec_elements <> n + 1 then
          failwith "Simplex rank mismatch (elements)";
        if List.length spec.spec_faces <> n + 1 then
          failwith "Simplex rank mismatch (faces)"
  ) defn.specs;

  Printf.printf "Type %s checked successfully\n" defn.name

let imported_files = ref []

let rec process_cmd file_path = function
  | CImport path ->
      let path_with_ext =
        if Filename.check_suffix path ".dan" then path else path ^ ".dan"
      in
      let full_path =
        if Sys.file_exists path_with_ext then
          path_with_ext
        else
          let dir = Filename.dirname file_path in
          let local_path = Filename.concat dir path_with_ext in
          if Sys.file_exists local_path then
            local_path
          else
            path_with_ext
          in
      if not (List.mem full_path !imported_files) then (
        imported_files := full_path :: !imported_files;
        process_file full_path
      )
  | CDef defn ->
      check_type_def defn

and process_file file_path =
  Printf.printf "Loading file %s...\n" file_path;
  let ic = open_in file_path in
  let lexbuf = Lexing.from_channel ic in
  try
    let cmds = Dan_parser.file Dan_lexer.token lexbuf in
    close_in ic;
    List.iter (process_cmd file_path) cmds
  with
  | Parsing.Parse_error ->
      close_in ic;
      let pos = lexbuf.Lexing.lex_curr_p in
      failwith (Printf.sprintf "Parse error at %s:%d:%d" file_path pos.pos_lnum (pos.pos_cnum - pos.pos_bol))
  | e ->
      close_in ic;
      raise e

let main_run () =
  if Array.length Sys.argv < 2 then (
    Printf.printf "Usage: dan <file.dan>\n";
    exit 1
  );
  try
    process_file Sys.argv.(1);
    Printf.printf "All checks completed successfully!\n"
  with Failure msg ->
    Printf.printf "Error: %s\n" msg;
    exit 2

let () = main_run ()
