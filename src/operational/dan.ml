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
  | E -> ()
  | Matrix m ->
      if not (List.mem defn.typ allowed_types) then failwith "Matrix only allowed in Group, Monoid, Ring, Category, Field"
      else List.iter (fun row -> List.iter (fun _ -> ()) row) m
  | Add (t1, t2) | Mul (t1, t2) ->
      if not (List.mem defn.typ [Ring; Field]) then failwith "Add/Mul only allowed in Ring, Field"
      else check_term defn env t1 allowed_types; check_term defn env t2 allowed_types
  | Div (t1, t2) ->
      if defn.typ <> Field then failwith "Div only allowed in Field"
      else check_term defn env t1 allowed_types; check_term defn env t2 allowed_types;
           if t2 = E then failwith "Division by zero"

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
        check_term defn env t1 [Group; Monoid; Ring; Category; Field];
        check_term defn env t2 [Group; Monoid; Ring; Category; Field];
        Hashtbl.add env id Simplex
    | Mapping (id, t1, t2) ->
        (match t1 with
         | Id lhs_id -> if not (Hashtbl.mem env lhs_id) then Hashtbl.add env lhs_id Simplex
         | _ -> ());
        check_term defn env t1 [Group; Monoid; Ring; Category; Field];
        check_term defn env t2 [Group; Monoid; Ring; Category; Field];
        Hashtbl.add env id Simplex
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
          check_term defn env t1 [Group; Monoid; Ring; Category; Field];
          check_term defn env t2 [Group; Monoid; Ring; Category; Field]
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
