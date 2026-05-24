open Dirtt
open Format

let imported_files = ref []

let rec process_cmd file_path cmd =
  match cmd with
  | CModule name ->
      printf "Module %s (in %s)\n" name file_path
  | CImport path ->
      let path_with_ext =
        if Filename.check_suffix path ".ulrik" then path else path ^ ".ulrik"
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
  | CFunctor (name, args, cod) ->
      printf "Declaring functor %s : %a\n" name pp_cat cod;
      cat_fun_sigs := (name, { arg_types = args; codomain = cod }) :: !cat_fun_sigs
  | CDefType (name, args, tp) ->
      printf "Defining type %s\n" name;
      type_defs := (name, (args, tp)) :: !type_defs
  | CDefTerm (name, args, tp, term) ->
      printf "Defining term %s\n" name;
      let old_active = !active_type_params in
      (try
         active_type_params := args @ old_active;
         let tp_expanded = expand_m_type tp in
         let inferred_delta = infer_categories_from_type tp_expanded in
         let cat_args = List.filter (fun (v, _) -> List.mem v args) inferred_delta in
         let type_args = List.filter (fun v -> not (List.mem_assoc v cat_args)) args in
         active_type_params := type_args @ old_active;
         let _ = check_sequent cat_args [] term tp_expanded in
         active_type_params := old_active;
         printf "  => Term %s typechecked successfully\n" name
       with Failure msg ->
         active_type_params := old_active;
         printf "  => Term %s typechecking FAILED: %s\n" name msg)
  | CCheck (delta, gamma, term, tp) ->
      check_sequent delta gamma term tp

and process_file file_path =
  printf "Loading file %s...\n" file_path;
  let ic = open_in file_path in
  let lexbuf = Lexing.from_channel ic in
  try
    let cmds = Parser.file Lexer.token lexbuf in
    close_in ic;
    List.iter (process_cmd file_path) cmds
  with
  | Parsing.Parse_error ->
      close_in ic;
      let pos = lexbuf.Lexing.lex_curr_p in
      failwith (sprintf "Parse error at %s:%d:%d" file_path pos.pos_lnum (pos.pos_cnum - pos.pos_bol))
  | e ->
      close_in ic;
      raise e

let () =
  if Array.length Sys.argv < 2 then (
    printf "Usage: %s <file.ulrik>\n" Sys.argv.(0);
    exit 1
  );
  try
    process_file Sys.argv.(1);
    printf "All checks completed successfully!\n"
  with Failure msg ->
    printf "Error: %s\n" msg;
    exit 2
