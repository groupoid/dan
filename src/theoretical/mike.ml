open Dirtt
open Format



let rec process_cmd file_path = function
  | Syntax.CModule name ->
      printf "Module %s (in %s)\n" name file_path
  | Syntax.CImport path ->
      let path_with_ext =
        if Filename.check_suffix path ".mike" then path else path ^ ".mike"
      in
      let full_path =
        if Sys.file_exists path_with_ext then path_with_ext
        else
          let dir = Filename.dirname file_path in
          let local_path = Filename.concat dir path_with_ext in
          if Sys.file_exists local_path then local_path
          else path_with_ext
      in
      if not (List.mem full_path !Main.imported_files) then (
        Main.imported_files := full_path :: !Main.imported_files;
        Main.process_file process_cmd full_path
      )
  | Syntax.CFunctor (name, args, cod) ->
      let args_dirtt = List.map (fun (cat, s) -> (to_cat cat, s)) args in
      let cod_dirtt = to_cat cod in
      printf "Declaring functor %s : %a\n" name pp_cat cod_dirtt;
      cat_fun_sigs := (name, { arg_types = args_dirtt; codomain = cod_dirtt }) :: !cat_fun_sigs
  | Syntax.CDef (name, args, opt_tp, term) ->
      (match opt_tp with
       | None ->
           printf "Defining type %s (Dirtt)\n" name;
           let tp_dirtt = to_m_type term in
           type_defs := (name, (args, tp_dirtt)) :: !type_defs
       | Some tp ->
           printf "Defining term %s (Dirtt)\n" name;
           let old_active = !active_type_params in
           (try
              active_type_params := args @ old_active;
              let tp_dirtt = to_m_type tp in
              let tp_expanded = expand_m_type tp_dirtt in
              let inferred_delta = infer_categories_from_type tp_expanded in
              let cat_args = List.filter (fun (v, _) -> List.mem v args) inferred_delta in
              let type_args = List.filter (fun v -> not (List.mem_assoc v cat_args)) args in
              active_type_params := type_args @ old_active;

              let term_dirtt = to_m_term term in
              let _ = check_sequent cat_args [] term_dirtt tp_expanded in
              printf "  => Term %s typechecked successfully (Dirtt Engine)\n" name;
              active_type_params := old_active
            with Failure msg ->
              active_type_params := old_active;
              printf "  => Term %s typechecking FAILED: %s\n" name msg))
  | Syntax.CCheck (delta, gamma, term, tp) ->
      let delta_dirtt = List.map (fun (x, cat) -> (x, to_cat cat)) delta in
      let gamma_dirtt = List.map (fun (x, t) -> (x, to_m_type t)) gamma in
      let term_dirtt = to_m_term term in
      let tp_dirtt = to_m_type tp in
      let tp_expanded = expand_m_type tp_dirtt in
      let gamma_expanded = List.map (fun (x, t) -> (x, expand_m_type t)) gamma_dirtt in
      printf "Running Dirtt Engine:\n";
      check_sequent delta_dirtt gamma_expanded term_dirtt tp_expanded;
      printf "  => OK! (Valid Dirtt Sequent)\n\n"
  | Syntax.CCheckSimplicial _ ->
      printf "Skipping Simplicialtt Sequent (Dirtt Only Mode)\n\n"
  | _ -> failwith "Unsupported command in Dirtt (Mike) mode"

let main () =
  if Array.length Sys.argv < 2 then (
    printf "Usage: %s <file.ulrik>\n" Sys.argv.(0);
    exit 1
  );
  try
    Main.process_file process_cmd Sys.argv.(1);
    printf "All checks completed successfully!\n"
  with Failure msg ->
    printf "Error: %s\n" msg;
    exit 2

let () = main ()
