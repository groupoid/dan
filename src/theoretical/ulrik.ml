open Format
open Simplicialtt

let rec process_cmd file_path = function
  | Syntax.CModule name ->
      printf "Module %s (in %s)\n" name file_path
  | Syntax.CImport path ->
      let path_with_ext =
        if Filename.check_suffix path ".ulrik" then path else path ^ ".ulrik"
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
  | Syntax.CCheckSimplicial (ctx, term, tp) ->
      printf "Checking Simplicialtt Sequent...\n";
      let rec eval_ctx built_ctx built_env = function
        | [] -> (built_ctx, built_env)
        | (x, tp_expr) :: rest ->
            let tp_val = Simplicialtt.eval (built_ctx @ !Main.global_simpl_ctx) built_env (Simplicialtt.translate tp_expr) in
            let vx = Simplicialtt.VNeutral (tp_val, Simplicialtt.NVar x) in
            eval_ctx ((x, tp_val) :: built_ctx) ((x, vx) :: built_env) rest
      in
      let (ctx_simpl, env_simpl) = eval_ctx [] !Main.global_simpl_env ctx in
      let full_ctx = ctx_simpl @ !Main.global_simpl_ctx in
      let full_env = env_simpl in
      let term_simpl = Simplicialtt.translate term in
      let tp_simpl = Simplicialtt.translate tp in
      let tp_val = Simplicialtt.eval full_ctx full_env tp_simpl in
      Simplicialtt.check full_ctx full_env term_simpl tp_val;
      printf "  => OK! (Valid Simplicialtt Sequent)\n\n"
  | Syntax.CDef (name, args, opt_tp, term) ->
      if args <> [] then (
        printf "Skipping Parameterized Definition %s (STT Mode)\n\n" name
      ) else (
        printf "Defining %s (STT)\n" name;
        let term_simpl = Simplicialtt.translate term in
        match opt_tp with
        | Some tp ->
            let tp_simpl = Simplicialtt.translate tp in
            let tp_val = Simplicialtt.eval !Main.global_simpl_ctx !Main.global_simpl_env tp_simpl in
            Simplicialtt.check !Main.global_simpl_ctx !Main.global_simpl_env term_simpl tp_val;
            let term_val = Simplicialtt.eval !Main.global_simpl_ctx !Main.global_simpl_env term_simpl in
            Main.global_simpl_ctx := (name, tp_val) :: !Main.global_simpl_ctx;
            Main.global_simpl_env := (name, term_val) :: !Main.global_simpl_env
        | None ->
            let tp_val = Simplicialtt.infer !Main.global_simpl_ctx !Main.global_simpl_env term_simpl in
            let term_val = Simplicialtt.eval !Main.global_simpl_ctx !Main.global_simpl_env term_simpl in
            Main.global_simpl_ctx := (name, tp_val) :: !Main.global_simpl_ctx;
            Main.global_simpl_env := (name, term_val) :: !Main.global_simpl_env
      )
  | Syntax.CFunctor _ | Syntax.CCheck _ ->
      printf "Skipping Dirtt Construct (STT Mode)\n\n"

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
