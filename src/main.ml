open Dirtt
open Format

type mode_type = SimplicialOnly | DirttOnly
let mode = ref SimplicialOnly

let imported_files = ref []
let global_simpl_ctx : (string * Simplicialtt.value) list ref = ref []

let is_cat_name x =
  String.length x > 0 && (let c = x.[0] in c >= 'A' && c <= 'Z')

let rec collect_cats = function
  | Syntax.EOp c | Syntax.ETw c -> collect_cats c
  | Syntax.ETensor (c1, c2) | Syntax.EFunc (c1, c2) | Syntax.EPair (c1, c2) -> collect_cats c1 @ collect_cats c2
  | Syntax.EHom (cat, _, _) -> collect_cats cat
  | Syntax.ECoend (cat, _, _) | Syntax.EEnd (cat, _, _) -> collect_cats cat
  | Syntax.EVar x -> if is_cat_name x then [x] else []
  | Syntax.EPi (a, (_, b)) | Syntax.ESig (a, (_, b)) -> collect_cats a @ collect_cats b
  | Syntax.ELam ((_, a), b) -> collect_cats a @ collect_cats b
  | Syntax.EApp (f, a) -> collect_cats f @ collect_cats a
  | Syntax.EExt (a, phi, f) -> collect_cats a @ collect_cats phi @ collect_cats f
  | Syntax.ESystem cases -> List.concat (List.map (fun (phi, t) -> collect_cats phi @ collect_cats t) cases)
  | _ -> []

let register_free_cats vars =
  List.iter (fun x ->
    if not (List.mem_assoc x !global_simpl_ctx) then
      global_simpl_ctx := (x, Simplicialtt.VUniv) :: !global_simpl_ctx
  ) vars

let rec process_cmd file_path cmd =

  match cmd with
  | Syntax.CModule name ->
      printf "Module %s (in %s)\n" name file_path
  | Syntax.CImport path ->
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
  | Syntax.CFunctor (name, args, cod) ->
      let args_dirtt = List.map (fun (cat, s) -> (to_cat cat, s)) args in
      let cod_dirtt = to_cat cod in
      printf "Declaring functor %s : %a\n" name pp_cat cod_dirtt;
      cat_fun_sigs := (name, { arg_types = args_dirtt; codomain = cod_dirtt }) :: !cat_fun_sigs;

      (* Register in simplicialtt global context *)
      let free = collect_cats cod @ List.concat (List.map (fun (cat, _) -> collect_cats cat) args) in
      register_free_cats free;
      let args_simpl = List.map (fun (cat, _) -> Simplicialtt.translate cat) args in

      let cod_simpl = Simplicialtt.translate cod in
      let rec make_pi_type = function
        | [] -> cod_simpl
        | arg :: rest -> Simplicialtt.EPi (arg, ("_", make_pi_type rest))
      in
      let functor_tp = make_pi_type args_simpl in
      let functor_tp_val = Simplicialtt.eval !global_simpl_ctx [] functor_tp in
      global_simpl_ctx := (name, functor_tp_val) :: !global_simpl_ctx

  | Syntax.CDefType (name, args, tp) ->
      printf "Defining type %s\n" name;
      let tp_dirtt = to_m_type tp in
      type_defs := (name, (args, tp_dirtt)) :: !type_defs

  | Syntax.CDefTerm (name, args, tp, term) ->
      printf "Defining term %s\n" name;
      let old_active = !active_type_params in
      (try
         active_type_params := args @ old_active;
         let tp_dirtt = to_m_type tp in
         let tp_expanded = expand_m_type tp_dirtt in
         let inferred_delta = infer_categories_from_type tp_expanded in
         let cat_args = List.filter (fun (v, _) -> List.mem v args) inferred_delta in
         let type_args = List.filter (fun v -> not (List.mem_assoc v cat_args)) args in
         active_type_params := type_args @ old_active;

         (* Check using dirtt engine *)
         let term_dirtt = to_m_term term in
         if !mode = DirttOnly then (
           let _ = check_sequent cat_args [] term_dirtt tp_expanded in
           printf "  => Term %s typechecked successfully (Dirtt Engine)\n" name
         );

         (* Check using simplicialtt compatibility engine *)
         if !mode = SimplicialOnly then (
           let free = collect_cats tp in
           register_free_cats free;
           let cat_args_simpl = List.map (fun (x, cat) ->

             (x, Simplicialtt.eval !global_simpl_ctx [] (cat_to_simpl cat))
           ) cat_args in
           let base_ctx = cat_args_simpl @ !global_simpl_ctx in
           let base_env = List.map (fun (x, v) -> (x, Simplicialtt.VNeutral (v, Simplicialtt.NVar x))) base_ctx in
           let term_simpl = m_term_to_simpl (expand_m_term term_dirtt) in
           let tp_simpl = m_type_to_simpl tp_expanded in
           let tp_val = Simplicialtt.eval base_ctx base_env tp_simpl in
           Simplicialtt.check base_ctx base_env term_simpl tp_val;
           printf "  => Term %s typechecked successfully (Simplicialtt Engine)\n" name
         );
         active_type_params := old_active
       with Failure msg ->
         active_type_params := old_active;
         printf "  => Term %s typechecking FAILED: %s\n" name msg)

  | Syntax.CCheck (delta, gamma, term, tp) ->
      (* Dirtt check *)
      let delta_dirtt = List.map (fun (x, cat) -> (x, to_cat cat)) delta in
      let gamma_dirtt = List.map (fun (x, t) -> (x, to_m_type t)) gamma in
      let term_dirtt = to_m_term term in
      let tp_dirtt = to_m_type tp in
      let tp_expanded = expand_m_type tp_dirtt in
      let gamma_expanded = List.map (fun (x, t) -> (x, expand_m_type t)) gamma_dirtt in

      if !mode = DirttOnly then (
        printf "Running Dirtt Engine:\n";
        check_sequent delta_dirtt gamma_expanded term_dirtt tp_expanded;
        printf "  => OK! (Valid Dirtt Sequent)\n\n"
      );

      if !mode = SimplicialOnly then (
        printf "Running Simplicialtt Compatibility Engine:\n";
        let free = List.concat (List.map (fun (_, cat) -> collect_cats cat) delta) @ collect_cats tp in
        register_free_cats free;
        let delta_simpl = List.map (fun (x, cat) ->

          (x, Simplicialtt.eval !global_simpl_ctx [] (to_cat cat |> cat_to_simpl))
        ) delta in
        let delta_env = List.map (fun (x, v) -> (x, Simplicialtt.VNeutral (v, Simplicialtt.NVar x))) delta_simpl in
        let base_ctx = delta_simpl @ !global_simpl_ctx in
        let base_env = delta_env @ List.map (fun (x, v) -> (x, Simplicialtt.VNeutral (v, Simplicialtt.NVar x))) !global_simpl_ctx in
        let gamma_simpl = List.map (fun (x, t) ->
          (x, Simplicialtt.eval base_ctx base_env (to_m_type t |> expand_m_type |> m_type_to_simpl))
        ) gamma in
        let ctx = gamma_simpl @ base_ctx in
        let env = List.map (fun (x, v) -> (x, Simplicialtt.VNeutral (v, Simplicialtt.NVar x))) gamma_simpl @ base_env in
        let term_simpl = m_term_to_simpl (expand_m_term term_dirtt) in
        let tp_simpl = m_type_to_simpl tp_expanded in
        let tp_val = Simplicialtt.eval ctx env tp_simpl in
        Simplicialtt.check ctx env term_simpl tp_val;
        printf "  => OK! (Valid Simplicialtt Compat Sequent)\n\n"
      )

  | Syntax.CCheckSimplicial (ctx, term, tp) ->
      if !mode = SimplicialOnly then (
        printf "Checking Simplicialtt Sequent...\n";
        let rec eval_ctx built_ctx built_env = function
          | [] -> (built_ctx, built_env)
          | (x, tp_expr) :: rest ->
              let tp_val = Simplicialtt.eval (built_ctx @ !global_simpl_ctx) built_env (Simplicialtt.translate tp_expr) in
              let vx = Simplicialtt.VNeutral (tp_val, Simplicialtt.NVar x) in
              eval_ctx ((x, tp_val) :: built_ctx) ((x, vx) :: built_env) rest
        in
        let (ctx_simpl, env_simpl) = eval_ctx [] [] ctx in
        let full_ctx = ctx_simpl @ !global_simpl_ctx in
        let full_env = env_simpl @ List.map (fun (x, v) -> (x, Simplicialtt.VNeutral (v, Simplicialtt.NVar x))) !global_simpl_ctx in
        let term_simpl = Simplicialtt.translate term in
        let tp_simpl = Simplicialtt.translate tp in
        let tp_val = Simplicialtt.eval full_ctx full_env tp_simpl in
        Simplicialtt.check full_ctx full_env term_simpl tp_val;
        printf "  => OK! (Valid Simplicialtt Sequent)\n\n"
      ) else (
        printf "Skipping Simplicialtt Sequent (Dirtt Only Mode)\n\n"
      )

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

let main_run () =
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
