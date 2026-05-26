open Dan_syntax

let lift_type_name = function
  | Simplex -> Syntax.EVar "Simplex"
  | Group -> Syntax.EVar "Group"
  | Simplicial -> Syntax.EVar "Simplicial"
  | Chain -> Syntax.EVar "Chain"
  | Category -> Syntax.EVar "Category"
  | Monoid -> Syntax.EVar "Monoid"
  | Ring -> Syntax.EVar "Ring"
  | Field -> Syntax.EVar "Field"
  | PermGroup -> Syntax.EVar "PermGroup"
  | MatGroup -> Syntax.EVar "MatGroup"
  | FpGroup -> Syntax.EVar "FpGroup"
  | PcGroup -> Syntax.EVar "PcGroup"
  | Module -> Syntax.EVar "Module"
  | Set -> Syntax.EVar "Set"
  | GSet -> Syntax.EVar "GSet"

let rec make_nested_tensor = function
  | [] -> Syntax.EVar "Simplex"
  | [x] -> x
  | x :: xs -> Syntax.ETensor (x, make_nested_tensor xs)

let rec make_nested_tensor_term = function
  | [] -> Syntax.EVar "refl"
  | [x] -> Syntax.EVar x
  | x :: xs -> Syntax.ETensor (Syntax.EVar x, make_nested_tensor_term xs)

let rec make_arrow_type arg_types ret_type =
  match arg_types with
  | [] -> ret_type
  | t :: ts -> Syntax.EFunc (t, make_arrow_type ts ret_type)

let rec make_lambda_term vars term_body =
  match vars with
  | [] -> term_body
  | (x, t) :: xs -> Syntax.ELam ((x, t), make_lambda_term xs term_body)

let lift_type_def defn =
  let var_types = List.concat (List.map (function
    | Decl (ids, typ) -> List.map (fun id -> (id, lift_type_name typ)) ids
    | Presentation (id, _) -> [(id, Syntax.EVar "FpGroup")]
    | Action (id, _, _) -> [(id, Syntax.EVar "Simplex")]
    | _ -> []
  ) defn.context) in
  let specs_typed = List.map (fun spec ->
    let vars = spec.spec_elements @ spec.spec_faces in
    let var_bindings = List.map (fun x ->
      let ty = match List.assoc_opt x var_types with
        | Some t -> t
        | None -> Syntax.EVar "Simplex"
      in
      (x, ty)
    ) vars in
    let term_expr = make_nested_tensor_term vars in
    let type_expr = make_nested_tensor (List.map snd var_bindings) in
    (var_bindings, term_expr, type_expr)
  ) defn.specs in
  let (var_bindings, final_term, final_type) = match specs_typed with
    | [] -> ([], Syntax.EVar "refl", Syntax.EVar "Simplex")
    | [x] -> x
    | _ ->
        let bindings = List.concat (List.map (fun (b, _, _) -> b) specs_typed) in
        let terms = List.map (fun (_, t, _) -> t) specs_typed in
        let types = List.map (fun (_, _, tp) -> tp) specs_typed in
        (bindings, make_nested_tensor terms, make_nested_tensor types)
  in
  let rec unique_bindings acc = function
    | [] -> List.rev acc
    | (x, t) :: rest ->
        if List.exists (fun (y, _) -> x = y) acc then
          unique_bindings acc rest
        else
          unique_bindings ((x, t) :: acc) rest
  in
  let var_bindings_unique = unique_bindings [] var_bindings in
  let tp = make_arrow_type (List.map snd var_bindings_unique) final_type in
  let term = make_lambda_term var_bindings_unique final_term in
  Syntax.CDefTerm (defn.name, ["Simplex"], tp, term)

let lift_import path =
  let base = Filename.basename path in
  let name = if Filename.check_suffix base ".dan" then Filename.chop_suffix base ".dan" else base in
  let target_name = if name = "category" then "category_dan" else name in
  "library/ulrik/" ^ target_name ^ ".ulrik"

let lift_cmd = function
  | CImport path -> Syntax.CImport (lift_import path)
  | CDef defn -> lift_type_def defn

let sanitize_ident s =
  if s = "" then "" else
  let s_ref = ref s in
  let replacements = [
    ("\xc3\xb6", "o");      (* ö *)
    ("\xe2\x88\x82", "d");  (* ∂ *)
    ("\xe2\x82\x80", "0");  (* ₀ *)
    ("\xe2\x82\x81", "1");  (* ₁ *)
    ("\xe2\x82\x82", "2");  (* ₂ *)
    ("\xe2\x82\x83", "3");  (* ₃ *)
    ("\xe2\x82\x84", "4");  (* ₄ *)
    ("\xe2\x82\x85", "5");  (* ₅ *)
    ("\xe2\x82\x86", "6");  (* ₆ *)
    ("\xe2\x82\x87", "7");  (* ₇ *)
    ("\xe2\x82\x88", "8");  (* ₈ *)
    ("\xe2\x82\x89", "9");  (* ₉ *)
    ("\xe2\x81\xb0", "0");  (* ⁰ *)
    ("\xe2\x81\xb4", "4");  (* ⁴ *)
    ("\xe2\x81\xb5", "5");  (* ⁵ *)
    ("\xe2\x81\xb6", "6");  (* ⁶ *)
    ("\xe2\x81\xb7", "7");  (* ⁷ *)
    ("\xe2\x81\xb8", "8");  (* ⁸ *)
    ("\xe2\x81\xb9", "9");  (* ⁹ *)
    ("\xc2\xb2", "2");      (* ² *)
    ("\xc2\xb3", "3");      (* ³ *)
    ("\xc2\xb9", "1");      (* ¹ *)
  ] in
  let rec replace str pattern replacement =
    let len = String.length pattern in
    if String.length str < len then str
    else if String.sub str 0 len = pattern then
      replacement ^ replace (String.sub str len (String.length str - len)) pattern replacement
    else
      String.sub str 0 1 ^ replace (String.sub str 1 (String.length str - 1)) pattern replacement
  in
  List.iter (fun (pat, rep) ->
    s_ref := replace !s_ref pat rep
  ) replacements;
  let s_clean = String.map (fun c ->
    if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_' || c = '\'' then
      c
    else
      '_'
  ) !s_ref in
  if String.length s_clean > 0 && s_clean.[0] >= '0' && s_clean.[0] <= '9' then
    "num" ^ s_clean
  else
    s_clean

let rec string_of_expr = function
  | Syntax.EVar x -> sanitize_ident x
  | Syntax.EApp (f, a) ->
      let f_str = string_of_expr f in
      let a_str = match a with
        | Syntax.EApp _ | Syntax.ELam _ | Syntax.EPi _ | Syntax.ESig _ -> "(" ^ string_of_expr a ^ ")"
        | _ -> string_of_expr a
      in
      f_str ^ " " ^ a_str
  | Syntax.ELam ((x, a), b) ->
      "\\(" ^ sanitize_ident x ^ " : " ^ string_of_expr a ^ "). " ^ string_of_expr b
  | Syntax.EPi (a, (x, b)) ->
      "(" ^ sanitize_ident x ^ " : " ^ string_of_expr a ^ ") -> " ^ string_of_expr b
  | Syntax.ESig (a, (x, b)) ->
      "(" ^ sanitize_ident x ^ " : " ^ string_of_expr a ^ ") * " ^ string_of_expr b
  | Syntax.EPair (a, b) ->
      "(" ^ string_of_expr a ^ ", " ^ string_of_expr b ^ ")"
  | Syntax.EFst a -> "fst(" ^ string_of_expr a ^ ")"
  | Syntax.ESnd a -> "snd(" ^ string_of_expr a ^ ")"
  | Syntax.EUniv -> "U"
  | Syntax.EId (_, x, y) ->
      string_of_expr x ^ " = " ^ string_of_expr y
  | Syntax.ERef (Syntax.EVar "_") -> "refl"
  | Syntax.ERef a -> "refl(" ^ string_of_expr a ^ ")"
  | Syntax.EIDir -> "𝕀"
  | Syntax.EZeroDir -> "0"
  | Syntax.EOneDir -> "1"
  | Syntax.ELeq (a, b) -> string_of_expr a ^ " <= " ^ string_of_expr b
  | Syntax.EShapeInc (a, b) -> string_of_expr a ^ " ⊆ " ^ string_of_expr b
  | Syntax.EExt (a, phi, f) ->
      "{ " ^ string_of_expr a ^ " |^" ^ string_of_expr phi ^ " " ^ string_of_expr f ^ " }"
  | Syntax.EModalPi (a, (x, b)) ->
      "μ(" ^ sanitize_ident x ^ " : " ^ string_of_expr a ^ "). " ^ string_of_expr b
  | Syntax.EModalLam ((x, a), b) ->
      "λ^μ(" ^ sanitize_ident x ^ " : " ^ string_of_expr a ^ "). " ^ string_of_expr b
  | Syntax.EModalApp (f, a) ->
      string_of_expr f ^ " @ " ^ string_of_expr a
  | Syntax.ETw a -> string_of_expr a ^ "^tw"
  | Syntax.EOp a -> string_of_expr a ^ "^op"
  | Syntax.ETwPi0 a -> "π₀(" ^ string_of_expr a ^ ")"
  | Syntax.ETwPi1 a -> "π₁(" ^ string_of_expr a ^ ")"
  | Syntax.EJoin (a, b) -> string_of_expr a ^ " ∨ " ^ string_of_expr b
  | Syntax.EMeet (a, b) -> string_of_expr a ^ " ∧ " ^ string_of_expr b
  | Syntax.ENeg a -> "¬" ^ string_of_expr a
  | Syntax.EHom (cat, a, b) ->
      "hom(" ^ string_of_expr cat ^ ", " ^ string_of_expr a ^ ", " ^ string_of_expr b ^ ")"
  | Syntax.ETensor (a, b) -> string_of_expr a ^ " * " ^ string_of_expr b
  | Syntax.EFunc (a, b) -> string_of_expr a ^ " -> " ^ string_of_expr b
  | Syntax.ECoend (cat, w, m) ->
      "coend(" ^ sanitize_ident w ^ " : " ^ string_of_expr cat ^ "). " ^ string_of_expr m
  | Syntax.EEnd (cat, w, m) ->
      "end(" ^ sanitize_ident w ^ " : " ^ string_of_expr cat ^ "). " ^ string_of_expr m
  | Syntax.EIdTerm a -> "id(" ^ string_of_expr a ^ ")"
  | _ -> "<expr>"

let string_of_cmd = function
  | Syntax.CModule name -> "module " ^ sanitize_ident name ^ " where"
  | Syntax.CImport path -> "import \"" ^ path ^ "\""
  | Syntax.CDefType (name, args, tp) ->
      let args_str = if args = [] then "" else " (" ^ String.concat " " (List.map sanitize_ident args) ^ ")" in
      "def_type " ^ sanitize_ident name ^ args_str ^ " := " ^ string_of_expr tp
  | Syntax.CDefTerm (name, args, tp, term) ->
      let args_str = if args = [] then "" else " (" ^ String.concat " " (List.map sanitize_ident args) ^ ")" in
      "def_term " ^ sanitize_ident name ^ args_str ^ " : " ^ string_of_expr tp ^ " := " ^ string_of_expr term
  | Syntax.CCheckSimplicial (ctx, term, tp) ->
      let ctx_str = String.concat ", " (List.map (fun (x, t) -> sanitize_ident x ^ " : " ^ string_of_expr t) ctx) in
      "check " ^ ctx_str ^ " ⊢ " ^ string_of_expr term ^ " : " ^ string_of_expr tp
  | _ -> "<cmd>"

let main () =
  if Array.length Sys.argv < 2 then (
    Printf.printf "Usage: lift <file.dan>\n";
    exit 1
  );
  let file_path = Sys.argv.(1) in
  let module_name =
    let base = Filename.basename file_path in
    if Filename.check_suffix base ".dan" then Filename.chop_suffix base ".dan" else base
  in
  let ic = open_in file_path in
  let lexbuf = Lexing.from_channel ic in
  try
    let cmds = Dan_parser.file Dan_lexer.token lexbuf in
    close_in ic;
    Printf.printf "module %s where\n\n" (sanitize_ident module_name);
    List.iter (fun cmd ->
      let lifted = lift_cmd cmd in
      Printf.printf "%s\n\n" (string_of_cmd lifted)
    ) cmds
  with e ->
    close_in ic;
    raise e

let () = main ()
