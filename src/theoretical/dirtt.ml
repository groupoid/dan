(* dirtt by Michael Shulman *)

open Syntax
open Format

type name = string

type cat =
  | CVar of name
  | COp of cat
  | CProd of cat * cat

type cat_term =
  | CTVar of name
  | CTFun of name * cat_term list
  | CTOp of cat_term

type m_type =
  | MHom of cat * cat_term * cat_term
  | MTensor of m_type * m_type
  | MCoend of cat * name * m_type
  | MEnd of cat * name * m_type
  | MFunc of m_type * m_type
  | MApp of name * cat_term list

type m_term =
  | MTId of cat_term
  | MTJ of m_type * name * name * name * m_term * cat_term * cat_term * m_term
  | MTJCov of m_type * name * m_term * cat_term * m_term
  | MTJContra of m_type * name * m_term * cat_term * m_term
  | MTTensorIntro of m_term * m_term
  | MTTensorElim of name * name * m_term * m_term
  | MTCoendIntro of name * name * name * m_term
  | MTCoendElim of name * name * m_term * m_term
  | MTEndIntro of name * m_term
  | MTEndElim of name * name * name * m_term * m_term
  | MTFuncIntro of name * m_type * m_term
  | MTFuncElim of m_term * m_term
  | MTVar of name

let rec to_cat = function
  | EVar x -> CVar x
  | EOp c -> COp (to_cat c)
  | ETw c -> COp (to_cat c)
  | ETensor (c1, c2) -> CProd (to_cat c1, to_cat c2)
  | e -> failwith "invalid dirtt category"

and to_cat_term = function
  | EVar x -> CTVar x
  | EApp (f, a) ->
      let rec collect_args acc = function
        | EApp (f, a) -> collect_args (flatten_expr_to_cat_terms a @ acc) f
        | EVar f -> (f, acc)
        | _ -> failwith "invalid category function application"
      in
      let (f, args) = collect_args (flatten_expr_to_cat_terms a) f in
      CTFun (f, args)
  | EOp a -> CTOp (to_cat_term a)
  | ETw a -> CTOp (to_cat_term a)

and flatten_expr_to_cat_terms = function
  | EPair (e1, e2) -> flatten_expr_to_cat_terms e1 @ flatten_expr_to_cat_terms e2
  | e -> [to_cat_term e]
  | e ->
      let rec string_of_expr = function
        | EVar s -> "EVar " ^ s
        | EApp (f, a) -> "EApp (" ^ string_of_expr f ^ ", " ^ string_of_expr a ^ ")"
        | ELam ((x, Some t), b) -> "ELam ((" ^ x ^ ", Some " ^ string_of_expr t ^ "), " ^ string_of_expr b ^ ")"
        | ELam ((x, None), b) -> "ELam ((" ^ x ^ ", None), " ^ string_of_expr b ^ ")"
        | EPi (a, (x, b)) -> "EPi (" ^ string_of_expr a ^ ", (" ^ x ^ ", " ^ string_of_expr b ^ "))"
        | ESig (a, (x, b)) -> "ESig (" ^ string_of_expr a ^ ", (" ^ x ^ ", " ^ string_of_expr b ^ "))"
        | EPair (a, b) -> "EPair (" ^ string_of_expr a ^ ", " ^ string_of_expr b ^ ")"
        | EFst a -> "EFst (" ^ string_of_expr a ^ ")"
        | ESnd a -> "ESnd (" ^ string_of_expr a ^ ")"
        | EUniv -> "EUniv"
        | EId (a, b, c) -> "EId (" ^ string_of_expr a ^ ", " ^ string_of_expr b ^ ", " ^ string_of_expr c ^ ")"
        | ERef a -> "ERef (" ^ string_of_expr a ^ ")"
        | EIDir -> "EIDir"
        | EZeroDir -> "EZeroDir"
        | EOneDir -> "EOneDir"
        | ELeq (a, b) -> "ELeq (" ^ string_of_expr a ^ ", " ^ string_of_expr b ^ ")"
        | EShapeInc (a, b) -> "EShapeInc (" ^ string_of_expr a ^ ", " ^ string_of_expr b ^ ")"
        | EExt (a, b, c) -> "EExt (" ^ string_of_expr a ^ ", " ^ string_of_expr b ^ ", " ^ string_of_expr c ^ ")"
        | ESystem _ -> "ESystem"
        | EModalPi (a, (x, b)) -> "EModalPi (" ^ string_of_expr a ^ ", (" ^ x ^ ", " ^ string_of_expr b ^ "))"
        | EModalLam ((x, a), b) -> "EModalLam ((" ^ x ^ ", " ^ string_of_expr a ^ "), " ^ string_of_expr b ^ ")"
        | EModalApp (f, a) -> "EModalApp (" ^ string_of_expr f ^ ", " ^ string_of_expr a ^ ")"
        | ETw a -> "ETw (" ^ string_of_expr a ^ ")"
        | EOp a -> "EOp (" ^ string_of_expr a ^ ")"
        | ETwPi0 a -> "ETwPi0 (" ^ string_of_expr a ^ ")"
        | ETwPi1 a -> "ETwPi1 (" ^ string_of_expr a ^ ")"
        | EJoin (a, b) -> "EJoin (" ^ string_of_expr a ^ ", " ^ string_of_expr b ^ ")"
        | EMeet (a, b) -> "EMeet (" ^ string_of_expr a ^ ", " ^ string_of_expr b ^ ")"
        | ENeg a -> "ENeg (" ^ string_of_expr a ^ ")"
        | EHom (a, b, c) -> "EHom (" ^ string_of_expr a ^ ", " ^ string_of_expr b ^ ", " ^ string_of_expr c ^ ")"
        | ETensor (a, b) -> "ETensor (" ^ string_of_expr a ^ ", " ^ string_of_expr b ^ ")"
        | EFunc (a, b) -> "EFunc (" ^ string_of_expr a ^ ", " ^ string_of_expr b ^ ")"
        | ECoend (a, x, b) -> "ECoend (" ^ string_of_expr a ^ ", " ^ x ^ ", " ^ string_of_expr b ^ ")"
        | EEnd (a, x, b) -> "EEnd (" ^ string_of_expr a ^ ", " ^ x ^ ", " ^ string_of_expr b ^ ")"
        | EIdTerm a -> "EIdTerm (" ^ string_of_expr a ^ ")"
        | EJ _ -> "EJ"
        | EJCov _ -> "EJCov"
        | EJContra _ -> "EJContra"
        | ETensorElim _ -> "ETensorElim"
        | ECoendIntro _ -> "ECoendIntro"
        | ECoendElim _ -> "ECoendElim"
        | EEndElim _ -> "EEndElim"
      in
      failwith ("invalid category term: " ^ string_of_expr e)

and to_m_type = function
  | EHom (cat, a, b) -> MHom (to_cat cat, to_cat_term a, to_cat_term b)
  | ETensor (m1, m2) -> MTensor (to_m_type m1, to_m_type m2)
  | ECoend (cat, w, m) -> MCoend (to_cat cat, w, to_m_type m)
  | EEnd (cat, w, m) -> MEnd (to_cat cat, w, to_m_type m)
  | EFunc (m1, m2) -> MFunc (to_m_type m1, to_m_type m2)
  | EApp (f, a) ->
      let rec collect_args acc = function
        | EApp (f, a) -> collect_args (flatten_expr_to_cat_terms a @ acc) f
        | EVar f -> (f, acc)
        | _ -> failwith "invalid module type application"
      in
      let (f, args) = collect_args (flatten_expr_to_cat_terms a) f in
      MApp (f, args)
  | EVar f -> MApp (f, [])
  | e -> failwith "invalid module type"

and to_m_term = function
  | EVar x -> MTVar x
  | EIdTerm a -> MTId (to_cat_term a)
  | EJ (tp, x, y, z, mz, a, b, f) ->
      MTJ (to_m_type tp, x, y, z, to_m_term mz, to_cat_term a, to_cat_term b, to_m_term f)
  | EJCov (tp, x, m, a, f) ->
      MTJCov (to_m_type tp, x, to_m_term m, to_cat_term a, to_m_term f)
  | EJContra (tp, x, m, b, f) ->
      MTJContra (to_m_type tp, x, to_m_term m, to_cat_term b, to_m_term f)
  | ETensor (m1, m2) -> MTTensorIntro (to_m_term m1, to_m_term m2)
  | ETensorElim (x, y, t, c) -> MTTensorElim (x, y, to_m_term t, to_m_term c)
  | ECoendIntro (x, y, z, m) -> MTCoendIntro (x, y, z, to_m_term m)
  | ECoendElim (w, m_var, t, c) -> MTCoendElim (w, m_var, to_m_term t, to_m_term c)
  | EEndElim (x, y, z, t, c) -> MTEndElim (x, y, z, to_m_term t, to_m_term c)
  | ELam ((x, Some tp), body) -> MTFuncIntro (x, to_m_type tp, to_m_term body)
  | ELam ((w, None), body) -> MTEndIntro (w, to_m_term body)
  | EApp (f, a) -> MTFuncElim (to_m_term f, to_m_term a)
  | EModalApp (f, a) -> MTFuncElim (to_m_term f, to_m_term a)
  | e -> failwith "invalid module term"

type sign = [ `Cov | `Contra ]

type cat_fun_sig = {
  arg_types : (cat * sign) list;
  codomain : cat;
}

type cmd =
  | CModule of string
  | CImport of string
  | CFunctor of name * (cat * sign) list * cat
  | CDefType of name * name list * m_type
  | CDefTerm of name * name list * m_type * m_term
  | CCheck of (name * cat) list * (name * m_type) list * m_term * m_type

let cat_fun_sigs : (name * cat_fun_sig) list ref = ref []
let type_defs : (name * (name list * m_type)) list ref = ref []
let active_type_params : string list ref = ref []

(* Printing *)
let rec pp_list pp fmt = function
  | [] -> ()
  | [x] -> pp fmt x
  | x :: xs -> fprintf fmt "%a, %a" pp x (pp_list pp) xs

let rec pp_cat fmt = function
  | CVar x -> fprintf fmt "%s" x
  | COp c -> fprintf fmt "%a^op" pp_cat_paren c
  | CProd (c1, c2) -> fprintf fmt "%a × %a" pp_cat_paren c1 pp_cat_paren c2

and pp_cat_paren fmt c =
  match c with
  | COp _ | CProd _ -> fprintf fmt "(%a)" pp_cat c
  | _ -> pp_cat fmt c

let rec pp_cat_term fmt = function
  | CTVar x -> fprintf fmt "%s" x
  | CTFun (f, args) ->
      fprintf fmt "%s(%a)" f (pp_list pp_cat_term) args
  | CTOp a -> fprintf fmt "%a†" pp_cat_term_paren a

and pp_cat_term_paren fmt a =
  match a with
  | CTFun _ | CTOp _ -> fprintf fmt "(%a)" pp_cat_term a
  | _ -> pp_cat_term fmt a

let rec pp_m_type fmt = function
  | MHom (cat, a, b) -> fprintf fmt "hom_%a(%a, %a)" pp_cat cat pp_cat_term a pp_cat_term b
  | MTensor (m1, m2) -> fprintf fmt "%a ⊗ %a" pp_m_type_paren m1 pp_m_type_paren m2
  | MCoend (cat, w, m) -> fprintf fmt "∫^{%s:%a} %a" w pp_cat cat pp_m_type m
  | MEnd (cat, w, m) -> fprintf fmt "∫_{%s:%a} %a" w pp_cat cat pp_m_type m
  | MFunc (m1, m2) -> fprintf fmt "%a ⊸ %a" pp_m_type_paren m1 pp_m_type_paren m2
  | MApp (name, args) -> fprintf fmt "%s(%a)" name (pp_list pp_cat_term) args

and pp_m_type_paren fmt m =
  match m with
  | MTensor _ | MFunc _ | MCoend _ | MEnd _ -> fprintf fmt "(%a)" pp_m_type m
  | _ -> pp_m_type fmt m

let rec pp_m_term fmt = function
  | MTId a -> fprintf fmt "id(%a)" pp_cat_term a
  | MTJ (tp, x, y, z, mz, a, b, f) ->
      fprintf fmt "J(%s.%s.%a, %s, %a; %a, %a, %a)" x y pp_m_type tp z pp_m_term mz pp_cat_term a pp_cat_term b pp_m_term f
  | MTJCov (tp, x, m, a, f) ->
      fprintf fmt "J_cov(%s.%a, %a, %a, %a)" x pp_m_type tp pp_m_term m pp_cat_term a pp_m_term f
  | MTJContra (tp, x, m, b, f) ->
      fprintf fmt "J_contra(%s.%a, %a, %a, %a)" x pp_m_type tp pp_m_term m pp_cat_term b pp_m_term f
  | MTTensorIntro (m1, m2) -> fprintf fmt "%a ⊗ %a" pp_m_term m1 pp_m_term m2
  | MTTensorElim (x, y, t, c) -> fprintf fmt "let %s ⊗ %s := %a in %a" x y pp_m_term t pp_m_term c
  | MTCoendIntro (x, y, z, m) -> fprintf fmt "mix %s %s := %s in %a" x y z pp_m_term m
  | MTCoendElim (w, m_var, t, c) -> fprintf fmt "let ⟨%s, %s⟩ := %a in %a" w m_var pp_m_term t pp_m_term c
  | MTEndIntro (w, m) -> fprintf fmt "end_intro(%s, %a)" w pp_m_term m
  | MTEndElim (x, y, z, t, c) -> fprintf fmt "let %s %s @ %s := %a in %a" x y z pp_m_term t pp_m_term c
  | MTFuncIntro (x, tp, body) -> fprintf fmt "λ(%s : %a). %a" x pp_m_type tp pp_m_term body
  | MTFuncElim (f, a) -> fprintf fmt "%a @ %a" pp_m_term f pp_m_term a
  | MTVar x -> fprintf fmt "%s" x

(* Helpers *)
let flip_sign = function
  | `Cov -> `Contra
  | `Contra -> `Cov

let flip_vars vars =
  List.map (fun (x, s) -> (x, flip_sign s)) vars

let rec op_cat = function
  | COp c -> c
  | c -> COp c

(* Substitution for category terms *)
let rec subst_cat_term (substs : (name * cat_term) list) = function
  | CTVar x ->
      (match List.assoc_opt x substs with
       | Some t -> t
       | None -> CTVar x)
  | CTFun (f, args) ->
      let f' = match List.assoc_opt f substs with
        | Some (CTVar y) -> y
        | _ -> f
      in
      CTFun (f', List.map (subst_cat_term substs) args)
  | CTOp a -> CTOp (subst_cat_term substs a)

let rec subst_cat_in_m_type (substs : (name * cat_term) list) = function
  | MHom (cat, a, b) -> MHom (cat, subst_cat_term substs a, subst_cat_term substs b)
  | MTensor (m1, m2) -> MTensor (subst_cat_in_m_type substs m1, subst_cat_in_m_type substs m2)
  | MCoend (cat, w, m) ->
      let filtered = List.filter (fun (x, _) -> x <> w) substs in
      MCoend (cat, w, subst_cat_in_m_type filtered m)
  | MEnd (cat, w, m) ->
      let filtered = List.filter (fun (x, _) -> x <> w) substs in
      MEnd (cat, w, subst_cat_in_m_type filtered m)
  | MFunc (m1, m2) -> MFunc (subst_cat_in_m_type substs m1, subst_cat_in_m_type substs m2)
  | MApp (name, args) -> MApp (name, List.map (subst_cat_term substs) args)

(* Polarized Substitution for Binders (Coends/Ends) *)
let rec subst_polarized_cat_term (sign : sign) (w : name) (a_cov : cat_term) (a_contra : cat_term) (t : cat_term) : cat_term =
  match t with
  | CTVar x ->
      if x = w then (
        match sign with
        | `Cov -> a_cov
        | `Contra -> a_contra
      ) else CTVar x
  | CTFun (f, args) ->
      let sig_f = List.assoc f !cat_fun_sigs in
      let args' = List.map2 (fun arg (_, s) ->
        let arg_sign = if s = `Contra then flip_sign sign else sign in
        subst_polarized_cat_term arg_sign w a_cov a_contra arg
      ) args sig_f.arg_types in
      CTFun (f, args')
  | CTOp a ->
      CTOp (subst_polarized_cat_term (flip_sign sign) w a_cov a_contra a)

let rec subst_polarized_m_type (sign : sign) (w : name) (a_cov : cat_term) (a_contra : cat_term) (tp : m_type) : m_type =
  match tp with
  | MHom (cat, a, b) ->
      let a' = subst_polarized_cat_term (flip_sign sign) w a_cov a_contra a in
      let b' = subst_polarized_cat_term sign w a_cov a_contra b in
      MHom (cat, a', b')
  | MTensor (m1, m2) ->
      MTensor (subst_polarized_m_type sign w a_cov a_contra m1,
               subst_polarized_m_type sign w a_cov a_contra m2)
  | MCoend (cat, y, m) ->
      if y = w then MCoend (cat, y, m)
      else MCoend (cat, y, subst_polarized_m_type sign w a_cov a_contra m)
  | MEnd (cat, y, m) ->
      if y = w then MEnd (cat, y, m)
      else MEnd (cat, y, subst_polarized_m_type sign w a_cov a_contra m)
  | MFunc (m1, m2) ->
      MFunc (subst_polarized_m_type (flip_sign sign) w a_cov a_contra m1,
             subst_polarized_m_type sign w a_cov a_contra m2)
  | MApp (name, args) ->
      MApp (name, List.map (subst_polarized_cat_term sign w a_cov a_contra) args)

let rec expand_m_type = function
  | MApp (f, args) ->
      if List.mem f !active_type_params then
        MApp (f, args)
      else
        (match List.assoc_opt f !type_defs with
         | Some (params, body) ->
             if List.length params <> List.length args then
               failwith ("arity mismatch for type definition " ^ f);
             let substs = List.combine params args in
             expand_m_type (subst_cat_in_m_type substs body)
         | None -> failwith ("unbound type definition: " ^ f))
  | MHom (cat, a, b) -> MHom (cat, a, b)
  | MTensor (m1, m2) -> MTensor (expand_m_type m1, expand_m_type m2)
  | MCoend (cat, w, m) -> MCoend (cat, w, expand_m_type m)
  | MEnd (cat, w, m) -> MEnd (cat, w, expand_m_type m)
  | MFunc (m1, m2) -> MFunc (expand_m_type m1, expand_m_type m2)

let rec expand_m_term = function
  | MTVar x -> MTVar x
  | MTId a -> MTId a
  | MTJ (tp, x, y, z, mz, a, b, f) ->
      MTJ (expand_m_type tp, x, y, z, expand_m_term mz, a, b, expand_m_term f)
  | MTJCov (tp, x, m, a, f) ->
      MTJCov (expand_m_type tp, x, expand_m_term m, a, expand_m_term f)
  | MTJContra (tp, x, m, b, f) ->
      MTJContra (expand_m_type tp, x, expand_m_term m, b, expand_m_term f)
  | MTTensorIntro (m1, m2) ->
      MTTensorIntro (expand_m_term m1, expand_m_term m2)
  | MTTensorElim (x, y, t, c) ->
      MTTensorElim (x, y, expand_m_term t, expand_m_term c)
  | MTCoendIntro (x, y, z, m) ->
      MTCoendIntro (x, y, z, expand_m_term m)
  | MTCoendElim (w, m_var, t, c) ->
      MTCoendElim (w, m_var, expand_m_term t, expand_m_term c)
  | MTEndIntro (w, m) ->
      MTEndIntro (w, expand_m_term m)
  | MTEndElim (x, y, z, t, c) ->
      MTEndElim (x, y, z, expand_m_term t, expand_m_term c)
  | MTFuncIntro (x, tp, body) ->
      MTFuncIntro (x, expand_m_type tp, expand_m_term body)
  | MTFuncElim (f, a) ->
      MTFuncElim (expand_m_term f, expand_m_term a)

(* Category Term Inferer *)
let rec infer_cat_term (delta : (name * cat) list) (t : cat_term) : cat * (name * sign) list =
  match t with
  | CTVar x ->
      (match List.assoc_opt x delta with
       | Some c -> (c, [(x, `Cov)])
       | None -> failwith ("unbound category variable: " ^ x))
  | CTFun (f, args) ->
      let sig_f =
        try List.assoc f !cat_fun_sigs
        with Not_found -> failwith ("unbound category generator function: " ^ f)
      in
      if List.length args <> List.length sig_f.arg_types then
        failwith ("generator function " ^ f ^ " arity mismatch");
      let vars = List.map2 (fun arg (expected_tp, s) ->
        let (inferred_tp, arg_vars) = infer_cat_term delta arg in
        if inferred_tp <> expected_tp then
          failwith ("type mismatch in arguments of " ^ f);
        if s = `Contra then flip_vars arg_vars else arg_vars
      ) args sig_f.arg_types in
      (sig_f.codomain, List.concat vars)
  | CTOp a ->
      let (tp, vars) = infer_cat_term delta a in
      (op_cat tp, flip_vars vars)

(* Module Type Inferer *)
let rec infer_m_type (delta : (name * cat) list) (tp : m_type) : (name * sign) list =
  match expand_m_type tp with
  | MHom (cat, a, b) ->
      let (ta, vars_a) = infer_cat_term delta a in
      let (tb, vars_b) = infer_cat_term delta b in
      if ta <> cat || tb <> cat then
        failwith "hom term categories must match signature";
      flip_vars vars_a @ vars_b
  | MTensor (m1, m2) ->
      infer_m_type delta m1 @ infer_m_type delta m2
  | MCoend (cat, w, m) ->
      let delta_ext = (w, cat) :: delta in
      let vars_m = infer_m_type delta_ext m in
      let w_occs = List.filter (fun (x, _) -> x = w) vars_m in
      let has_cov = List.exists (fun (_, s) -> s = `Cov) w_occs in
      let has_contra = List.exists (fun (_, s) -> s = `Contra) w_occs in
      if List.length w_occs <> 2 || not (has_cov && has_contra) then
        failwith ("coend bound variable " ^ w ^ " must occur exactly once covariantly and once contravariantly");
      List.filter (fun (x, _) -> x <> w) vars_m
  | MEnd (cat, w, m) ->
      let delta_ext = (w, cat) :: delta in
      let vars_m = infer_m_type delta_ext m in
      let w_occs = List.filter (fun (x, _) -> x = w) vars_m in
      let has_cov = List.exists (fun (_, s) -> s = `Cov) w_occs in
      let has_contra = List.exists (fun (_, s) -> s = `Contra) w_occs in
      if List.length w_occs <> 2 || not (has_cov && has_contra) then
        failwith ("end bound variable " ^ w ^ " must occur exactly once covariantly and once contravariantly");
      List.filter (fun (x, _) -> x <> w) vars_m
  | MFunc (m1, m2) ->
      flip_vars (infer_m_type delta m1) @ infer_m_type delta m2
  | MApp (f, args) ->
      if List.mem f !active_type_params then (
        if args <> [] then
          failwith ("abstract type " ^ f ^ " cannot have category arguments in this model");
        []
      ) else
        failwith "impossible: unexpanded MApp in infer_m_type"

(* Quadraticality Validator *)
let check_quadraticality (delta : (name * cat) list) (gamma : (name * m_type) list) (target : m_type) : unit =
  let vars_gamma = List.fold_left (fun acc (_, tp) ->
    acc @ flip_vars (infer_m_type delta tp)
  ) [] gamma in
  let vars_target = infer_m_type delta target in
  let all_vars = vars_gamma @ vars_target in
  List.iter (fun (x, _) ->
    let occs = List.filter (fun (var, _) -> var = x) all_vars in
    let cov_count = List.length (List.filter (fun (_, s) -> s = `Cov) occs) in
    let contra_count = List.length (List.filter (fun (_, s) -> s = `Contra) occs) in
    let count = cov_count + contra_count in
    if count = 0 then
      failwith (sprintf "quadraticality check failed for variable '%s': variable does not occur in the sequent" x)
    else if cov_count <> contra_count then
      failwith (sprintf "quadraticality check failed for variable '%s': expected equal number of covariant and contravariant occurrences, but got %d covariant and %d contravariant occurrences (total %d)" x cov_count contra_count count)
  ) delta

let remove_vars gamma used =
  List.filter (fun (x, _) -> not (List.mem x used)) gamma

(* Bidirectional Module Term Type Checker *)
let rec check_m_term (delta : (name * cat) list) (gamma : (name * m_type) list) (e : m_term) (tp : m_type) : name list =
  let tp = expand_m_type tp in
  let gamma = List.map (fun (x, t) -> (x, expand_m_type t)) gamma in
  match e, tp with
  | MTId a, MHom (cat, al, ar) ->
      if gamma <> [] then
        failwith "identity context must be empty (linearity)";
      let (ta, _) = infer_cat_term delta a in
      if ta <> cat then
        failwith "identity category mismatch";
      if al <> a || ar <> a then
        failwith "identity path boundaries must equal the point term";
      []

  | MTJ (m_tp, x_var, y_var, z_var, mz, a, b, f), target_tp ->
      let m_tp = expand_m_type m_tp in
      let (tf, used_f) = infer_m_term delta gamma f in
      (match expand_m_type tf with
       | MHom (cat, af, bf) ->
           if af <> a || bf <> b then
             failwith "J-elim boundaries mismatch";
           let va = match a with CTVar name -> name | _ -> failwith "J-elim source must be variable" in
           let vb = match b with CTVar name -> name | _ -> failwith "J-elim target must be variable" in
           (* Check target type matches m_tp[a/x, b/y] *)
           let expected_target = subst_cat_in_m_type [(x_var, a); (y_var, b)] m_tp in
           if expected_target <> target_tp then
             failwith "J-elim target type mismatch";
           (* check base case mz *)
           let gamma_z = remove_vars gamma used_f in
           let gamma_z' =
             List.map (fun (v, tp) ->
               (v, subst_cat_in_m_type [(va, CTVar z_var); (vb, CTVar z_var)] tp)
             ) gamma_z
           in
           let tp_z = subst_cat_in_m_type [(x_var, CTVar z_var); (y_var, CTVar z_var)] m_tp in
           let used_z = check_m_term ((z_var, cat) :: delta) gamma_z' mz tp_z in
           used_f @ used_z
       | _ -> failwith "J-elim expects path term")

  | MTJCov (m_tp, x_var, m, a, f), target_tp ->
      let m_tp = expand_m_type m_tp in
      let (tf, used_f) = infer_m_term delta gamma f in
      (match expand_m_type tf with
       | MHom (cat, af, x) ->
           if af <> a then
             failwith "J_cov start boundary mismatch";
           let x_name = match x with CTVar name -> name | _ -> failwith "J_cov target must be variable" in
           let expected_target = subst_cat_in_m_type [(x_var, x)] m_tp in
           if expected_target <> target_tp then
             failwith "J_cov target type mismatch";
           let gamma_rem = remove_vars gamma used_f in
           let gamma_rem' =
             List.map (fun (v, tp) ->
               (v, subst_cat_in_m_type [(x_name, a)] tp)
             ) gamma_rem
           in
           let tp_m = subst_cat_in_m_type [(x_var, a)] m_tp in
           let used_m = check_m_term delta gamma_rem' m tp_m in
           used_f @ used_m
       | _ -> failwith "J_cov expects path term")

  | MTJContra (m_tp, x_var, m, b, f), target_tp ->
      let m_tp = expand_m_type m_tp in
      let (tf, used_f) = infer_m_term delta gamma f in
      (match expand_m_type tf with
       | MHom (cat, x, bf) ->
           if bf <> b then
             failwith "J_contra end boundary mismatch";
           let x_name = match x with CTVar name -> name | _ -> failwith "J_contra source must be variable" in
           let expected_target = subst_cat_in_m_type [(x_var, x)] m_tp in
           if expected_target <> target_tp then
             failwith "J_contra target type mismatch";
           let gamma_rem = remove_vars gamma used_f in
           let gamma_rem' =
             List.map (fun (v, tp) ->
               (v, subst_cat_in_m_type [(x_name, b)] tp)
             ) gamma_rem
           in
           let tp_m = subst_cat_in_m_type [(x_var, b)] m_tp in
           let used_m = check_m_term delta gamma_rem' m tp_m in
           used_f @ used_m
       | _ -> failwith "J_contra expects path term")

  | MTTensorIntro (m1, m2), MTensor (tp1, tp2) ->
      let used1 = check_m_term delta gamma m1 tp1 in
      let gamma_rem = remove_vars gamma used1 in
      let used2 = check_m_term delta gamma_rem m2 tp2 in
      used1 @ used2

  | MTTensorElim (x, y, t, c), target_tp ->
      let (tt, used_t) = infer_m_term delta gamma t in
      (match expand_m_type tt with
       | MTensor (tp_x, tp_y) ->
           let gamma_rem = remove_vars gamma used_t in
           let gamma_ext = (x, tp_x) :: (y, tp_y) :: gamma_rem in
           let used_c = check_m_term delta gamma_ext c target_tp in
           if not (List.mem x used_c) || not (List.mem y used_c) then
             failwith "linear tensor elim variables must be used in body";
           let used_c_rem = List.filter (fun v -> v <> x && v <> y) used_c in
           used_t @ used_c_rem
       | _ -> failwith "tensor elim expects tensor term")

  | MTCoendIntro (x, y, z, m), MCoend (cat, w, target_tp) ->
      let tp_m = subst_polarized_m_type `Cov w (CTVar x) (CTVar y) target_tp in
      let gamma' = List.map (fun (v, tp) ->
        (v, subst_polarized_m_type `Contra z (CTVar y) (CTVar x) tp)
      ) gamma in
      let delta_rem = List.filter (fun (var, _) -> var <> z) delta in
      let delta_ext = (x, cat) :: (y, cat) :: delta_rem in
      check_m_term delta_ext gamma' m tp_m

  | MTCoendElim (w, m_var, t, c), target_tp ->
      let (tt, used_t) = infer_m_term delta gamma t in
      (match expand_m_type tt with
       | MCoend (cat, w_bound, tp_t) ->
           let gamma_rem = remove_vars gamma used_t in
           let tp_t' = subst_cat_in_m_type [(w_bound, CTVar w)] tp_t in
           let delta_ext = (w, cat) :: delta in
           let gamma_ext = (m_var, tp_t') :: gamma_rem in
           let used_c = check_m_term delta_ext gamma_ext c target_tp in
           if not (List.mem m_var used_c) then
             failwith "coend elim module variable must be used in body";
           let used_c_rem = List.filter (fun v -> v <> m_var) used_c in
           used_t @ used_c_rem
       | _ -> failwith "coend elim expects coend term")

  | MTEndIntro (w, m), MEnd (cat, w_bound, target_tp) ->
      let delta_ext = (w, cat) :: delta in
      let tp_m = subst_cat_in_m_type [(w_bound, CTVar w)] target_tp in
      check_m_term delta_ext gamma m tp_m

  | MTEndElim (x, y, z, t, c), target_tp ->
      let (tt, used_t) = infer_m_term delta gamma t in
      (match expand_m_type tt with
       | MEnd (cat, w, target_tp_inner) ->
           let w_var = match t with MTVar name -> name | _ -> failwith "end elim expects a variable to eliminate" in
           let tp_m = subst_polarized_m_type `Cov w (CTVar x) (CTVar y) target_tp_inner in
           let gamma_rem = remove_vars gamma used_t in
           let gamma_rem' = List.map (fun (v, tp) ->
             (v, subst_polarized_m_type `Contra z (CTVar y) (CTVar x) tp)
           ) gamma_rem in
           let gamma' = (w_var, tp_m) :: gamma_rem' in
           let delta_rem = List.filter (fun (var, _) -> var <> z) delta in
           let delta_ext = (x, cat) :: (y, cat) :: delta_rem in
           let target_tp' = subst_polarized_m_type `Cov z (CTVar x) (CTVar y) target_tp in
           check_m_term delta_ext gamma' c target_tp'
       | _ -> failwith "end elim expects end term")

  | MTFuncIntro (x, tp_x, body), MFunc (domain, target) ->
      let tp_x = expand_m_type tp_x in
      if tp_x <> domain then
        failwith "function domain type mismatch";
      let used = check_m_term delta ((x, domain) :: gamma) body target in
      if not (List.mem x used) then
        failwith "linear function variable must be used";
      List.filter (fun v -> v <> x) used

  | e, tp ->
      let (inferred_tp, used) = infer_m_term delta gamma e in
      if inferred_tp <> tp then
        failwith "type mismatch in check_m_term";
      used

and infer_m_term (delta : (name * cat) list) (gamma : (name * m_type) list) (e : m_term) : m_type * name list =
  let gamma = List.map (fun (x, t) -> (x, expand_m_type t)) gamma in
  match e with
  | MTVar x ->
      (match List.assoc_opt x gamma with
       | Some tp -> (tp, [x])
       | None -> failwith ("unbound module variable: " ^ x))

  | MTId a ->
      let (cat, _) = infer_cat_term delta a in
      (MHom (cat, a, a), [])

  | MTFuncElim (f, a) ->
      let (tf, used_f) = infer_m_term delta gamma f in
      (match expand_m_type tf with
       | MFunc (domain, target) ->
           let gamma_rem = remove_vars gamma used_f in
           let used_a = check_m_term delta gamma_rem a domain in
           (target, used_f @ used_a)
       | _ -> failwith "application of non-function type")

  | _ -> failwith ("cannot infer type of term: " ^ (let b = Buffer.create 16 in let f = formatter_of_buffer b in pp_m_term f e; pp_print_flush f (); Buffer.contents b))

let check_sequent (delta : (name * cat) list) (gamma : (name * m_type) list) (m : m_term) (tp : m_type) : unit =
  let gamma = List.map (fun (x, t) -> (x, expand_m_type t)) gamma in
  let tp = expand_m_type tp in
  printf "Checking Sequent: %a | %a ⊢ %a : %a\n"
    (pp_list (fun fmt (x, c) -> fprintf fmt "%s:%a" x pp_cat c)) delta
    (pp_list (fun fmt (x, t) -> fprintf fmt "%s:%a" x pp_m_type t)) gamma
    pp_m_term m
    pp_m_type tp;
  
  (* 1. Quadraticality Check on Signature *)
  check_quadraticality delta gamma tp;
  
  (* 2. Linear Module Variable Check *)
  let used = check_m_term delta gamma m tp in
  let expected = List.map fst gamma in
  let rec verify_vars = function
    | [] -> ()
    | x :: xs ->
        if not (List.mem x used) then
          failwith ("module variable " ^ x ^ " was not used in the term (linearity failed)");
        if List.mem x xs then
          failwith ("module variable " ^ x ^ " was used multiple times");
        verify_vars xs
  in
  verify_vars expected;
  if List.length used <> List.length expected then
    failwith "unused module variables exist in the context";
  printf "  => OK! (Valid Sequent)\n\n"

(* Test Suite *)
let tests () =
  let cat_a = CVar "A" in
  
  (* Add a contravariant functor generator f : A^op -> A *)
  cat_fun_sigs := [
    ("f", { arg_types = [(cat_a, `Contra)]; codomain = cat_a })
  ];

  printf "=== Running dirtt Type Checker Tests ===\n\n";

  (* Test 1: Identity Morphism *)
  (* delta = x : A | gamma = . |- id(x) : hom_A(x, x) *)
  let delta1 = [("x", cat_a)] in
  let gamma1 = [] in
  let term1 = MTId (CTVar "x") in
  let type1 = MHom (cat_a, CTVar "x", CTVar "x") in
  (try
     check_sequent delta1 gamma1 term1 type1;
   with Failure msg ->
     printf "  => FAILED: %s\n\n" msg);

  (* Test 2: Morphism Composition *)
  (* x : A, y : A, z : A | f : hom_A(x, y), g : hom_A(y, z) |- J(f, g) : hom_A(x, z) *)
  let delta2 = [("x", cat_a); ("y", cat_a); ("z", cat_a)] in
  let gamma2 = [
    ("f", MHom (cat_a, CTVar "x", CTVar "y"));
    ("g", MHom (cat_a, CTVar "y", CTVar "z"))
  ] in
  (* composition = J(x.y.hom_A(x, y_var), z_var, f; y, z, g) *)
  let comp_term = MTJ (
    MHom (cat_a, CTVar "x", CTVar "y_var"), (* M(x_var, y_var) *)
    "x_var", "y_var", "z_var",
    MTVar "f",
    CTVar "y", CTVar "z", MTVar "g"
  ) in
  let comp_type = MHom (cat_a, CTVar "x", CTVar "z") in
  (try
     check_sequent delta2 gamma2 comp_term comp_type;
   with Failure msg ->
     printf "  => FAILED: %s\n\n" msg);

  (* Test 3: Covariant Yoneda left rule *)
  (* x : A, y : A | m : M(x, y), f : hom_A(y, z) |- J_cov(m, f) : M(x, z) *)
  (* Let M(x, y) = hom_A(x, y) *)
  let delta3 = [("x", cat_a); ("y", cat_a); ("z", cat_a)] in
  let gamma3 = [
    ("m", MHom (cat_a, CTVar "x", CTVar "y"));
    ("f", MHom (cat_a, CTVar "y", CTVar "z"))
  ] in
  let y_term = MTJCov (
    MHom (cat_a, CTVar "x", CTVar "y_var"),
    "y_var",
    MTVar "m",
    CTVar "y",
    MTVar "f"
  ) in
  let y_type = MHom (cat_a, CTVar "x", CTVar "z") in
  (try
     check_sequent delta3 gamma3 y_term y_type;
   with Failure msg ->
     printf "  => FAILED: %s\n\n" msg);

  (* Test 4: Identity on doubled variable *)
  (* x : A | m : hom_A(x, x) |- m : hom_A(x, x) *)
  let delta4 = [("x", cat_a)] in
  let gamma4 = [("m", MHom (cat_a, CTVar "x", CTVar "x"))] in
  let term4 = MTVar "m" in
  let type4 = MHom (cat_a, CTVar "x", CTVar "x") in
  (try
     check_sequent delta4 gamma4 term4 type4;
   with Failure msg ->
     printf "  => FAILED: %s\n\n" msg);

  (* Test 5: Coend Intro/Elim (limits/colimits check) *)
  (* z : A | m : hom_A(x, y) |- mix x y := z in m : ∫^{w:A} hom_A(w, w) *)
  (* Let's verify coend type validation *)
  let delta5 = [("z", cat_a)] in
  let gamma5 = [("m", MHom (cat_a, CTVar "z", CTVar "z"))] in
  let coend_type = MCoend (cat_a, "w", MHom (cat_a, CTVar "w", CTVar "w")) in
  let coend_term = MTCoendIntro ("x", "y", "z", MTVar "m") in
  (try
     check_sequent delta5 gamma5 coend_term coend_type;
   with Failure msg ->
     printf "  => FAILED: %s\n\n" msg);

  (* Test 6: Quadraticality Violation *)
  (* x : A, y : A | m : hom_A(x, x) |- m : hom_A(x, y) (Invalid because occurrences are unequal) *)
  let delta6 = [("x", cat_a); ("y", cat_a)] in
  let gamma6 = [("m", MHom (cat_a, CTVar "x", CTVar "x"))] in
  let term6 = MTVar "m" in
  let type6 = MHom (cat_a, CTVar "x", CTVar "y") in
  (try
     check_sequent delta6 gamma6 term6 type6;
     printf "  => ERROR: expected quadraticality failure, but check succeeded!\n\n"
   with Failure msg ->
     printf "  => Success! (Caught expected failure: %s)\n\n" msg)

let rec infer_categories_in_cat_term (expected_cat : cat) (t : cat_term) : (name * cat) list =
  match t with
  | CTVar x -> [(x, expected_cat)]
  | CTFun (f, args) ->
      (match List.assoc_opt f !cat_fun_sigs with
       | Some sig_f ->
           List.concat (List.map2 (fun arg (expected_arg_cat, _) ->
             infer_categories_in_cat_term expected_arg_cat arg
           ) args sig_f.arg_types)
       | None -> [])
  | CTOp a -> infer_categories_in_cat_term (op_cat expected_cat) a

let rec infer_categories_in_m_type (tp : m_type) : (name * cat) list =
  match tp with
  | MHom (cat, a, b) ->
      infer_categories_in_cat_term cat a @ infer_categories_in_cat_term cat b
  | MTensor (m1, m2) ->
      infer_categories_in_m_type m1 @ infer_categories_in_m_type m2
  | MCoend (cat, w, m) ->
      (w, cat) :: infer_categories_in_m_type m
  | MEnd (cat, w, m) ->
      (w, cat) :: infer_categories_in_m_type m
  | MFunc (m1, m2) ->
      infer_categories_in_m_type m1 @ infer_categories_in_m_type m2
  | MApp (f, args) ->
      if List.mem f !active_type_params then []
      else (match List.assoc_opt f !type_defs with
       | Some (params, body) ->
           let substs = List.combine params args in
           infer_categories_in_m_type (subst_cat_in_m_type substs body)
       | None -> [])

let infer_categories_from_type (tp : m_type) : (name * cat) list =
  let raw = infer_categories_in_m_type tp in
  let rec unique acc = function
    | [] -> List.rev acc
    | (x, c) :: rest ->
        if List.mem_assoc x acc then
          let c' = List.assoc x acc in
          if c <> c' then
            failwith ("category conflict for variable " ^ x)
          else
            unique acc rest
        else
          unique ((x, c) :: acc) rest
  in
  unique [] raw


let () = tests ()

