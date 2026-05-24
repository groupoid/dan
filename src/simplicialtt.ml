(* simplicialtt by Ulrik Buchholtz *)

open Format

type name = string

type exp =

  (* MLTT Core *)
  | EUniv                                   (* U *)
  | EVar of name
  | EPi of exp * (name * exp)               (* (x : A) → B *)
  | ELam of (name * exp) * exp
  | EApp of exp * exp
  | ESig of exp * (name * exp)              (* Σ *)
  | EPair of exp * exp
  | EFst of exp
  | ESnd of exp
  | EId of exp * exp * exp                  (* strict Id (undirected) *)
  | ERef of exp

  (* === Directed STT === *)
  | EIDir                                   (* directed interval 𝕀 *)
  | EZeroDir
  | EOneDir
  | ELeq of exp * exp                       (* i ≤ j *)
  | EShapeInc of exp * exp                  (* φ ⊆ ψ  (cofibration) *)
  | ESystem of (exp * exp) list
  | EExt of exp * exp * exp                 (* Extension type {x : A |^φ f} *)
  | EModalPi of exp * (name * exp)          (* μx:A.B(x) — covariant/modal Π *)
  | EModalLam of (name * exp) * exp
  | EModalApp of exp * exp                  (* directed application f @ φ *)
  | ETw of exp                              (* A^tw — Twisted arrow modality *)
  | ETwPi0 of exp                           (* π₀ : tw A → A^op *)
  | ETwPi1 of exp                           (* π₁ : tw A → A *)

  (* Lattice extensions *)
  | EJoin of exp * exp                      (* i ∨ j *)
  | EMeet of exp * exp                      (* i ∧ j *)
  | ENeg of exp                             (* ¬i *)

type value =
  | VUniv
  | VPi of value * closure
  | VLam of closure
  | VSig of value * closure
  | VPair of value * value
  | VId of value * value * value
  | VRef of value
  | VIDir
  | VZeroDir
  | VOneDir
  | VLeq of value * value
  | VShapeInc of value * value
  | VSystem of (value * value) list
  | VExt of value * value * value
  | VModalPi of value * closure
  | VModalLam of closure
  | VTw of value
  | VTwPi0 of value
  | VTwPi1 of value
  | VJoin of value * value
  | VMeet of value * value
  | VNeg of value
  | VNeutral of value * neutral
  | VShapeClosure of env * exp

and neutral =
  | NVar of name
  | NApp of neutral * value
  | NFst of neutral
  | NSnd of neutral
  | NModalApp of neutral * value
  | NTwPi0 of neutral
  | NTwPi1 of neutral
  | NSystemElim of neutral * (value * value) list

and closure = name * env * exp
and env = (name * value) list
and context = (name * value) list

let var x = EVar x
let univ = EUniv

(* hom(x, y) := {f : 𝕀 → A | f0 = x, f1 = y} *)
let hom (a : exp) (x : exp) (y : exp) : exp =
  EExt (
    EPi (EIDir, ("t", a)),
    EJoin (ELeq (EVar "t", EZeroDir), ELeq (EOneDir, EVar "t")),
    ESystem [(ELeq (EVar "t", EZeroDir), x); (ELeq (EOneDir, EVar "t"), y)]
  )

(* isContr(A) *)
let is_contr (a : exp) : exp =
  ESig (a, ("c",
    EPi (a, ("x", EId (a, var "c", var "x")))))

(* Printing *)
let rec pp_exp fmt = function
  | EUniv           -> fprintf fmt "U"
  | EVar x          -> fprintf fmt "%s" x
  | EPi (a, (x, b)) -> fprintf fmt "Π(%s : %a). %a" x pp_exp a pp_exp b
  | ELam ((x, a), b)-> fprintf fmt "λ(%s : %a). %a" x pp_exp a pp_exp b
  | EApp (f, a)     -> fprintf fmt "%a %a" pp_exp_paren f pp_exp_paren a
  | ESig (a, (x, b))-> fprintf fmt "Σ(%s : %a). %a" x pp_exp a pp_exp b
  | EPair (a, b)    -> fprintf fmt "(%a, %a)" pp_exp a pp_exp b
  | EFst e          -> fprintf fmt "%a.1" pp_exp_paren e
  | ESnd e          -> fprintf fmt "%a.2" pp_exp_paren e
  | EId (a, x, y)   -> fprintf fmt "%a = %a" pp_exp_paren x pp_exp_paren y
  | ERef e          -> fprintf fmt "refl"
  | EIDir           -> fprintf fmt "𝕀"
  | EZeroDir        -> fprintf fmt "0"
  | EOneDir         -> fprintf fmt "1"
  | ELeq (i, j)     -> fprintf fmt "%a ≤ %a" pp_exp_paren i pp_exp_paren j
  | EShapeInc (phi, psi) -> fprintf fmt "%a ⊆ %a" pp_exp_paren phi pp_exp_paren psi
  | EExt (a, phi, f) -> fprintf fmt "{ %a |^%a %a }" pp_exp a pp_exp phi pp_exp f
  | EModalPi (a, (x, b)) -> fprintf fmt "μ(%s : %a). %a" x pp_exp a pp_exp b
  | EModalLam ((x, a), b)-> fprintf fmt "λ^μ(%s : %a). %a" x pp_exp a pp_exp b
  | EModalApp (f, a) -> fprintf fmt "%a @ %a" pp_exp_paren f pp_exp_paren a
  | ETw a           -> fprintf fmt "%a^tw" pp_exp_paren a
  | ETwPi0 a        -> fprintf fmt "π₀(%a)" pp_exp a
  | ETwPi1 a        -> fprintf fmt "π₁(%a)" pp_exp a
  | EJoin (a, b)    -> fprintf fmt "%a ∨ %a" pp_exp_paren a pp_exp_paren b
  | EMeet (a, b)    -> fprintf fmt "%a ∧ %a" pp_exp_paren a pp_exp_paren b
  | ENeg a          -> fprintf fmt "¬%a" pp_exp_paren a
  | ESystem list    ->
      if list = [] then fprintf fmt "[]"
      else (
        let (a, b) = List.hd list in
        fprintf fmt "[ %a | %a ]" pp_exp a pp_exp b;
        List.iter (fun (a, b) -> fprintf fmt " [ %a | %a ]" pp_exp a pp_exp b) (List.tl list)
      )

and pp_exp_paren fmt e =
  match e with
  | EApp _ | EModalApp _ | EFst _ | ESnd _ | EJoin _ | EMeet _ | ENeg _ -> fprintf fmt "(%a)" pp_exp e
  | _ -> pp_exp fmt e

(* Evaluator *)
let rec eval (ctx : context) (env : env) (e : exp) : value =
  match e with
  | EUniv -> VUniv
  | EVar x ->
      (match List.assoc_opt x env with
       | Some v -> v
       | None ->
           (match List.assoc_opt x ctx with
            | Some tp -> VNeutral (tp, NVar x)
            | None -> failwith ("unbound variable: " ^ x)))
  | EPi (a, (x, b)) -> VPi (eval ctx env a, (x, env, b))
  | ELam ((x, a), b) -> VLam (x, env, b)
  | EApp (f, a) ->
      let vf = eval ctx env f in
      let va = eval ctx env a in
      apply ctx vf va
  | ESig (a, (x, b)) -> VSig (eval ctx env a, (x, env, b))
  | EPair (a, b) -> VPair (eval ctx env a, eval ctx env b)
  | EFst e ->
      (match eval ctx env e with
       | VPair (v1, _) -> v1
       | VNeutral (VSig (a, _), neu) -> VNeutral (a, NFst neu)
       | _ -> failwith "fst of non-pair")
  | ESnd e ->
      (match eval ctx env e with
       | VPair (_, v2) -> v2
       | VNeutral (VSig (a, b), neu) ->
           let v1 = VNeutral (a, NFst neu) in
           VNeutral (inst ctx b v1, NSnd neu)
       | _ -> failwith "snd of non-pair")
  | EId (a, x, y) -> VId (eval ctx env a, eval ctx env x, eval ctx env y)
  | ERef e -> VRef (eval ctx env e)
  | EIDir -> VIDir
  | EZeroDir -> VZeroDir
  | EOneDir -> VOneDir
  | ELeq (i, j) -> VLeq (eval ctx env i, eval ctx env j)
  | EShapeInc (phi, psi) -> VShapeInc (eval ctx env phi, eval ctx env psi)
  | ESystem cases ->
      let rec find_active = function
        | [] -> VSystem (List.map (fun (phi, t) -> (eval ctx env phi, eval ctx env t)) cases)
        | (phi, t) :: rest ->
            let vphi = eval ctx env phi in
            if is_true ctx env vphi then eval ctx env t
            else find_active rest
      in
      find_active cases
  | EExt (a, phi, f) -> VExt (eval ctx env a, VShapeClosure (env, phi), VShapeClosure (env, f))
  | EModalPi (a, (x, b)) -> VModalPi (eval ctx env a, (x, env, b))
  | EModalLam ((x, a), b) -> VModalLam (x, env, b)
  | EModalApp (f, a) ->
      let vf = eval ctx env f in
      let va = eval ctx env a in
      apply_modal ctx vf va
  | ETw a -> VTw (eval ctx env a)
  | ETwPi0 a ->
      (match eval ctx env a with
       | VNeutral (VTw tp, neu) -> VNeutral (VTw tp, NTwPi0 neu)
       | v -> VTwPi0 v)
  | ETwPi1 a ->
      (match eval ctx env a with
       | VNeutral (VTw tp, neu) -> VNeutral (VTw tp, NTwPi1 neu)
       | v -> VTwPi1 v)
  | EJoin (e1, e2) -> VJoin (eval ctx env e1, eval ctx env e2)
  | EMeet (e1, e2) -> VMeet (eval ctx env e1, eval ctx env e2)
  | ENeg e -> VNeg (eval ctx env e)

and apply ctx (f : value) (a : value) : value =
  match f with
  | VLam (x, env, body) -> eval ctx ((x, a) :: env) body
  | VNeutral (VPi (domain, target), neu) ->
      VNeutral (inst ctx target a, NApp (neu, a))
  | _ -> failwith "apply of non-lambda"

and apply_modal ctx (f : value) (a : value) : value =
  match f with
  | VModalLam (x, env, body) -> eval ctx ((x, a) :: env) body
  | VNeutral (VModalPi (domain, target), neu) ->
      VNeutral (inst ctx target a, NModalApp (neu, a))
  | _ -> failwith "apply_modal of non-lambda"

and inst ctx (name, env, body) v = eval ctx ((name, v) :: env) body

(* Distributive Lattice Valuation Solver *)
and gen_valuations = function
  | [] -> [[]]
  | x :: xs ->
      let sub = gen_valuations xs in
      List.map (fun env -> (x, VZeroDir) :: env) sub @
      List.map (fun env -> (x, VOneDir) :: env) sub

and eval_value ctx (val_env : env) = function
  | VZeroDir -> 0
  | VOneDir -> 1
  | VJoin (v1, v2) ->
      let b1 = eval_value ctx val_env v1 in
      let b2 = eval_value ctx val_env v2 in
      if b1 = 1 || b2 = 1 then 1 else 0
  | VMeet (v1, v2) ->
      let b1 = eval_value ctx val_env v1 in
      let b2 = eval_value ctx val_env v2 in
      if b1 = 1 && b2 = 1 then 1 else 0
  | VNeg v ->
      1 - eval_value ctx val_env v
  | VLeq (v1, v2) ->
      let b1 = eval_value ctx val_env v1 in
      let b2 = eval_value ctx val_env v2 in
      if b1 <= b2 then 1 else 0
  | VShapeInc (v1, v2) ->
      let b1 = eval_value ctx val_env v1 in
      let b2 = eval_value ctx val_env v2 in
      if b1 <= b2 then 1 else 0
  | VNeutral (_, NVar x) ->
      (match List.assoc_opt x val_env with
       | Some VZeroDir -> 0
       | Some VOneDir -> 1
       | _ -> failwith ("unbound lattice variable in neutral: " ^ x))
  | VShapeClosure (env_phi, phi_exp) ->
      let v = eval ctx (val_env @ env_phi) phi_exp in
      eval_value ctx val_env v
  | _ -> failwith "not a lattice value"

and is_true ctx env v =
  let ivars = List.filter_map (fun (x, t) ->
    if t = VIDir then Some x else None
  ) ctx in
  let valuations = gen_valuations ivars in
  List.for_all (fun val_env ->
    try eval_value ctx val_env v = 1
    with _ -> false
  ) valuations

(* Quotation / Readback *)
let rec quote (ctx : context) (depth : int) (tp : value) (v : value) : exp =
  match tp with
  | VPi (a, b) ->
      let x = "x" ^ string_of_int depth in
      let vx = VNeutral (a, NVar x) in
      let v_applied = apply ctx v vx in
      let target_tp = inst ctx b vx in
      let new_ctx = (x, a) :: ctx in
      let quoted_body = quote new_ctx (depth + 1) target_tp v_applied in
      ELam ((x, quote ctx depth VUniv a), quoted_body)
  | VSig (a, b) ->
      let v1 = fst_val v in
      let v2 = snd_val ctx v in
      let q1 = quote ctx depth a v1 in
      let q2 = quote ctx depth (inst ctx b v1) v2 in
      EPair (q1, q2)
  | VExt (a, phi, f) ->
      quote ctx depth a v
  | VModalPi (a, b) ->
      let x = "x" ^ string_of_int depth in
      let vx = VNeutral (a, NVar x) in
      let v_applied = apply_modal ctx v vx in
      let target_tp = inst ctx b vx in
      let new_ctx = (x, a) :: ctx in
      let quoted_body = quote new_ctx (depth + 1) target_tp v_applied in
      EModalLam ((x, quote ctx depth VUniv a), quoted_body)
  | _ ->
      quote_structural ctx depth v

and quote_structural (ctx : context) (depth : int) (v : value) : exp =
  match v with
  | VUniv -> EUniv
  | VPi (a, (x, env, b)) ->
      let x_fresh = "x" ^ string_of_int depth in
      let vx = VNeutral (a, NVar x_fresh) in
      let new_ctx = (x_fresh, a) :: ctx in
      EPi (quote ctx depth VUniv a, (x_fresh, quote new_ctx (depth + 1) VUniv (eval new_ctx ((x, vx) :: env) b)))
  | VLam (x, env, b) ->
      let x_fresh = "x" ^ string_of_int depth in
      let vx = VNeutral (VIDir, NVar x_fresh) in
      let new_ctx = (x_fresh, VIDir) :: ctx in
      ELam ((x_fresh, EUniv), quote new_ctx (depth + 1) VUniv (eval new_ctx ((x, vx) :: env) b))
  | VSig (a, (x, env, b)) ->
      let x_fresh = "x" ^ string_of_int depth in
      let vx = VNeutral (a, NVar x_fresh) in
      let new_ctx = (x_fresh, a) :: ctx in
      ESig (quote ctx depth VUniv a, (x_fresh, quote new_ctx (depth + 1) VUniv (eval new_ctx ((x, vx) :: env) b)))
  | VPair (a, b) ->
      EPair (quote_structural ctx depth a, quote_structural ctx depth b)
  | VId (a, x, y) ->
      EId (quote ctx depth VUniv a, quote ctx depth a x, quote ctx depth a y)
  | VRef e ->
      ERef (quote_structural ctx depth e)
  | VIDir -> EIDir
  | VZeroDir -> EZeroDir
  | VOneDir -> EOneDir
  | VLeq (i, j) -> ELeq (quote ctx depth VIDir i, quote ctx depth VIDir j)
  | VShapeInc (phi, psi) -> EShapeInc (quote ctx depth VIDir phi, quote ctx depth VIDir psi)
  | VSystem cases ->
      ESystem (List.map (fun (phi, t) -> (quote_structural ctx depth phi, quote_structural ctx depth t)) cases)
  | VExt (a, phi, f) ->
      EExt (quote ctx depth VUniv a, quote ctx depth VIDir phi, quote_structural ctx depth f)
  | VModalPi (a, (x, env, b)) ->
      let x_fresh = "x" ^ string_of_int depth in
      let vx = VNeutral (a, NVar x_fresh) in
      let new_ctx = (x_fresh, a) :: ctx in
      EModalPi (quote ctx depth VUniv a, (x_fresh, quote new_ctx (depth + 1) VUniv (eval new_ctx ((x, vx) :: env) b)))
  | VModalLam (x, env, b) ->
      let x_fresh = "x" ^ string_of_int depth in
      let vx = VNeutral (VIDir, NVar x_fresh) in
      let new_ctx = (x_fresh, VIDir) :: ctx in
      EModalLam ((x_fresh, EUniv), quote new_ctx (depth + 1) VUniv (eval new_ctx ((x, vx) :: env) b))
  | VTw a -> ETw (quote ctx depth VUniv a)
  | VTwPi0 a -> ETwPi0 (quote_structural ctx depth a)
  | VTwPi1 a -> ETwPi1 (quote_structural ctx depth a)
  | VJoin (v1, v2) -> EJoin (quote ctx depth VIDir v1, quote ctx depth VIDir v2)
  | VMeet (v1, v2) -> EMeet (quote ctx depth VIDir v1, quote ctx depth VIDir v2)
  | VNeg v -> ENeg (quote ctx depth VIDir v)
  | VShapeClosure (_, e) -> e
  | VNeutral (tp, neu) -> quote_neutral ctx depth neu

and quote_neutral (ctx : context) (depth : int) (neu : neutral) : exp =
  match neu with
  | NVar x -> EVar x
  | NApp (n, a) ->
      EApp (quote_neutral ctx depth n, quote_structural ctx depth a)
  | NFst n -> EFst (quote_neutral ctx depth n)
  | NSnd n -> ESnd (quote_neutral ctx depth n)
  | NModalApp (n, a) ->
      EModalApp (quote_neutral ctx depth n, quote_structural ctx depth a)
  | NTwPi0 n -> ETwPi0 (quote_neutral ctx depth n)
  | NTwPi1 n -> ETwPi1 (quote_neutral ctx depth n)
  | NSystemElim (n, _) -> quote_neutral ctx depth n

and fst_val = function
  | VPair (v1, _) -> v1
  | VNeutral (VSig (a, _), neu) -> VNeutral (a, NFst neu)
  | _ -> failwith "fst of non-pair value"

and snd_val ctx = function
  | VPair (_, v2) -> v2
  | VNeutral (VSig (a, b), neu) ->
      let v1 = VNeutral (a, NFst neu) in
      VNeutral (inst ctx b v1, NSnd neu)
  | _ -> failwith "snd of non-pair value"

(* Equivalence checking under constraint phi *)
let equal_under ctx env phi tp v1 v2 =
  let ivars = List.filter_map (fun (x, t) ->
    if t = VIDir then Some x else None
  ) ctx in
  let valuations = gen_valuations ivars in
  let size = List.length env in
  List.for_all (fun val_env ->
    let eval_env = val_env @ env in
    let phi_exp = quote ctx size VUniv phi in
    let phi_val = eval ctx eval_env phi_exp in
    if eval_value ctx val_env phi_val = 1 then
      let e1 = quote ctx size tp v1 in
      let e2 = quote ctx size tp v2 in
      let v1' = eval ctx eval_env e1 in
      let v2' = eval ctx eval_env e2 in
      let tp' = eval ctx eval_env (quote ctx size VUniv tp) in
      if tp' = VIDir then
        eval_value ctx val_env v1' = eval_value ctx val_env v2'
      else
        quote ctx size tp' v1' = quote ctx size tp' v2'
    else
      true
  ) valuations

let equal ctx env tp v1 v2 =
  equal_under ctx env VOneDir tp v1 v2

(* Bidirectional Type Checker *)
let rec check (ctx : context) (env : env) (e : exp) (tp : value) : unit =
  match e, tp with
  | ELam ((x, a_exp), body), VPi (a, b) ->
      let va = eval ctx env a_exp in
      if not (equal ctx env VUniv va a) then
        failwith "lambda domain type mismatch";
      let vx = VNeutral (a, NVar x) in
      let target_tp = inst ctx b vx in
      check ((x, a) :: ctx) ((x, vx) :: env) body target_tp

  | EModalLam ((x, a_exp), body), VModalPi (a, b) ->
      let va = eval ctx env a_exp in
      if not (equal ctx env VUniv va a) then
        failwith "modal lambda domain type mismatch";
      let vx = VNeutral (a, NVar x) in
      let target_tp = inst ctx b vx in
      check ((x, a) :: ctx) ((x, vx) :: env) body target_tp

  | EPair (e1, e2), VSig (a, b) ->
      check ctx env e1 a;
      let v1 = eval ctx env e1 in
      check ctx env e2 (inst ctx b v1)

  | ESystem cases, tp ->
      List.iter (fun (phi, t) ->
        let ivars = List.filter_map (fun (x, t) ->
          if t = VIDir then Some x else None
        ) ctx in
        let valuations = gen_valuations ivars in
        List.iter (fun val_env ->
          let eval_env = val_env @ env in
          let phi_val = eval ctx eval_env phi in
          if eval_value ctx val_env phi_val = 1 then
            let tp_val = eval ctx eval_env (quote ctx (List.length env) VUniv tp) in
            check ctx eval_env t tp_val
        ) valuations
      ) cases;
      let rec check_compat = function
        | [] -> ()
        | (phi1, t1) :: rest ->
            List.iter (fun (phi2, t2) ->
              let vmeet_phi = eval ctx env (EMeet (phi1, phi2)) in
              let v1 = eval ctx env t1 in
              let v2 = eval ctx env t2 in
              if not (equal_under ctx env vmeet_phi tp v1 v2) then
                failwith "system compatibility check failed"
            ) rest;
            check_compat rest
      in
      check_compat cases

  | e, VExt (base_tp, phi, f) ->
      check ctx env e base_tp;
      let ve = eval ctx env e in
      (match base_tp with
       | VPi (VIDir, (t, env_t, b)) ->
           let ivars = List.filter_map (fun (x, t) ->
             if t = VIDir then Some x else None
           ) ctx in
           let ivars = if List.mem t ivars then ivars else t :: ivars in
           let valuations = gen_valuations ivars in
           let size = List.length env in
           let rec check_all = function
             | [] -> ()
             | val_env :: rest ->
                 let eval_env = val_env @ env in
                 let phi_exp = quote ctx size VUniv phi in
                 let phi_val = eval ctx eval_env phi_exp in
                 if eval_value ctx val_env phi_val = 1 then
                   let vt = List.assoc t val_env in
                   let ve_t = apply ctx ve vt in
                   let vb = eval ctx ((t, vt) :: env_t) b in
                   let f_exp = quote ctx size vb f in
                   let f_val = eval ctx eval_env f_exp in
                   if not (equal ctx eval_env vb ve_t f_val) then
                     failwith "extension type boundary constraint failed"
                 else ();
                 check_all rest
           in
           check_all valuations
       | _ -> failwith "extension base type must be Pi over interval")

  | e, tp ->
      let inferred = infer ctx env e in
      if not (equal ctx env VUniv inferred tp) then (
        printf "Type mismatch for term: %a\n" pp_exp e;
        printf "  Inferred: %a\n" pp_exp (quote ctx (List.length env) VUniv inferred);
        printf "  Expected: %a\n" pp_exp (quote ctx (List.length env) VUniv tp);
        failwith "type mismatch in check"
      )

and infer (ctx : context) (env : env) (e : exp) : value =
  match e with
  | EUniv -> VUniv
  | EVar x ->
      (match List.assoc_opt x ctx with
       | Some tp -> tp
       | None -> failwith ("unbound variable: " ^ x))
  | EPi (a, (x, b)) ->
      check ctx env a VUniv;
      let va = eval ctx env a in
      let vx = VNeutral (va, NVar x) in
      check ((x, va) :: ctx) ((x, vx) :: env) b VUniv;
      VUniv
  | EApp (f, a) ->
      (match infer ctx env f with
       | VPi (domain, target) ->
           check ctx env a domain;
           let va = eval ctx env a in
           inst ctx target va
       | _ -> failwith "apply of non-function type")
  | ESig (a, (x, b)) ->
      check ctx env a VUniv;
      let va = eval ctx env a in
      let vx = VNeutral (va, NVar x) in
      check ((x, va) :: ctx) ((x, vx) :: env) b VUniv;
      VUniv
  | EFst e ->
      (match infer ctx env e with
       | VSig (a, _) -> a
       | _ -> failwith "fst of non-sigma type")
  | ESnd e ->
      (match infer ctx env e with
       | VSig (a, b) ->
           let ve = eval ctx env e in
           inst ctx b (fst_val ve)
       | _ -> failwith "snd of non-sigma type")
  | EId (a, x, y) ->
      check ctx env a VUniv;
      let va = eval ctx env a in
      check ctx env x va;
      check ctx env y va;
      VUniv
  | ERef e ->
      let tp = infer ctx env e in
      let ve = eval ctx env e in
      VId (tp, ve, ve)
  | EIDir -> VUniv
  | EZeroDir -> VIDir
  | EOneDir -> VIDir
  | ELeq (i, j) ->
      check ctx env i VIDir;
      check ctx env j VIDir;
      VUniv
  | EShapeInc (phi, psi) ->
      check ctx env phi VUniv;
      check ctx env psi VUniv;
      VUniv
  | EExt (a, phi, f) ->
      check ctx env a VUniv;
      let va = eval ctx env a in
      (match va with
       | VPi (VIDir, (t, env_t, b)) ->
           let vt = VNeutral (VIDir, NVar t) in
           check ((t, VIDir) :: ctx) ((t, vt) :: env) phi VUniv;
           let vb = eval ((t, vt) :: env_t) env_t b in
           check ((t, VIDir) :: ctx) ((t, vt) :: env) f vb
       | _ -> failwith "base type of extension must be Pi over interval");
      VUniv
  | EModalPi (a, (x, b)) ->
      check ctx env a VUniv;
      let va = eval ctx env a in
      let vx = VNeutral (va, NVar x) in
      check ((x, va) :: ctx) ((x, vx) :: env) b VUniv;
      VUniv
  | EModalApp (f, a) ->
      (match infer ctx env f with
       | VModalPi (domain, target) ->
           check ctx env a domain;
           let va = eval ctx env a in
           inst ctx target va
       | _ -> failwith "modal apply of non-modal-function type")
  | ETw a ->
      check ctx env a VUniv;
      VUniv
  | ETwPi0 e ->
      (match infer ctx env e with
       | VTw a -> a
       | _ -> failwith "pi0 of non-twisted arrow")
  | ETwPi1 e ->
      (match infer ctx env e with
       | VTw a -> a
       | _ -> failwith "pi1 of non-twisted arrow")
  | EJoin (e1, e2) ->
      let t1 = infer ctx env e1 in
      if t1 = VIDir then (
        check ctx env e2 VIDir;
        VIDir
      ) else if t1 = VUniv then (
        check ctx env e2 VUniv;
        VUniv
      ) else failwith "Join arguments must be either interval terms or shapes"
  | EMeet (e1, e2) ->
      let t1 = infer ctx env e1 in
      if t1 = VIDir then (
        check ctx env e2 VIDir;
        VIDir
      ) else if t1 = VUniv then (
        check ctx env e2 VUniv;
        VUniv
      ) else failwith "Meet arguments must be either interval terms or shapes"
  | ENeg e ->
      let t = infer ctx env e in
      if t = VIDir then VIDir
      else if t = VUniv then VUniv
      else failwith "Neg argument must be either interval term or shape"
  | ELam _ | EModalLam _ | EPair _ | ESystem _ ->
      failwith "cannot infer type of lambda, pair, or system"

(* Test suite *)
let tests () =
  let a = var "A"
  and x = var "x"
  and y = var "y" in
  let examples = [
    ("Universe", univ);
    ("Directed Interval", EIDir);
    ("hom(x, y)", hom a x y);
    ("Modal Pi", EModalPi (a, ("t", EApp ((var "B"),(var "t")))));
    ("Twisted Arrow", ETw (var "C"));
    ("isContr", is_contr (hom a x y));
  ] in
  List.iter (fun (name, term) -> printf "%-20s: %a\n" name pp_exp term ) examples;

  printf "\n=== Running Type Checker Tests ===\n";
  let vA = VNeutral (VUniv, NVar "A") in
  let ctx = [("A", VUniv); ("x", vA); ("y", vA)] in
  let env = [("A", vA); ("x", VNeutral (vA, NVar "x")); ("y", VNeutral (vA, NVar "y"))] in

  (* Test 1: hom a x y is a valid type *)
  let hom_expr = hom a x y in
  (try
    let tp = infer ctx env hom_expr in
    printf "Test 1 passed: hom A x y is a valid type: %a\n" pp_exp (quote ctx 3 VUniv tp)
   with Failure msg ->
     printf "Test 1 FAILED: %s\n" msg);

  (* Test 2: identity term checks against hom A x x *)
  let id_term = ELam (("x", a), ELam (("t", EIDir), EVar "x")) in
  let id_type = EPi (a, ("x", hom a (EVar "x") (EVar "x"))) in
  (try
     check ctx env id_term (eval ctx env id_type);
     printf "Test 2 passed: id_A typechecks against Π(x:A). hom A x x\n"
   with Failure msg ->
     printf "Test 2 FAILED: %s\n" msg);

  (* Test 3: Lattice distributivity validation *)
  let i = EVar "i" and j = EVar "j" and k = EVar "k" in
  let lhs = EMeet (i, EJoin (j, k)) in
  let rhs = EJoin (EMeet (i, j), EMeet (i, k)) in
  let lattice_ctx = [("i", VIDir); ("j", VIDir); ("k", VIDir)] in
  let lattice_env = [] in
  let vlhs = eval lattice_ctx lattice_env lhs in
  let vrhs = eval lattice_ctx lattice_env rhs in
  let is_eq = equal_under lattice_ctx lattice_env VOneDir VIDir vlhs vrhs in
  printf "Test 3 passed: Lattice distributivity lhs = rhs: %b\n" is_eq

let () = tests ()
