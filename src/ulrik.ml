(* Clean Educational Minimal STT Kernel *)

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

let var x = EVar x
let univ = EUniv

(* hom(x, y) := {f : 𝕀 → A | f0 = x, f1 = y} *)

let hom (a : exp) (x : exp) (y : exp) : exp =
    EExt ((EPi (EIDir, ("t", a))),
          (EShapeInc ((EVar "∂𝕀"), (EIDir))),           (* placeholder for boundary inclusion *)
          (ESystem [(EZeroDir, x); (EOneDir, y)]))

(* isContr(A) *)

let is_contr (a : exp) : exp =
  ESig (a, ("c",
    EPi (a, ("x", EId (a, var "c", var "x")))))

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
  | ESystem list    ->  let (a,b) = List.hd list in fprintf fmt "[ %a | %a ] " pp_exp a pp_exp b;
                        List.iter (fun (a, b) -> fprintf fmt "[ %a | %a ]" pp_exp a pp_exp b ) (List.tl list);

and pp_exp_paren fmt e =
  match e with
  | EApp _ | EModalApp _ | EFst _ | ESnd _ -> fprintf fmt "(%a)" pp_exp e
  | _ -> pp_exp fmt e

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
  List.iter (fun (name, term) -> printf "%-20s: %a\n" name pp_exp term ) examples

let () = tests ()
