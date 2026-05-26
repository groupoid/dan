type name = string
type sign = [ `Cov | `Contra ]

type expr =

  (* Common *)
  | EVar of name
  | EApp of expr * expr
  | ELam of (name * expr option) * expr
  | EPi of expr * (name * expr)
  | ESig of expr * (name * expr)
  | EPair of expr * expr
  | EFst of expr
  | ESnd of expr

  (* Simplicial Core *)
  | EUniv                                   (* U *)
  | EId of expr * expr * expr               (* strict Id *)
  | ERef of expr                            (* refl *)
  | EIDir                                   (* directed interval 𝕀 *)
  | EZeroDir                                (* 0 *)
  | EOneDir                                 (* 1 *)
  | ELeq of expr * expr                     (* i ≤ j *)
  | EShapeInc of expr * expr                (* φ ⊆ ψ *)
  | EExt of expr * expr * expr              (* {x : A |^φ f} *)
  | ESystem of (expr * expr) list           (* [ φ | f ] ... *)
  | EModalPi of expr * (name * expr)        (* μ(x:A). B(x) *)
  | EModalLam of (name * expr) * expr        (* λ^μ(x:A). body *)
  | EModalApp of expr * expr                (* f @ φ *)
  | ETw of expr                             (* A^tw *)
  | EOp of expr                             (* category opposite *)
  | ETwPi0 of expr                          (* π₀(x) *)
  | ETwPi1 of expr                          (* π₁(x) *)
  | EJoin of expr * expr                    (* i ∨ j *)
  | EMeet of expr * expr                    (* i ∧ j *)
  | ENeg of expr                            (* ¬i *)

  (* Dirtt compatibility / direct AST *)
  | EHom of expr * expr * expr                                  (* hom(cat, a, b) *)
  | ETensor of expr * expr                                      (* M * N or M ⊗ N *)
  | EFunc of expr * expr                                        (* M -> N or M ⊸ N *)
  | ECoend of expr * name * expr                                (* coend(x:cat). M *)
  | EEnd of expr * name * expr                                  (* end(x:cat). M *)
  | EIdTerm of expr                                             (* id(a) *)
  | EJ of expr * name * name * name * expr * expr * expr * expr (* J *)
  | EJCov of expr * name * expr * expr * expr                   (* J_cov *)
  | EJContra of expr * name * expr * expr * expr                (* J_contra *)
  | ETensorElim of name * name * expr * expr                    (* let x * y := t in c *)
  | ECoendIntro of name * name * name * expr                    (* mix x y := z in m *)
  | ECoendElim of name * name * expr * expr                     (* let <x, y> := t in c *)
  | EEndElim of name * name * name * expr * expr                (* let x y @ z := t in c *)

type cmd =
  | CModule of string
  | CImport of string
  | CFunctor of name * (expr * sign) list * expr
  | CDef of name * name list * expr option * expr
  | CCheck of (name * expr) list * (name * expr) list * expr * expr  (* dirtt check *)
  | CCheckSimplicial of (name * expr) list * expr * expr             (* simplicial check *)
