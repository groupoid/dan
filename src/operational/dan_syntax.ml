(* Dan Operational Syntax *)
type superscript = S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8 | S9 | SN of string | Sn of int
type dimension = Dim of int | DimVar of string

type type_name =
  | Simplex | Group | Simplicial | Chain | Category | Monoid | Ring | Field
  | PermGroup | MatGroup | FpGroup | PcGroup | Module | Set | GSet

type term =
  | Id of string
  | Comp of term * term
  | Inv of term
  | Pow of term * superscript
  | E
  | Matrix of int list list
  | Add of term * term
  | Mul of term * term
  | Div of term * term
  | Conj of term * term
  | Comm of term * term
  | PowInt of term * int
  | Perm of int list
  | Cycle of int list list
  | PermGroup of term list
  | MatGroup of term list * int * int
  | FpGroup of string list * term list
  | PcGroup of string list * term list
  | Scalar of int
  | Face of superscript * term
  | Deg of superscript * term
  | Boundary of term
  | Act of term * term
  | Hom of term * term
  | RelEq of term * term

type constrain =
  | Eq of term * term
  | Map of string * string list
  | Neq of term * term
  | In of term * term
  | Order of term * int
  | Rel of term list

type hypothesis =
  | Decl of string list * type_name   (* e.g., (a b c : Simplex) *)
  | Equality of string * term * term  (* e.g., ac = ab ∘ bc *)
  | Mapping of string * term * term   (* e.g., ∂₁ = C₂ < C₃ *)
  | Presentation of string * term
  | Relation of term
  | Action of string * term * term
  | Orbit of term * term * term list
  | Stabilizer of term * term * term

type rank = Finite of int | Infinite

type rank_spec = {
  spec_rank : rank;
  spec_elements : string list;
  spec_faces : string list;
  spec_constraints : constrain list;
}

type type_def = {
  name : string;
  typ : type_name;
  context : hypothesis list;
  specs : rank_spec list;
}

type cmd =
  | CImport of string
  | CDef of type_def

let parse_type_name = function
  | "Simplex" -> Simplex
  | "Group" -> Group
  | "Simplicial" -> Simplicial
  | "Chain" -> Chain
  | "Category" -> Category
  | "Monoid" -> Monoid
  | "Ring" -> Ring
  | "Field" -> Field
  | "PermGroup" -> PermGroup
  | "MatGroup" -> MatGroup
  | "FpGroup" -> FpGroup
  | "PcGroup" -> PcGroup
  | "Module" -> Module
  | "Set" -> Set
  | "GSet" -> GSet
  | s -> failwith ("unknown type name: " ^ s)

let rec string_of_term = function
  | Id s -> s
  | Comp (t1, t2) -> string_of_term t1 ^ " ∘ " ^ string_of_term t2
  | Inv t -> string_of_term t ^ "⁻¹"
  | Pow (t, s) ->
      let s_str = match s with
        | S1 -> "¹" | S2 -> "²" | S3 -> "³" | S4 -> "⁴" | S5 -> "⁵"
        | S6 -> "⁶" | S7 -> "⁷" | S8 -> "⁸" | S9 -> "⁹" | SN str -> str | Sn n -> string_of_int n
      in
      string_of_term t ^ s_str
  | E -> "e"
  | Matrix _ -> "matrix"
  | Add (t1, t2) -> string_of_term t1 ^ " + " ^ string_of_term t2
  | Mul (t1, t2) -> string_of_term t1 ^ " * " ^ string_of_term t2
  | Div (t1, t2) -> string_of_term t1 ^ " / " ^ string_of_term t2
  | Conj (t1, t2) -> string_of_term t1 ^ "^" ^ string_of_term t2
  | Comm (t1, t2) -> "[" ^ string_of_term t1 ^ ", " ^ string_of_term t2 ^ "]"
  | PowInt (t, n) -> string_of_term t ^ "^" ^ string_of_int n
  | Perm l -> "Perm(" ^ String.concat "," (List.map string_of_int l) ^ ")"
  | Cycle l -> String.concat "" (List.map (fun c -> "(" ^ String.concat "," (List.map string_of_int c) ^ ")") l)
  | PermGroup l -> "PermGroup(" ^ String.concat "," (List.map string_of_term l) ^ ")"
  | MatGroup (l, q, n) -> "MatGroup(" ^ String.concat "," (List.map string_of_term l) ^ ", " ^ string_of_int q ^ ", " ^ string_of_int n ^ ")"
  | FpGroup (gens, rels) -> "FpGroup<" ^ String.concat " " gens ^ " | " ^ String.concat "," (List.map string_of_term rels) ^ ">"
  | PcGroup (gens, rels) -> "PcGroup<" ^ String.concat " " gens ^ " | " ^ String.concat "," (List.map string_of_term rels) ^ ">"
  | Scalar n -> string_of_int n
  | Face (s, t) ->
      let s_str = match s with S1 -> "1" | S2 -> "2" | S3 -> "3" | S4 -> "4" | S5 -> "5" | S6 -> "6" | S7 -> "7" | S8 -> "8" | S9 -> "9" | SN str -> str | Sn n -> string_of_int n in
      "d_" ^ s_str ^ "(" ^ string_of_term t ^ ")"
  | Deg (s, t) ->
      let s_str = match s with S1 -> "1" | S2 -> "2" | S3 -> "3" | S4 -> "4" | S5 -> "5" | S6 -> "6" | S7 -> "7" | S8 -> "8" | S9 -> "9" | SN str -> str | Sn n -> string_of_int n in
      "s_" ^ s_str ^ "(" ^ string_of_term t ^ ")"
  | Boundary t -> "∂(" ^ string_of_term t ^ ")"
  | Act (t1, t2) -> string_of_term t1 ^ " · " ^ string_of_term t2
  | Hom (t1, t2) -> "Hom(" ^ string_of_term t1 ^ ", " ^ string_of_term t2 ^ ")"
  | RelEq (t1, t2) -> string_of_term t1 ^ " = " ^ string_of_term t2
