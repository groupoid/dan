(* Dan Operational Syntax *)
type superscript = S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8 | S9 | SN of string
type type_name = Simplex | Group | Simplicial | Chain | Category | Monoid | Ring | Field

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

type constrain =
  | Eq of term * term
  | Map of string * string list

type hypothesis =
  | Decl of string list * type_name   (* e.g., (a b c : Simplex) *)
  | Equality of string * term * term  (* e.g., ac = ab ∘ bc *)
  | Mapping of string * term * term   (* e.g., ∂₁ = C₂ < C₃ *)

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
  | s -> failwith ("unknown type name: " ^ s)

let rec string_of_term = function
  | Id s -> s
  | Comp (t1, t2) -> string_of_term t1 ^ " ∘ " ^ string_of_term t2
  | Inv t -> string_of_term t ^ "^-1"
  | Pow (t, s) ->
      let s_str = match s with
        | S1 -> "¹" | S2 -> "²" | S3 -> "³" | S4 -> "⁴" | S5 -> "⁵"
        | S6 -> "⁶" | S7 -> "⁷" | S8 -> "⁸" | S9 -> "⁹" | SN str -> str
      in
      string_of_term t ^ s_str
  | E -> "e"
  | Matrix _ -> "matrix"
  | Add (t1, t2) -> string_of_term t1 ^ " + " ^ string_of_term t2
  | Mul (t1, t2) -> string_of_term t1 ^ " * " ^ string_of_term t2
  | Div (t1, t2) -> string_of_term t1 ^ " / " ^ string_of_term t2
