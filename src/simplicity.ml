(* Groupoid Infinity Simplicity HoTT as Rezk/GAP replacement

   $ ocamlopt -o simplicity simplicity.ml

   Copyright (c) 2025 Groupoid Infinity

   STATUS: early bird prototype (achieved 20 rewrites)
*)


type superscript = S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8 | S9
type type_name = Simplex | Group | Simplicial | Chain | Category | Monoid | Ring | Field

type term =
  | Id of string
  | Comp of term * term
  | Inv of term
  | Pow of term * superscript
  | E
  | Matrix of int list list
  | Add of term * term  (* r₁ + r₂ *)
  | Mul of term * term  (* r₁ ⋅ r₂ *)
  | Div of term * term  (* r₁ / r₂ *)

type constrain =
  | Eq of term * term
  | Map of string * string list

type hypothesis =
  | Decl of string list * type_name   (* e.g., (a b c : Simplex) *)
  | Equality of string * term * term  (* e.g., ac = ab ∘ bc *)
  | Mapping of string * term * term   (* e.g., ∂₁ = C₂ < C₃ *)

type rank = Finite of int | Infinite  (* Updated to support ∞ *)

type type_def = {
  name : string;
  typ : type_name;
  context : hypothesis list;
  rank : rank;                  (* <n> *)
  elements : string list;       (* <elements> *)
  faces : string list option;   (* Optional: only for Simplex *)
  constraints : constrain list  (* <constraints> *)
}

(* Parsing helpers *)
let parse_superscript = function
  | "¹" -> S1 | "²" -> S2 | "³" -> S3 | "⁴" -> S4 | "⁵" -> S5
  | "⁶" -> S6 | "⁷" -> S7 | "⁸" -> S8 | "⁹" -> S9 | _ -> failwith "Invalid superscript"

let parse_n s = match s with
  | "∞" -> Infinite
  | n -> Finite (int_of_string n)

let check_str s = 
  try int_of_string s |> ignore; true
  with Failure _ -> false

let rec check_term defn env t allowed_types =
  match t with
  | Id id -> 
        if (check_str id) then () else
        if not (Hashtbl.mem env id) then failwith ("Undeclared term: " ^ id)
  | Comp (t1, t2) -> check_term defn env t1 allowed_types; check_term defn env t2 allowed_types
  | Inv t -> check_term defn env t allowed_types
  | Pow (t, _) -> check_term defn env t allowed_types
  | E -> ()
  | Matrix m ->
      if not (List.mem defn.typ allowed_types) then failwith "Matrix only allowed in Group, Monoid, Ring, Category, Field"
      else List.iter (fun row -> List.iter (fun _ -> ()) row) m
  | Add (t1, t2) | Mul (t1, t2) ->
      if not (List.mem defn.typ [Ring; Field]) then failwith "Add/Mul only allowed in Ring, Field"
      else check_term defn env t1 allowed_types; check_term defn env t2 allowed_types
  | Div (t1, t2) ->
      if defn.typ <> Field then failwith "Div only allowed in Field"
      else check_term defn env t1 allowed_types; check_term defn env t2 allowed_types;
           if t2 = E then failwith "Division by zero"

let check_type_def defn =
  let env = Hashtbl.create 10 in

  (* Context check *)
  List.iter (fun h ->
    match h with
    | Decl (ids, typ) -> List.iter (fun id -> if Hashtbl.mem env id then failwith ("Duplicate: " ^ id) else Hashtbl.add env id typ) ids
    | Equality (id, t1, t2) ->
        check_term defn env t1 [Group; Monoid; Ring; Category; Field];
        check_term defn env t2 [Group; Monoid; Ring; Category; Field];
        Hashtbl.add env id Simplex
    | Mapping (id, t1, t2) -> Hashtbl.add env id Simplex
  ) defn.context;

  List.iter (fun el -> if not (Hashtbl.mem env el) then failwith ("Undeclared element: " ^ el)) defn.elements;

  (* Face control *)
  (match defn.faces with
   | Some faces -> List.iter (fun f -> if not (Hashtbl.mem env f) then failwith ("Undeclared face: " ^ f)) faces
   | None -> ());

  (* Check validity *)
  List.iter (fun c ->
    match c with
    | Eq (t1, t2) -> check_term defn env t1 [Group; Monoid; Ring; Category; Field]; check_term defn env t2 [Group; Monoid; Ring; Category; Field]
    | Map (id1, ids2) ->
        if not (Hashtbl.mem env id1) then failwith ("Undeclared map source: " ^ id1);
        List.iter (fun id2 -> if not (Hashtbl.mem env id2) then failwith ("Undeclared map target: " ^ id2)) ids2
  ) defn.constraints;

  (* Rank checking *)
  (match defn.typ, defn.rank with
  | Ring, Finite n -> if n < 0 then failwith "Ring rank must be non-negative"
  | Ring, Infinite -> failwith "Ring rank cannot be infinite"
  | Field, Finite n -> if n < 0 then failwith "Field rank must be non-negative"
  | Field, Infinite -> failwith "Field rank cannot be infinite"
  | Group, Finite n | Monoid, Finite n -> if List.length defn.elements <> n then failwith "Group/Monoid rank mismatch (n = generator count)"
  | Group, Infinite | Monoid, Infinite -> failwith "Group/Monoid cannot have infinite rank"
  | Simplicial, Finite n | Chain, Finite n | Category, Finite n -> if n < 0 then failwith "Simplicial/Chain/Category rank must be non-negative"
  | Simplicial, Infinite | Chain, Infinite | Category, Infinite -> ()
  | Simplex, Infinite -> failwith "Simplex cannot have infinite rank (use Simplicial)"
  | Simplex, Finite n -> if List.length defn.elements <> n + 1 then failwith "Simplex rank mismatch (elements)";
                         (match defn.faces with | Some faces -> if List.length faces <> n + 1 then failwith "Simplex rank mismatch (faces)"
                                                | None -> failwith "Simplex requires faces"));

  Printf.printf "Type %s checked successfully\n" defn.name

let singular_cone = {
  name = "singular_cone";
  typ = Simplex;
  context = [
    Decl (["p"; "q"; "r"; "s"; "qrs"; "prs"; "pqs"; "pqr"], Simplex);
    Equality ("pqr_comp", Comp (Id "pqs", Id "qrs"), Id "pqr")
  ];
  rank = Finite 3;
  elements = ["p"; "q"; "r"; "s"];
  faces = Some ["qrs"; "prs"; "pqs"; "pqr"];
  constraints = [Eq (Comp (Id "pqs", Id "qrs"), Id "pqr")]
}

let mobius = {
  name = "Möbius";
  typ = Simplex;
  context = [
    Decl (["a"; "b"; "c"], Simplex);
    Decl (["ab"; "bc"; "ac"], Simplex);
    Equality ("ab", Comp (Id "bc", Id "ac"), Id "ab")
  ];
  rank = Finite 2;
  elements = ["a"; "b"; "c"];
  faces = Some ["bc"; "ac"; "ab"];
  constraints = [Eq (Id "ab", Comp (Id "bc", Id "ac"))]
}

let degen_tetra = {
  name = "degen_tetra";
  typ = Simplex;
  context = [
    Decl (["p"; "q"; "r"; "s"], Simplex);
    Equality ("q", Id "r", Id "q");
    Decl (["pqr"; "qrs"; "prs"; "pqs"], Simplex);
    Equality ("pqr", Comp (Id "pqs", Id "qrs"), Id "pqr")
  ];
  rank = Finite 3;
  elements = ["p"; "q"; "r"; "s"];
  faces = Some ["qrs"; "prs"; "pqs"; "pqr"];
  constraints = [Eq (Id "pqr", Comp (Id "pqs", Id "qrs"))]
}

let twisted_annulus_1 = {
  name = "twisted_annulus_1";
  typ = Simplex;
  context = [
    Decl (["a"; "b"; "c"; "d"], Simplex);
    Decl (["cd"; "ab"; "bc"; "ac"; "bd"], Simplex);
    Equality ("ab", Comp (Id "bc", Id "ac"), Id "ab");
    Equality ("cd", Comp (Id "ac", Id "bd"), Id "cd")
  ];
  rank = Finite 2;
  elements = ["a"; "b"; "c"];
  faces = Some ["bc"; "ac"; "ab"];
  constraints = [Eq (Id "ab", Comp (Id "bc", Id "ac"))]
}

let twisted_annulus_2 = {
  name = "twisted_annulus_2";
  typ = Simplex;
  context = [
    Decl (["a"; "b"; "c"; "d"], Simplex);
    Decl (["cd"; "ab"; "bc"; "ac"; "bd"], Simplex);
    Equality ("ab", Comp (Id "bc", Id "ac"), Id "ab");
    Equality ("cd", Comp (Id "ac", Id "bd"), Id "cd")
  ];
  rank = Finite 2;
  elements = ["b"; "c"; "d"];
  faces = Some ["bc"; "bd"; "cd"];
  constraints = [Eq (Id "cd", Comp (Id "ac", Id "bd"))]
}

let degen_triangle = {
  name = "degen_triangle";
  typ = Simplex;
  context = [
    Decl (["a"; "b"; "c"], Simplex);
    Equality ("b", Id "c", Id "b");
    Decl (["ab"; "bc"; "ac"], Simplex);
    Equality ("ab", Comp (Id "bc", Id "ac"), Id "ab")
  ];
  rank = Finite 2;
  elements = ["a"; "b"; "c"];
  faces = Some ["bc"; "ac"; "ab"];
  constraints = [Eq (Id "ab", Comp (Id "bc", Id "ac"))]
}

let singular_prism = {
  name = "singular_prism";
  typ = Simplex;
  context = [
    Decl (["p"; "q"; "r"; "s"; "t"], Simplex);
    Decl (["pqr"; "qrs"; "prs"; "pqt"], Simplex);
    Equality ("qrs", Id "qrs", Id "qrs");
    Equality ("pqr", Comp (Id "pqt", Id "qrs"), Id "pqr")
  ];
  rank = Finite 3;
  elements = ["p"; "q"; "r"; "s"];
  faces = Some ["qrs"; "prs"; "pqt"; "pqr"];
  constraints = [Eq (Id "pqr", Comp (Id "pqt", Id "qrs"))]
}

let path_z2_category = {
  name = "path_z2_category";
  typ = Category;
  context = [
    Decl (["x"; "y"], Simplex);
    Decl (["f"; "g"; "h"], Simplex);
    Decl (["e"; "a"], Simplex);
    Equality ("a2", Pow (Id "a", S2), Id "e");
    Equality ("h", Comp (Id "f", Id "g"), Id "h")
  ];
  rank = Finite 2;  (* 2 objects: x, y *)
  elements = ["x"; "y"];
  faces = None;  (* No faces for Category *)
  constraints = [Eq (Id "h", Comp (Id "f", Id "g"))]
}

let nat_monoid = {
  name = "nat_monoid";
  typ = Monoid;
  context = [
    Decl (["z"; "s"], Simplex);
    Equality ("sz", Comp (Id "s", Id "z"), Id "s");
    Equality ("zs", Comp (Id "z", Id "s"), Id "s")
  ];
  rank = Finite 2;  (* 2 generators: z, s *)
  elements = ["z"; "s"];
  faces = None;  (* No faces for Monoid *)
  constraints = [
    Eq (Id "sz", Comp (Id "s", Id "z"));
    Eq (Id "zs", Comp (Id "z", Id "s"))
  ]
}

let triangle_chain = {
  name = "triangle_chain";
  typ = Chain;
  context = [
    Decl (["v0"; "v1"; "v2"; "e01"; "e02"; "e12"; "t"; "∂₁₀"; "∂₁₁"; "∂₁₂"; "∂₂"], Simplex);
    Equality ("∂₁₀", Id "e01", Id "∂₁₀");
    Equality ("∂₁₁", Id "e02", Id "∂₁₁");
    Equality ("∂₁₂", Id "e12", Id "∂₁₂");
    Equality ("∂₂", Id "t", Id "∂₂")
  ];
  rank = Finite 2;  (* Chain length: 0 -> 1 -> 2 *)
  elements = ["v0"; "v1"; "v2"; "e01"; "e02"; "e12"; "t"];
  faces = None;  (* No faces for Chain *)
  constraints = [
    Eq (Id "∂₁₀", Id "e01");
    Eq (Id "∂₁₁", Id "e02");
    Eq (Id "∂₁₂", Id "e12");
    Map ("∂₂", ["e01"; "e02"; "e12"])
  ]
}

let circle = {
  name = "circle";
  typ = Simplicial;
  context = [
    Decl (["v"; "e"; "∂₁₀"; "∂₁₁"; "s₀"], Simplex);
    Equality ("∂₁₀", Id "v", Id "∂₁₀");
    Equality ("∂₁₁", Id "v", Id "∂₁₁");
    Equality ("s₀", Id "e", Id "s₀")
  ];
  rank = Finite 1;  (* Max dimension: 1 *)
  elements = ["v"; "e"];
  faces = None;  (* No faces for Simplicial *)
  constraints = [
    Eq (Id "∂₁₀", Id "v");
    Eq (Id "∂₁₁", Id "v");
    Map ("s₀", ["v"])
  ]
}

let z3 = {
  name = "z3";
  typ = Group;
  context = [
    Decl (["e"; "a"], Simplex);
    Equality ("a3", Pow (Id "a", S3), Id "e")
  ];
  rank = Finite 1;  (* 1 generator: a *)
  elements = ["a"];
  faces = None;  (* No faces for Group *)
  constraints = [Eq (Id "a3", Pow (Id "a", S3))]
}

let s1_infty = {
  name = "s1_infty";
  typ = Simplicial;
  context = [
    Decl (["v"; "e"; "∂₁₀"; "∂₁₁"; "∂₂₀"; "s₀"; "s₁₀"], Simplex);
    Equality ("∂₁₀", Id "v", Id "∂₁₀");
    Equality ("∂₁₁", Id "v", Id "∂₁₁");
    Equality ("s₀", Id "e", Id "s₀");
    Equality ("∂₂₀", Comp (Id "e", Id "e"), Id "∂₂₀");
    Equality ("s₁₀", Id "∂₂₀", Id "s₁₀")
  ];
  rank = Infinite;  (* Unbounded dimensions *)
  elements = ["v"; "e"; "∂₂₀"];
  faces = None;  (* No faces for Simplicial *)
  constraints = [
    Eq (Id "∂₁₀", Id "v");
    Eq (Id "∂₁₁", Id "v");
    Map ("s₀", ["v"]);
    Eq (Id "∂₂₀", Comp (Id "e", Id "e"));
    Map ("s₁₀", ["∂₂₀"])
  ]
}

let cube_infty = {
  name = "cube_infty";
  typ = Category;
  context = [
    Decl (["a"; "b"; "c"], Simplex);
    Decl (["f"; "g"; "h"], Simplex);
    Decl (["cube2"; "cube3"], Simplex);
    Equality ("cube2", Comp (Id "g", Id "f"), Id "h");
    Equality ("cube3", Comp (Id "cube2", Id "f"), Id "cube3");
  ];
  rank = Infinite; 
  elements = ["a"; "b"; "c"];
  faces = Some ["cube2"; "cube3"];
  constraints = [
    Eq (Id "cube2", Comp (Id "g", Id "f"));
    Eq (Id "cube3", Comp (Id "cube2", Id "f"))
  ]
}

let integer_ring = {
  name = "integer_ring";
  typ = Ring;
  context = [
    Decl (["x"; "y"; "s"; "p"], Simplex);
    Equality ("x_val", Id "x", Id "2");
    Equality ("y_val", Id "y", Id "3");
    Equality ("s_val", Id "s", Id "5");
    Equality ("p_val", Id "p", Id "6")
  ];
  rank = Finite 4;
  elements = ["x"; "y"; "s"; "p"];
  faces = None;
  constraints = [
    Eq (Add (Id "x", Id "y"), Id "s");
    Eq (Mul (Id "x", Id "y"), Id "p");
    Eq (Id "x", Id "2");
    Eq (Id "y", Id "3");
    Eq (Id "s", Id "5");
    Eq (Id "p", Id "6")
  ]
}

let poly_ring_zx = {
  name = "poly_ring_zx";
  typ = Ring;
  context = [
    Decl (["f"; "g"; "s"; "p"; "x"; "1"; "2"; "3"], Simplex);
    Equality ("f_val", Id "f", Add (Id "x", Id "1"));
    Equality ("g_val", Id "g", Mul (Id "2", Id "x"));
    Equality ("s_val", Id "s", Add (Mul (Id "3", Id "x"), Id "1"));
    Equality ("p_val", Id "p", Add (Mul (Id "2", Mul (Id "x", Id "x")), Mul (Id "2", Id "x")))
  ];
  rank = Finite 8;
  elements = ["f"; "g"; "s"; "p"; "x"; "1"; "2"; "3"];
  faces = None;
  constraints = [
    Eq (Add (Id "f", Id "g"), Id "s");
    Eq (Mul (Id "f", Id "g"), Id "p");
    Eq (Id "f", Add (Id "x", Id "1"));
    Eq (Id "g", Mul (Id "2", Id "x"));
    Eq (Id "s", Add (Mul (Id "3", Id "x"), Id "1"));
    Eq (Id "p", Add (Mul (Id "2", Mul (Id "x", Id "x")), Mul (Id "2", Id "x")))
  ]
}

let matrix_ring_spectrum = {
  name = "matrix_ring_spectrum";
  typ = Ring;
  context = [
    Decl (["a"; "b"; "s"; "p"], Simplex);
    Equality ("a_val", Id "a", Matrix [[1;2];[3;4]]);
    Equality ("b_val", Id "b", Matrix [[0;1];[1;0]]);
    Equality ("s_val", Id "s", Matrix [[1;3];[4;4]]);
    Equality ("p_val", Id "p", Matrix [[2;1];[4;3]])
  ];
  rank = Finite 4;
  elements = ["a"; "b"; "s"; "p"];
  faces = None;
  constraints = [
    Eq (Add (Id "a", Id "b"), Id "s");
    Eq (Mul (Id "a", Id "b"), Id "p");
    Eq (Id "a", Matrix [[1;2];[3;4]]);
    Eq (Id "b", Matrix [[0;1];[1;0]]);
    Eq (Id "s", Matrix [[1;3];[4;4]]);
    Eq (Id "p", Matrix [[2;1];[4;3]])
  ]
}

let hz_spectrum = {
  name = "hz_spectrum";
  typ = Ring;
  context = [
    Decl (["x"; "y"; "p"], Simplex);
    Equality ("x_val", Id "x", Id "2");
    Equality ("y_val", Id "y", Id "3");
    Equality ("p_val", Id "p", Id "6")
  ];
  rank = Finite 3;
  elements = ["x"; "y"; "p"];
  faces = None;
  constraints = [
    Eq (Mul (Id "x", Id "y"), Id "p");
    Eq (Id "x", Id "2");
    Eq (Id "y", Id "3");
    Eq (Id "p", Id "6")
  ]
}

let examples = [
    singular_cone; mobius; degen_tetra; twisted_annulus_1; twisted_annulus_2;
    degen_triangle; singular_prism; path_z2_category; nat_monoid;
    triangle_chain; circle; z3; s1_infty; cube_infty; 
    integer_ring; poly_ring_zx; matrix_ring_spectrum; hz_spectrum
]


let () = List.iter check_type_def examples
