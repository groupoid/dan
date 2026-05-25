type universe = U0 | U1

type expr =
  | Univ of universe
  | Var of string
  | Pi of string * expr * expr
  | Sigma of string * expr * expr
  | Id of expr * expr * expr

  | Lam of string * expr * expr
  | App of expr * expr
  | Pair of expr * expr
  | Fst of expr
  | Snd of expr
  | Refl of expr

  | Category
  | AbelianStructure of expr
  | Complex of expr * expr
  | ComplexMorphism of expr * expr * expr * expr
  | QuasiIso of expr * expr * expr * expr * expr
  | DerivedCategory of expr * expr
  | Shift of expr * expr * expr * int

  | CategoryIntro of { ob : expr; hom : expr; compose : expr; id : expr }
  | ComplexIntro of { obj : expr; diff : expr }
  | MorIntro of expr

(* Контекст *)
type context = (string * expr) list

(* Виняток для помилок *)
exception TypeError of string

(* Перевірка рівності типів *)
let rec equal_ty ty1 ty2 = ty1 = ty2

(* Пошук змінної в контексті *)
let lookup ctx x =
  try List.assoc x ctx
  with Not_found -> raise (TypeError ("Variable not found: " ^ x))

(* Підстановка в типах *)
let rec subst_ty ty x t =
  match ty with
  | Univ u -> Univ u
  | Pi (y, a, b) -> Pi (y, subst_ty a x t, if y = x then b else subst_ty b x t)
  | Sigma (y, a, b) -> Sigma (y, subst_ty a x t, if y = x then b else subst_ty b x t)
  | Id (a, t1, t2) -> Id (subst_ty a x t, subst_term t1 x t, subst_term t2 x t)
  | Category -> Category
  | AbelianStructure c -> AbelianStructure (subst_ty c x t)
  | Complex (c, a) -> Complex (subst_ty c x t, subst_ty a x t)
  | ComplexMorphism (c, a, x', y) -> ComplexMorphism (subst_ty c x t, subst_ty a x t, subst_ty x' x t, subst_ty y x t)
  | QuasiIso (c, a, x', y, f) -> QuasiIso (subst_ty c x t, subst_ty a x t, subst_ty x' x t, subst_ty y x t, subst_term f x t)
  | DerivedCategory (c, a) -> DerivedCategory (subst_ty c x t, subst_ty a x t)
  | Shift (c, a, x', n) -> Shift (subst_ty c x t, subst_ty a x t, subst_ty x' x t, n)
  | _ -> ty

(* Підстановка в термах *)
and subst_term t x v =
  match t with
  | Var y -> if y = x then v else t
  | Lam (y, a, t') -> Lam (y, subst_ty a x v, if y = x then t' else subst_term t' x v)
  | App (t1, t2) -> App (subst_term t1 x v, subst_term t2 x v)
  | Pair (t1, t2) -> Pair (subst_term t1 x v, subst_term t2 x v)
  | Fst t' -> Fst (subst_term t' x v)
  | Snd t' -> Snd (subst_term t' x v)
  | Refl t' -> Refl (subst_term t' x v)
  | CategoryIntro { ob; hom; compose; id } ->
      CategoryIntro { ob = subst_ty ob x v; hom = subst_ty hom x v;
                      compose = subst_term compose x v; id = subst_term id x v }
  | ComplexIntro { obj; diff } ->
      ComplexIntro { obj = subst_term obj x v; diff = subst_term diff x v }
  | MorIntro f -> MorIntro (subst_term f x v)
  | _ -> t

(* Заглушка для рівності термів *)
let equal_term _ctx t1 t2 = t1 = t2

(* Заглушка для Hom *)
let hom_of _c = Univ U0

(* Перевірка типу *)
let rec check (ctx : context) (t : expr) (ty : expr) : unit =
  match t, ty with
  | Var x, ty' ->
      let ty_x = lookup ctx x in
      if not (equal_ty ty_x ty') then
        raise (TypeError ("Type mismatch for " ^ x))
  | Lam (x, a, t), Pi (x', a', b) when equal_ty a a' ->
      let ctx' = (x, a) :: ctx in
      check ctx' t b
  | App (t1, t2), b ->
      let a = infer ctx t2 in
      (match infer ctx t1 with
       | Pi (x, a', b') when equal_ty a a' -> check ctx t2 a
       | _ -> raise (TypeError "Expected Pi type for application"))
  | Pair (t1, t2), Sigma (x, a, b) ->
      check ctx t1 a;
      check ctx t2 (subst_ty b x t1)
  | Fst t, a ->
      (match infer ctx t with
       | Sigma (x, a', _) when equal_ty a a' -> ()
       | _ -> raise (TypeError "Expected Sigma type for fst"))
  | Snd t, b ->
      (match infer ctx t with
       | Sigma (x, _, b') -> check ctx t (Sigma (x, infer ctx (Fst t), b'))
       | _ -> raise (TypeError "Expected Sigma type for snd"))
  | Refl t', Id (a, t1, t2) ->
      check ctx t' a;
      if not (equal_term ctx t1 t2) then
        raise (TypeError "Terms in Id type must be equal")
  | CategoryIntro { ob; hom; compose; id }, Category ->
      check ctx compose (Pi ("A", ob, Pi ("B", ob, Pi ("C", ob,
        Pi ("f", hom, Pi ("g", hom, hom))))))
  | ComplexIntro { obj; diff }, Complex (c, a) ->
      check ctx obj (Pi ("n", Univ U0, Univ U0));
      check ctx diff (Pi ("n", Univ U0, hom_of c))
  | MorIntro f, ComplexMorphism (c, a, x, y) ->
      check ctx f (Pi ("n", Univ U0, hom_of c))
  | _ -> raise (TypeError ("Type mismatch: " ^ string_of_expr t ^ " vs " ^ string_of_expr ty))

(* Виведення типу *)
and infer (ctx : context) (t : expr) : expr =
  match t with
  | Var x -> lookup ctx x
  | Lam (x, a, t) ->
      let b = infer ((x, a) :: ctx) t in
      Pi (x, a, b)
  | App (t1, t2) ->
      (match infer ctx t1 with
       | Pi (x, a, b) ->
           check ctx t2 a;
           subst_ty b x t2
       | _ -> raise (TypeError "Expected Pi type for application"))
  | Pair (t1, t2) ->
      let a = infer ctx t1 in
      let b = infer ctx t2 in
      Sigma ("_", a, b)
  | Fst t ->
      (match infer ctx t with
       | Sigma (x, a, _) -> a
       | _ -> raise (TypeError "Expected Sigma type for fst"))
  | Snd t ->
      (match infer ctx t with
       | Sigma (x, a, b) -> subst_ty b x (Fst t)
       | _ -> raise (TypeError "Expected Sigma type for snd"))
  | Refl t' ->
      let a = infer ctx t' in
      Id (a, t', t')
  | CategoryIntro _ -> Category
  | ComplexIntro { obj; diff } ->
      let c = Univ U0 in
      let a = Univ U0 in
      Complex (c, a)
  | MorIntro f -> ComplexMorphism (Univ U0, Univ U0, Univ U0, Univ U0)
  | _ -> raise (TypeError "Cannot infer type")

(* Допоміжна функція для виведення рядка *)
and string_of_expr = function
  | Var x -> x
  | Univ U0 -> "U0"
  | Univ U1 -> "U1"
  | Pi (x, a, b) -> "Pi(" ^ x ^ " : " ^ string_of_expr a ^ ", " ^ string_of_expr b ^ ")"
  | Sigma (x, a, b) -> "Sigma(" ^ x ^ " : " ^ string_of_expr a ^ ", " ^ string_of_expr b ^ ")"
  | Id (a, t1, t2) -> "Id(" ^ string_of_expr a ^ ", " ^ string_of_expr t1 ^ ", " ^ string_of_expr t2 ^ ")"
  | Category -> "Category"
  | _ -> "<complex expr>"

(* Теорема 1: Композиція квазіізоморфізмів *)
let theorem_quasi_iso_compose =
  let ctx = [
    ("C", Category);
    ("A", AbelianStructure (Var "C"));
    ("X", Complex (Var "C", Var "A"));
    ("Y", Complex (Var "C", Var "A"));
    ("Z", Complex (Var "C", Var "A"));
    ("f", ComplexMorphism (Var "C", Var "A", Var "X", Var "Y"));
    ("qf", QuasiIso (Var "C", Var "A", Var "X", Var "Y", Var "f"));
    ("g", ComplexMorphism (Var "C", Var "A", Var "Y", Var "Z"));
    ("qg", QuasiIso (Var "C", Var "A", Var "Y", Var "Z", Var "g"));
    ("compose", Pi ("A", Complex (Var "C", Var "A"), 
                   Pi ("B", Complex (Var "C", Var "A"),
                   Pi ("C", Complex (Var "C", Var "A"),
                   Pi ("f", ComplexMorphism (Var "C", Var "A", Var "A", Var "B"),
                   Pi ("g", ComplexMorphism (Var "C", Var "A", Var "B", Var "C"),
                   ComplexMorphism (Var "C", Var "A", Var "A", Var "C")))))))
  ] in
  let compose_term = App (App (App (App (App (Var "compose", Var "X"), Var "Y"), Var "Z"), Var "f"), Var "g") in
  let ty = QuasiIso (Var "C", Var "A", Var "X", Var "Z", compose_term) in
  try
    check ctx compose_term ty;  (* Перевіряємо, що compose_term є квазіізоморфізмом *)
    print_endline "Quasi-iso composition theorem typechecks OK"
  with TypeError msg -> Printf.printf "Type error in Quasi-iso theorem: %s\n" msg

(* Теорема 2: Існування трикутника *)
let theorem_triangle =
  let ctx = [
    ("C", Category);
    ("A", AbelianStructure (Var "C"));
    ("X", DerivedCategory (Var "C", Var "A"));
    ("Y", DerivedCategory (Var "C", Var "A"));
    ("Z", DerivedCategory (Var "C", Var "A"));
    ("f", ComplexMorphism (Var "C", Var "A", Var "X", Var "Y"));
    ("g", ComplexMorphism (Var "C", Var "A", Var "Y", Var "Z"));
    ("w", ComplexMorphism (Var "C", Var "A", Var "Z", Shift (Var "C", Var "A", Var "X", 1)))
  ] in
  let t = Pair (Var "Z", Pair (Var "g", Var "w")) in
  let ty = Sigma ("Z", DerivedCategory (Var "C", Var "A"),
                  Sigma ("g", ComplexMorphism (Var "C", Var "A", Var "Y", Var "Z"),
                         ComplexMorphism (Var "C", Var "A", Var "Z", Shift (Var "C", Var "A", Var "X", 1)))) in
  try
    check ctx t ty;
    print_endline "Triangle theorem typechecks OK"
  with TypeError msg -> Printf.printf "Type error in Triangle theorem: %s\n" msg

(* Тестування *)
let () =
  try
    let ctx = [
      ("compose", Pi ("A", Univ U0, Pi ("B", Univ U0, Pi ("C", Univ U0,
                  Pi ("f", Univ U0, Pi ("g", Univ U0, Univ U0))))))
    ] in
    let cat = CategoryIntro { 
      ob = Univ U0; 
      hom = Univ U0; 
      compose = Var "compose"; 
      id = Var "id" 
    } in
    check ctx cat Category;
    print_endline "Category typechecks OK";
    theorem_quasi_iso_compose;
    theorem_triangle
  with
  | TypeError msg -> Printf.printf "Type error: %s\n" msg
