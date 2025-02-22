# Dan Kan: Simplicial HoTT

Groupoid Infinity Simplicial HoTT pure algebraїc implementation with explicit syntaxt for fastest type checking.
It supports following extensions: `Chain`, `Simplex`, `Simplicial`, `Category`, `Monoid`, `Group`.
Simplicial HoTT is a Rezk/GAP replacement incorporated into CCHM/CHM/HTS Agda-like Anders/Dan core.

## Abstract

We present a domain-specific language (DSL) extension to Cubical Homotopy Type Theory (CCHM) for simplicial structures,
designed as a fast type checker with a focus on algebraic purity. Built on the Cohen-Coquand-Huber-Mörtberg (CCHM)
framework, our DSL employs a Lean/Anders-like sequent syntax `П (context) ⊢ k (v₀, ..., vₖ | f₀, ..., fₗ | ... )` to define 
k-dimensional simplices via explicit contexts, vertex lists, and face relations, eschewing geometric coherence terms
in favor of compositional constraints (e.g., `f = g ∘ h`). The semantics, formalized as inference rules in a Martin-Löf
Type Theory MLTT-like setting, include Formation, Introduction, Elimination, Composition, Computational, and
Uniqueness rules, ensuring a lightweight, deterministic computational model with linear-time type checking (O(k + m + n),
where k is vertices, m is faces, and n is relations). Inspired by opetopic purity, our system avoids cubical
path-filling (e.g., `PathP`), aligning with syntactic approaches to higher structures while retaining CCHM’s
type-theoretic foundation. Compared to opetopic sequent calculi and the Rzk prover, our DSL balances algebraic
simplicity with practical efficiency, targeting simplicial constructions over general ∞-categories,
and achieves a fast, pure checker suitable for formal proofs and combinatorial reasoning.

## Syntax

Incorporating into CCHM/CHM/HTS Anders/Dan core.

###  Definition

New sequent contruction:

```
def <name> : <type> := П (context), conditions ⊢ <n> (elements | constraints)
```

Instances:

```
def chain : Chain := П (context), conditions ⊢ n (C₀, C₁, ..., Cₙ | ∂₀, ∂₁, ..., ∂ₙ₋₁)
def simplicial : Simplicial := П (context), conditions ⊢ n (s₀, s₁, ..., sₙ | facemaps, degeneracies)
def group : Group := П (context), conditions ⊢ n (generators | relations)
def cat : Category := П (context), conditions ⊢ n (objects | morphisms | coherence)
```

### BNF

```
<program> ::= <definition> | <definition> <program>
<definition> ::= "def" <id> ":" <type-name> ":=" <type-term>
<type-name> ::= "Simplex" | "Group" | "Simplicial" | "Chain" | "Category" | "Monoid"
<type-term> ::= "П" "(" <context> ")" "⊢" <n> "(" <elements> "|" <constraints> ")" 
<digit> ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
<superscript> ::= "¹" | "²" | "³" | "⁴" | "⁵" | "⁶" | "⁷" | "⁸" | "⁹"
<n> ::= <digit> | <digit> <n>
<context> ::= <hypothesis> | <hypothesis> "," <context>
<hypothesis> ::= <id> ":" <type-term>              % Single declaration, e.g., a : Simplex
               | "(" <id-list> ":" <type-term> ")" % Grouped declaration, e.g., (a b c : Simplex)
               | <id> "=" <t> "<" <t>              % Map, e.g., ∂₁ = C₂ < C₃
               | <id> "=" <t> "∘" <t>              % Equality, e.g., ac = ab ∘ bc
<id-list> ::= <id> | <id> <id-list>                % e.g., a b c
<elements> ::= <element-list> | ε
<element-list> ::= <id> | <id> "," <element-list>
<constraints> ::= <constraint-list> | ε
<constraint-list> ::= <constraint> | <constraint> "," <constraint-list>
<constraint> ::= <t> "=" <t>                      % Equality (e.g., a ∘ a = e)
               | <id> "<" <id>                    % Map (e.g., ∂₁ < C₂)
<t> ::= <id>                                      % e.g., a
      | <t> "∘" <t>                               % e.g., a ∘ b
      | <t> "^-1"                                 % e.g., a^-1
      | <t> "^" <superscript>                     % e.g., a³
      | "e"                                       % identity
```

Meaning of <n> Across Types:

* Simplex: Dimension of the simplex—e.g., n=2 for a triangle (2-simplex).
* Group: Number of generators—e.g., n=1 for Z/3Z (one generator a).
* Simplicial: Maximum dimension of the simplicial set—e.g., n=1 for S1 (up to 1-simplices).
* Chain: Length of the chain (number of levels minus 1)—e.g., n=2 for a triangle chain (0, 1, 2 levels).
* Category: Number of objects—e.g., n=2 for a path category (two objects x,y).
* Monoid: Number of generators—e.g., n=2 for N (zero and successor).

## Semantics

### Chain

### Category

### Monoid

### Simplicial

### Simplex

#### Formation

```
\frac{}{\Gamma \vdash \text{Simplex} : \text{Set}} \quad (\text{Simplex-Form})
```

#### Introduction

```
\frac{
  \Gamma = v_0 : \text{Simplex}, \dots, v_k : \text{Simplex}, e_1, \dots,
   e_p, f_0 : \text{Simplex}, \dots, f_m : \text{Simplex}, r_1, \dots, r_n \\
  \{ v_0, \dots, v_k \} = \text{vertices in } [v_0 \, \dots \, v_k] \text{ after applying equalities } e_i \\
  \{ f_0, \dots, f_l \} = \{ f_0, \dots, f_m \} \cup \{ f_i \mid r_j = f_i = g \circ h \} \\
  |\text{set } \{ f_0, \dots, f_l \}| = k + 1 \\
  \text{for each } e_i = v_a = v_b, \, \Gamma \vdash v_a = v_b \\
  \text{for each } r_j = f_i = g \circ h, \, \Gamma \vdash \partial_0 g = \partial_k h
}{
  \Gamma \vdash k [v_0 \, \dots \, v_k] \{ f_0, \dots, f_l \} : \text{Simplex}
} \quad (\text{Simplex-Intro})
```

#### Elimination (Simplex-Face)

```
\frac{ \Gamma \vdash k [v_0 \, \dots \, v_k] \{ f_0, \dots, f_l \} : \text{Simplex} \quad i : \text{Fin}(k+1)}
     { \Gamma \vdash \partial_i \, (k [v_0 \, \dots \, v_k] \{ f_0, \dots, f_l \})
       \Rightarrow f_i } \quad (\text{Simplex-Face})
```

#### Composition 

```
\frac{\Gamma \vdash g : \text{Simplex} \quad \Gamma \vdash h : \text{Simplex} \\
      \Gamma \vdash \partial_0 g = \partial_k h }
     {\Gamma \vdash g \circ h : \text{Simplex}} \quad (\text{Composition})
```

#### Computation

Face Extraction:

```
\partial_i \, (k [v_0 \, \dots \, v_k] \{ f_0, f_1, \dots, f_l \}) \to f_i
```

Composition Reduction:

```
f_i \to g \circ h \quad \text{if } \Gamma \text{ contains } f_i = g \circ h
```

Degeneracy Reduction:

```
k [v_0 \, \dots \, v_i \, v_{i+1} \, \dots \, v_k] \{ f_0, \dots, f_l \} 
\to (k-1) [v_0 \, \dots \, v_{i-1} \, v_{i+1} \, \dots \, v_k] 
  \{ f_0', \dots, f_{l-1}' \} \quad \text{if } v_i = v_{i+1} \text{ in } \Gamma
```

Base Case:

```
0 [v] \{ \} \to v
```

#### Uniqueness

Uniqueness of Face Extraction (Simplex-Uniqueness-Face):

```
\frac{ \Gamma \vdash s = k [v_0 \, \dots \, v_k] \{ f_0, \dots, f_l \} : \text{Simplex} \\
       \Gamma \vdash t = k [v_0 \, \dots \, v_k] \{ f_0, \dots, f_l \} : \text{Simplex} \\
       \Gamma \vdash \partial_i \, s = \partial_i \, t \quad (\text{for all } i) }
     { \Gamma \vdash s = t} \quad (\text{Simplex-Uniqueness-Face})
```

Uniqueness of Composition (Composition-Uniqueness):

```
\frac{ \Gamma \vdash f = g \circ h : \text{Simplex} \\
       \Gamma \vdash f' = g' \circ h' : \text{Simplex} \\
       \Gamma \vdash g = g' \quad \Gamma \vdash h = h' \\
       \Gamma \vdash \partial_0 g = \partial_k h \quad \Gamma \vdash \partial_0 g' = \partial_k h'}
     { \Gamma \vdash f = f' } \quad (\text{Composition-Uniqueness})
```

Uniqueness of Degeneracy (Degeneracy-Uniqueness):

```
\frac{ \Gamma \vdash s = k [v_0 \, \dots \, v_i \, v_{i+1} \, \dots \, v_k] \{ f_0, \dots, f_l \} : \text{Simplex} \\
       \Gamma \vdash t = (k-1) [v_0 \, \dots \, v_{i-1} \, v_{i+1} \, \dots \, v_k] \{ f_0', \dots, f_{l-1}' \}
     : \text{Simplex} \\
       \Gamma \vdash v_i = v_{i+1} \\
       \Gamma \vdash \partial_j s = \partial_j t \quad (\text{for all } j, \text{ adjusted indices}) }
     { \Gamma \vdash s = t } \quad (\text{Degeneracy-Uniqueness})
```

## Examples

### N-Monoid

```
def nat_monoid : Monoid
 := П (z s : Simplex),
      s ∘ z = s, z ∘ s = s
    ⊢ 2 (z s | s ∘ z = s, z ∘ s = s)
```

O(5).

### Category with Group (Path Category with Z/2Z)

```
def path_z2_category : Category
 := П (x y : Simplex),
      (f g h : Simplex),
      (z2 : Group(П (e a : Simplex), a² = e ⊢ 1 (a | a² = e))),
      f ∘ g = h
    ⊢ 2 (x y | f g h | f ∘ g = h)
```

O(8)—5 context + 2 nested group + 1 constraint—linear with nesting.

### Triangle Chain

```
def triangle_chain : Chain
 := П (v₀ v₁ v₂ e₀₁ e₀₂ e₁₂ t : Simplex),
      ∂₁₀ = e₀₁, ∂₁₁ = e₀₂, ∂₁₂ = e₁₂, ∂₂ < e₀₁ e₀₂ e₁₂
    ⊢ 2 (v₀ v₁ v₂, e₀₁ e₀₂ e₁₂, t | ∂₁₀ ∂₁₁ ∂₁₂, ∂₂)
```

O(11).

### Simplicial Circle

```
def circle : Simplicial
 := П (v e : Simplex),
       ∂₁₀ = v, ∂₁₁ = v, s₀ < v
     ⊢ 1 (v, e | ∂₁₀ ∂₁₁, s₀)
```

O(5).

### Z/3Z

```
def z3 : Group
 := П (e a : Simplex),
      a³ = e
    ⊢ 1 (a | a³ = e)
```

O(4).

### Triangle

```
def triangle : Simplex := П (a b c : Simplex),
         (ab bc ca : Simplex), ac = ab ∘ bc
         ⊢ 2 (a b c | ab bc ca)
```

O(7).

### Singular Cone

```
def singular_cone : Simplex
 := П (p q r s : Simplex),
      (qrs prs pqs : Simplex), pqr = pqs ∘ qrs
    ⊢ 3 (p q r s | qrs prs pqs pqr)
```

Context: p, q, r, s: Simplex (vertices), qrs, prs, pqs : Simplex (faces), pqr = pqs ∘ qrs.

Simplex: Dimension 3, 4 faces.

### Möbius Piece

```
def Möbius : Simplex
 := П (a b c : Simplex),
      (bc ac : Simplex), ab = bc ∘ ac
    ⊢ 2 (a b c | bc ac ab)
```

Context: a, b, c : Simplex (vertices), bc, ac : Simplex (faces), ab = bc ∘ ac (relation).

Simplex: Dimension 2, 3 faces.

### Degenerate Tetrahedron

```
def degen_tetra : Simplex
 := П (p q r s : Simplex, q = r),
      (qrs prs pqs : Simplex), pqr = pqs ∘ qrs
    ⊢ 3 (p q r s | qrs prs pqs pqr)
```

Context: p, q, r, s : Simplex, q = r (degeneracy), qrs, prs, pqs : Simplex, pqr = pqs ∘ qrs.

Simplex: Dimension 3, 4 faces—degeneracy implies a collapsed edge.

Non-Triviality: q = r flattens the structure algebraically, testing composition under equality.

### Twisted Annulus

```
def twisted_annulus : Simplex
 := П (a b c d : Simplex),
      (bc ac bd : Simplex), ab = bc ∘ ac, cd = ac ∘ bd
    ⊢ 2 (a b c | bc ac ab), 2 (b c d | bc bd cd)
```

Context:
* Vertices:  a, b, c, d.
* Faces: bc, ac, bd.
* Relations: ab = bc ∘ ac,  cd = ac ∘ bd  (twist via composition).
  
Simplices:
* (a b c | bc, ac, ab ): First triangle.
* (b c d | bc, bd, cd ): Second triangle, sharing bc.
  
Checking:
* Vertices: a, b, c, d ∈ Γ — O(4).
* Faces: bc, ac, ab (O(3)), bc, bd, cd (O(3)) — total O(6).
* Relations: ab = bc ∘ ac (O(1)), cd = ac ∘ bd (O(1)) — O(2).
* Total: O(12) — linear, fast.

### Degenerate Triangle (Collapsed Edge)

```
def degen_triangle : Simplex
 := П (a b c : Simplex, b = c),
      (bc ac : Simplex), ab = bc ∘ ac
    ⊢ 2 (a b c | bc ac ab)
```

Context: 
* Vertices: a, b, c, with b = c.
* Faces: bc, ac.
* Relation: ab = bc ∘ ac.

Simplex:
* (a b c | bc, ac, ab ) — 3 faces, despite degeneracy.

Checking:
* Vertices: a, b, c ∈ Γ, b = c — O(3).
* Faces: bc, ac, ab ∈ Γ — O(3).
* Relation: ab = bc ∘ ac — O(1).
* Total: O(7)—efficient, handles degeneracy cleanly.

### Singular Prism (Degenerate Face)

```
def singular_prism : Simplex
 := П (p q r s t : Simplex),
      (qrs prs pqt : Simplex, qrs = qrs), pqr = pqt ∘ qrs
    ⊢ 3 (p q r s | qrs prs pqt pqr)
```

Context: 
* Vertices: p, q, r, s, t.
* Faces: qrs, prs, pqt.
* Relations: qrs = qrs (degenerate identity), pqr = pqt ∘ qrs.

Simplex: 
* (p q r s | qrs, prs, pqt, pqr ) — 4 faces, one degenerate.

Checking:
* Vertices: p, q, r, s ∈ Γ (t unused, valid) — O(4).
* Faces: qrs, prs, pqt, pqr ∈ Γ — O(4).
* Relations: qrs = qrs (O(1)), pqr = pqt ∘ qrs (O(1)) — O(2).
* Total: O(10) — linear, fast despite degeneracy.

### S¹ as ∞-Groupoid

```
def s1_infty : Simplicial
 := П (v e : Simplex),
      ∂₁₀ = v, ∂₁₁ = v, s₀ < v,
      ∂₂₀ = e ∘ e, s₁₀ < ∂₂₀
    ⊢ ∞ (v, e, ∂₂₀ | ∂₁₀ ∂₁₁, s₀, ∂₂₀, s₁₀)
```

AST:

```
(* Infinite S¹ ∞-groupoid *)
let s1_infty = {
  name = "s1_infty";
  typ = Simplicial;
  context = [
    Decl (["v"; "e"], Simplex);  (* Base point and loop *)
    Equality ("∂₁₀", Id "v", Id "∂₁₀");
    Equality ("∂₁₁", Id "v", Id "∂₁₁");
    Equality ("s₀", Id "e", Id "s₀");
    Equality ("∂₂₀", Comp (Id "e", Id "e"), Id "∂₂₀");  (* 2-cell: e ∘ e *)
    Equality ("s₁₀", Id "∂₂₀", Id "s₁₀")  (* Degeneracy for 2-cell *)
  ];
  rank = Infinite;  (* Unbounded dimensions *)
  elements = ["v"; "e"; "∂₂₀"];  (* Finite truncation: 0-, 1-, 2-cells *)
  constraints = [
    Eq (Id "∂₁₀", Id "v");
    Eq (Id "∂₁₁", Id "v");
    Map ("s₀", ["v"]);
    Eq (Id "∂₂₀", Comp (Id "e", Id "e"));
    Map ("s₁₀", ["∂₂₀"])
  ]
}
```

### ∞-Category with cube fillers

```
def cube_infty : Category := П (a b c : Simplex),
       (f g h : Simplex), cube2 = g ∘ f, cube2 : Simplex,
       cube3 = cube2 ∘ f, cube3 : Simplex
       ⊢ ∞ (a b c | cube2 cube3)
```

## Conclusion

Dan Kan Simplicity HoTT, hosted at groupoid/dan, is a lightweight, pure type checker
built on Cubical Homotopy Type Theory (CCHM), named in tribute to Daniel Kan for
his foundational work on simplicial sets—e.g., enabling O(5) checks for circle—driving
our focus on algebraic elegance and efficiency. With a unified syntax — 
`П (context) ⊢ n (elements | constraints)` — Dan supports a rich type
system `Simplex`, `Group`, `Simplicial`, `Chain`, `Category`, `Monoid`, now extended with 
∞-categories featuring cube fillers.
