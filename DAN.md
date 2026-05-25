# Entering Dan from GAP: A Technical Guide

This guide is designed for mathematicians, computer scientists, and software engineers who are familiar with **GAP (Groups, Algorithms, and Programming)** and wish to transition to the **Dan (Simplicity HoTT)** language.

We compare the language paradigms, syntax, and structural definitions of both computer algebra systems, demonstrating how to map your computational discrete algebra into Dan's type-checked presentations.

---

## 1. Paradigm Shift: Dynamic Computation vs. Static Verification

Before diving into syntax, it is crucial to understand the fundamental difference in design philosophy:

- **GAP** is a **dynamically typed, computationally active** environment. You define groups or rings, and GAP computes their properties (order, conjugacy classes, composition series) on the fly using algebraic algorithms.
- **Dan** is a **statically checked, presentation-oriented** system. Dan is designed to quickly verify that your algebraic and simplicial presentations are structurally sound. Because Dan maps directly into **Simplicial Type Theory (Ulrik)** and **Directed Type Theory (Mike)**, it allows you to prove metatheorems (such as limits, adjunctions, or Yoneda mappings) about your constructions that hold "for free" across all models.

---

## 2. Defining Groups and Monoids

### In GAP:
In GAP, you typically present a group by declaring a free group and factoring out relations:

```gap
# GAP Code: Defining the Cyclic Group Z/3Z
f := FreeGroup("a");;
z3 := f / [ f.1^3 ];;
Print(Size(z3)); # Outputs: 3
```

### In Dan:
In Dan, you present groups using the unified sequent notation:
$$\Pi (\text{context}), \text{conditions} \vdash \text{rank} (\text{generators} \mid \text{relations})$$

```dan
-- Dan Code: Defining the Cyclic Group Z/3Z
def z3 : Group
 := П (e a : Simplex),
      a³ = e
    ⊢ 1 (a | a³ = e)
```

**Key Differences:**
1. **Explicit Identity**: You must explicitly declare the identity element `e` and generator `a` in the context $\Pi$.
2. **Rank Restriction**: The rank `1` indicates that the group is presented by a single generator. Dan's checker verifies that the count of elements in the elements list (`a`) matches this rank.
3. **Purity**: Dan checks that the equations in the constraints are well-formed and contain only declared variables.

---

## 3. Rings and Fields

### In GAP:
GAP provides concrete representations of finite fields and polynomial rings:

```gap
# GAP Code: Galois Field GF(7) and polynomial ring operations
f7 := GF(7);;
x := Indeterminate(f7, "x");;
poly := x^2 + One(f7);;
```

### In Dan:
Dan presents rings and fields algebraically by declaring elements and equations in the presentation. It allows embedding concrete spectra (like matrices or polynomials) directly in the presentation:

```dan
-- Dan Code: GF(7) Prime Field
def gf7 : Field
 := П (x y s p d : Simplex),
      x + y = s, x ⋅ y = p, x / y = d,
      x = 2, y = 3, s = 5, p = 6, d = 3
    ⊢ 5 (x y s p d | x + y = s, x ⋅ y = p, x / y = d,
                     x = 2, y = 3, s = 5, p = 6, d = 3)

-- Dan Code: Polynomial Ring Z[x]
def poly_ring_zx : Ring
 := П (f g s p : Simplex),
      f + g = s, f ⋅ g = p,
      f = x + 1, g = 2 ⋅ x, s = 3 ⋅ x + 1, p = 2 ⋅ x ⋅ x + 2 ⋅ x
    ⊢ 4 (f g s p | f + g = s, f ⋅ g = p, f = x + 1, g = 2 ⋅ x,
                   s = 3 ⋅ x + 1, p = 2 ⋅ x ⋅ x + 2 ⋅ x)
```

**Optimization Note:**
Dan's algebraic checker validates the boundary equations and arithmetic relations using fast operational OCaml lookups, verifying field/ring operations in linear time before they are elaborated to type theory.

---

## 4. Higher Categorical Structures and Complexes

GAP has no native core representation for category-theoretic structures or simplicial complexes (though package extensions like CAP exist). In Dan, **Categories**, **Simplicial Sets**, and **Chain Complexes** are first-class constructs.

### 4.1 Simplicial Sets (circle $S^1$)
In Dan, a simplicial set is defined by vertices, edges, face relations, and degeneracies:

```dan
-- Dan Code: Simplicial Circle S1
def circle : Simplicial
 := П (v e : Simplex),
      ∂₁₀ = v, ∂₁₁ = v, s₀ < v
    ⊢ 1 (v, e | ∂₁₀ ∂₁₁, s₀)
```
- `∂₁₀ = v, ∂₁₁ = v` represents that both endpoints of the 1-simplex (edge `e`) map to the 0-simplex (vertex `v`).
- `s₀ < v` is the degeneracy map constraint (the vertex `v` collapses to a degenerate edge).

### 4.2 Categories
A category is presented by objects, morphisms, and compositional constraints:

```dan
-- Dan Code: Path Category with Z2 Group symmetries
def path_z2_category : Category
 := П (x y : Simplex),
      (f g h : Simplex),
      (z2 : Group(П (e a : Simplex), a² = e ⊢ 1 (a | a² = e))),
      f ∘ g = h
    ⊢ 2 (x y | f g h | f ∘ g = h)
```
- The context can contain nested algebraic structures, such as the group `z2`.
- Composition is represented by `f ∘ g = h`.

---

## 5. Syntax Correspondence Sheet

| Construct | GAP Syntax | Dan Syntax |
| :--- | :--- | :--- |
| **Variable Assignment** | `x := 2;;` | `x = 2` (declared in context $\Pi$) |
| **Group Generator** | `f.1` | `a` |
| **Morphism Composition**| `*` (or custom functions) | `∘` (e.g. `f ∘ g`) |
| **Power Operation** | `a^3` | `a³` (or `Pow(a, S3)`) |
| **Matrix Definition** | `[[1,2],[3,4]]` | `[[1,2],[3,4]]` |
| **Identity Element** | `One(G)` | `e` |
| **Boundary Maps** | Not Native | `∂ᵢⱼ` |
| **Degeneracy Maps** | Not Native | `sᵢⱼ` |

---

## 6. How it Bridges to Verification

When you write a definition in Dan, you can verify it in the OCaml type-checking engines `Ulrik` and `Mike`.

For example, when Dan parses your category `path_z2_category`, Option B translates it automatically:
1. Objects `x, y` map to points in a type `C : U`.
2. Morphisms `f, g, h` map to extension types over the directed interval $\mathbb{I}$:
   $$\text{hom}_C(x, y) \coloneqq \{ t : \mathbb{I} \to C \mid t(0) = x, t(1) = y \}$$
3. The composition equation `f ∘ g = h` maps to a Segal equivalence path proof.

This means you can immediately prove theorems about `path_z2_category` (such as the existence of limits or composition of quasi-isomorphisms) using the full power of Directed and Simplicial Type Theories!
