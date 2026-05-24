Ulrik
=====

[![OPAM](https://img.shields.io/github/v/release/groupoid/ulrik.svg)](https://opam.ocaml.org/packages/ulrik/)
[![Actions](https://github.com/groupoid/ulrik/workflows/opam/badge.svg)](https://github.com/groupoid/ulrik/actions)

Here is presented a proof assistant and typechecker for Simplicial and Directed Type Theories called **ulrik**.

Setup
-----

```shell
$ opam install ulrik
```

Usage
-----

```shell
$ dune exec -- ./ulrik library/book.ulrik
Universe            : U
Directed Interval   : 𝕀
hom(x, y)           : { Π(t : 𝕀). A |^t ≤ 0 ∨ 1 ≤ t [ t ≤ 0 | x ] [ 1 ≤ t | y ] }
Modal Pi            : μ(t : A). B t
Twisted Arrow       : C^tw
isContr             : Σ(c : { Π(t : 𝕀). A |^t ≤ 0 ∨ 1 ≤ t [ t ≤ 0 | x ] [ 1 ≤ t | y ] }). Π(x : { Π(t : 𝕀). A |^t ≤ 0 ∨ 1 ≤ t [ t ≤ 0 | x ] [ 1 ≤ t | y ] }). c = x

=== Running Type Checker Tests ===
Test 1 passed: hom A x y is a valid type: U
Test 2 passed: id_A typechecks against Π(x:A). hom A x x
Test 3 passed: Lattice distributivity lhs = rhs: true
=== Running dirtt Type Checker Tests ===

Checking Sequent: x:A |  ⊢ id(x) : hom_A(x, x)
  => OK! (Valid Sequent)
...
Loading file library/book.ulrik...
Module book (in library/book.ulrik)
Loading file library/yoneda.ulrik...
Module yoneda (in library/yoneda.ulrik)
...
Defining term yoneda_map
  => Term yoneda_map typechecked successfully (Simplicialtt Engine)
All checks completed successfully!
```

Syntax
------

Modal Directed and Simplicial Type System.

```OCaml
type name = string
type sign = [ `Cov | `Contra ]

type expr =
  (* Common *)
  | EVar of name
  | EApp of expr * expr
  | ELam of (name * expr) * expr
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
  | EShapeInc of expr * expr                 (* φ ⊆ ψ *)
  | EExt of expr * expr * expr              (* {x : A |^φ f} *)
  | ESystem of (expr * expr) list           (* [ φ | f ] ... *)
  | EModalPi of expr * (name * expr)         (* μ(x:A). B(x) *)
  | EModalLam of (name * expr) * expr       (* λ^μ(x:A). body *)
  | EModalApp of expr * expr                 (* f @ φ *)
  | ETw of expr                             (* A^tw *)
  | EOp of expr                             (* category opposite *)
  | ETwPi0 of expr                          (* π₀(x) *)
  | ETwPi1 of expr                          (* π₁(x) *)
  | EJoin of expr * expr                    (* i ∨ j *)
  | EMeet of expr * expr                    (* i ∧ j *)
  | ENeg of expr                            (* ¬i *)

  (* Dirtt compatibility / direct AST *)
  | EHom of expr * expr * expr              (* hom(cat, a, b) *)
  | ETensor of expr * expr                  (* M * N or M ⊗ N *)
  | EFunc of expr * expr                    (* M -> N or M ⊸ N *)
  | ECoend of expr * name * expr            (* coend(x:cat). M *)
  | EEnd of expr * name * expr              (* end(x:cat). M *)
  | EIdTerm of expr                         (* id(a) *)
  | EJ of expr * name * name * name * expr * expr * expr * expr (* J *)
  | EJCov of expr * name * expr * expr * expr               (* J_cov *)
  | EJContra of expr * name * expr * expr * expr            (* J_contra *)
  | ETensorElim of name * name * expr * expr                 (* let x * y := t in c *)
  | ECoendIntro of name * name * name * expr                 (* mix x y := z in m *)
  | ECoendElim of name * name * expr * expr                 (* let <x, y> := t in c *)
  | EEndIntro of name * expr                                (* end(w, m) *)
  | EEndElim of name * name * name * expr * expr            (* let x y @ z := t in c *)

type cmd =
  | CModule of string
  | CImport of string
  | CFunctor of name * (expr * sign) list * expr
  | CDefType of name * name list * expr
  | CDefTerm of name * name list * expr * expr
  | CCheck of (name * expr) list * (name * expr) list * expr * expr  (* dirtt check *)
  | CCheckSimplicial of (name * expr) list * expr * expr             (* simplicial check *)
```

Ulrik is a proof assistant based on:

* Riehl-Shulman simplicial type theory (STT) with a directed interval, Segal and Rezk types;
* Licata-Nuyts-Schultz-Shulman directed type theory (Dirtt) with linear polarities (+/-) and quadraticality;
* Modal operators (μ/mu, modal lambda, modal application) for synthetic infinity category theory.

Features
--------

* Fibrant MLTT-style П-Σ primitives with U hierarchy
* Directed Interval 𝕀 with ordering (≤) and join/meet (∨, ∧) operators
* Segal precategories (types satisfying Segal condition)
* Rezk categories (Segal types where identity paths and isomorphisms coincide)
* Linear Directed Type Theory (dirtt) mode with linear contexts (+/- polarities)
* Quadratic variable check (guaranteeing contravariant and covariant duality)
* Binders for Ends and Coends (integrals) with corresponding elimination rules
* Opposite category and Twisted Arrow category modal operators
* Pure OCaml implementation (lexer, parser, type checker)

Benchmarks
----------

Intel i5-12400 or M4: Compilation in under 1 second, full library checks in under 0.5 seconds.

```
% time dune build
dune build  0.74s user 0.34s system 240% cpu 0.449 total
```

```
% time dune exec -- ./ulrik library/book.ulrik
dune exec -- ./ulrik library/book.ulrik  0.01s user 0.01s system 6% cpu 0.386 total
```

# Ulrik: Category Theory Library

Here is given the Ulrik Category Theory Library.

### Library

In the `library` folder presented the category theory base library:

```
library/
├── abelian.ulrik      -- Zero morphisms in abelian categories
├── adjunction.ulrik   -- Adjunctions hom(B, F(a), b) -> hom(A, a, G(b))
├── book.ulrik         -- Module index importing the category library
├── cat.ulrik          -- CAT: category of categories representation
├── category.ulrik     -- Precategories, identity, and J composition
├── equivalence.ulrik  -- Equivalences, unit and counit transformations
├── functor.ulrik      -- Functors, mapping, and J functoriality
├── groupoid.ulrik     -- Groupoids, morphism inversion maps
├── natural.ulrik      -- Natural transformations as ends
├── symmetric.ulrik    -- Symmetric monoidal categories, swap map
├── topos.ulrik        -- Presheaves on a category
├── universal.ulrik    -- Limits as ends and colimits as coends
└── yoneda.ulrik       -- Contravariant Yoneda coend and Yoneda mapping
```

Mentions
--------

* Emily Riehl, Mike Shulman. <a href="https://arxiv.org/pdf/1705.07401">A type theory for synthetic ∞-categories</a>. 2017.
* Dan Licata, Andreas Nuyts, Patrick Schultz, Michael Shulman. <a href="http://dlicata.web.wesleyan.edu/pubs/lnss20dirtt/lnss20dirtt.pdf">A Directed Type Theory for Formal Category Theory</a>. 2020.
* Daniel Gratzer, Jonathan Weinberger, Ulrik Buchholtz. <a href="https://arxiv.org/pdf/2605.xxxxx">Yoneda embedding in simplicial type theory</a>. 2026.
* Максим Сохацький. <a href="https://groupoid.github.io/anders/doc/yoneda-simplicialtt-ua.pdf">Вкладення Йонеди в сiмплiцiальнiй теорiї типiв</a>. 2026.
