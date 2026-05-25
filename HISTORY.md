# HISTORY: Decision History & Requirements

This document records the design requirements, architectural alternatives, decision history, and plan agreements for creating a unified surface language that connects the operational GAP-like core (`Dan`/`Dan Kan`) to the theoretical languages (`Ulrik` and `Mike`).

## 1. Requirements Analysis

To establish a sound architecture, we analyze the constraints and requirements of each layer.

### 1.1 Operational Layer Requirements (Dan / GAP Core)

The operational computer algebra layer is designed for fast, discrete, combinatorial algebra:

- **Presentation-Based**: Algebraic structures (groups, categories, rings, fields) are presented by generators (elements) and relations (coherences/equations).
- **Simplicial Presentations**: Simplicial complexes are specified by explicit vertices, edges, face maps ($\partial_{i}$), and degeneracy maps ($s_{i}$).
- **Linear-Time Verification**: Verification of presentations should be fast ($O(V + F + R)$, where $V$=vertices, $F$=faces, $R$=relations) by resolving boundaries and equations via lookups rather than complex type-theoretic normalization.
- **Concrete Models**: Support for concrete data types (such as integers, matrices, and polynomials) to model algebraic spectra (e.g. prime fields $\mathbb{F}_{p}$, matrix rings, spectra).

### 1.2 Theoretical Layer Requirements (Ulrik & Mike)

The theoretical layers are proof assistants for synthetic higher category theory:

- **Ulrik (Simplicial Type Theory - STT)**:
  - Requires a directed interval $\mathbb{I}$ with endpoints $0, 1$, ordering $\le$, and lattice operations ($\lor, \land, \neg$).
  - Requires shape inclusions (cofibrations) $\phi \subseteq \psi$ and extension types $\{x : A \mid^\phi f\}$.
  - Requires modal types ($\mu(t:A). B(t)$) for opposite categories ($A^{op}$) and twisted arrow categories ($A^{tw}$).
  - Standard MLTT core (dependent types $\Pi, \Sigma$, identity types $Id$).

- **Mike (Directed Type Theory - Dirtt)**:
  - Requires a linear context with polarities/signs (`Cov` or `Contra`).
  - Requires a **Quadraticality Restriction**: Category variables must occur exactly twice (once covariantly, once contravariantly) to ensure category dualities work.
  - Direct type constructs for categories, hom-spaces ($hom_C(a,b)$), monoidal tensors ($\otimes$), linear functions ($\multimap$), ends ($\int_x$), and coends ($\int^x$).
  - $J$-induction for identity paths and composition.

### 1.3 Transport Requirements ("Theorems for Free")

- **Preservation of Soundness**: An operational term (e.g., a GAP Category) must compile into a valid theoretical term (e.g., a Segal precategory in `ulrik` or category in `mike`) such that type-safety is preserved.
- **Equality Preservation**: Definitional or propositional equations in the operational presentation (e.g., $a \circ b = c$) must be mapped to identity/path terms in the theoretical layers.
- **Visual Verifiability**: A human checking the AST representation must be able to visually trace the translation to confirm that the operational structure is absorbed correctly by the theoretical type theory.

## 2. Design Options & Trade-offs

We evaluated three main architectural options for the unified surface language.

### Option A: The Unified AST Model (Super-AST)

A single AST containing all language constructs: operational types (`Group`, `Ring`, `Field`),
simplicial type theory variables, and directed type theory linear tensors/binders.

- **Pros**:
  - Single grammar, single parser, single AST datatype in OCaml.

- **Cons**:
  - **Axiomatic Pollution**: The different rules of the languages (e.g., linearity and quadraticality in `mike`, dependent structures in `ulrik`, and concrete algebraic lookups in `dan`) would be mixed.
  - **Unsoundness Risk**: Hard to guarantee that variables bound in the operational context do not leak into non-linear contexts in `mike` or violate fibrancy conditions in `ulrik`.
  - **Aesthetics & Readability**: The AST would become bloated and extremely difficult for humans to inspect and verify.

### Option B: The Compilation & Elaboration Model (AST-to-AST Mapping)

A clean surface language that allows defining operational structures as high-level declarations.
The compiler then elaborates/compiles these declarations into corresponding expressions in `Ulrik` and `Mike`'s ASTs.

- **Pros**:

  - **Separation of Concerns**: The core engines (`Dan`, `Simplicialtt`, and `Dirtt`) remain completely independent and mathematically pure.
  - **Soundness by Translation**: The translation function is a formal, syntax-directed mapping. It guarantees that any valid operational presentation yields a valid type-theoretic type/term.
  - **Verification Clarity**: Humans can verify the translation visually by comparing the parsed operational AST and the elaborated theoretical AST.
  - **Theorems for Free**: By translating the operational category to a Segal precategory, any theorem proven about general Segal precategories in the library immediately applies to the operational category.

- **Cons**:

  - Requires writing and maintaining two translation compilers: operational $\to$ simplicial, and operational $\to$ directed.

### Option C: The Deep Embedding Model

Operational structures are defined as terms of predefined algebraic record types
in `Ulrik`/`Mike` (e.g. `Record Group := { G : Type; mult : G -> G -> G; ... }`).

- **Pros**:
  - No new compilers or AST transformations are needed. Everything is done within the type theory's libraries.

- **Cons**:
  - **Computational Inefficiency**: We lose the fast $O(1)$ lookup and rewriting of the operational computer algebra system. Every operation requires expanding terms and applying path induction.
  - **Syntactic Bloat**: Specifying concrete structures like matrices or prime fields in pure MLTT is notoriously verbose and hard to read.

## 3. Decision History & Motivation

Based on the trade-offs, we selected **Option B (Compilation & Elaboration Model)**.

### Motivation

1. **Mathematical Purity**: Maintaining separate ASTs for `Ulrik` (simplicial) and `Mike` (directed) is critical because their type systems operate under different mathematical foundations (dependent fibrant type theory vs. polarized linear type theory). Merging them into a single AST (Option A) would compromise their formal verification guarantees.
2. **Visual Verifiability**: By using an explicit AST-to-AST translation map, we can print the operational AST and its translated theoretical counterparts side-by-side. This makes it trivial for humans to inspect and verify that terms from the operational layer are absorbed correctly.
3. **Execution Speed**: It preserves the fast, discrete algebraic checking of the GAP core while letting us prove theorems about these structures in the metatheory of Simplicial and Directed Type Theories.

## 4. The Golden Middle: Kernel and AST Optimization Rationale

By implementing Option B, we are able to define a "Golden Middle" architecture that balances three competing engineering priorities:

1. **Minimal Kernels**:
   - The theoretical proof engines should contain as few primitives as possible.
   - In `Ulrik` (Simplicial TT), we avoid adding a primitive `hom` type former. Instead, `hom` is elaborated to a dependent path function space over the interval $\mathbb{I}$ with endpoint extension boundaries (`EExt`).
   - In `Mike` (Directed TT), instead of duplicate linear operators, we map linear tensors $\otimes$ and coends $\int^x$ to Simplicial $\Sigma$-types (`ESig`), and linear functions $\multimap$ and ends $\int_x$ to Simplicial $\Pi$-types (`EPi`).
   - J-induction variants (`EJCov` and `EJContra`) are mapped directly to general path induction (`EJ` / `MTJ`) and composition.

2. **Clean AST Mappings**:
   - Mappings from GAP-like structures (`Dan`) to Type Theory must be direct.
   - Categories map to types satisfying Segal conditions.
   - Groups map to their classifying space loop structures ($BG$).
   - Operational algebraic equations translate to type-theoretic identity paths (`EId` / `ERef`).

3. **Fast Type Checking**:
   - Combinatorial structures (like complexes or groups) are validated statically at the operational layer in linear time.
   - Interval inequality computations and cofibration constraints in the type theory are handled by a distributive lattice solver, eliminating the need to construct explicit inductive structural proofs for interval equations.

## 5. Requirement-Based Plan Agreement

- **Phase 1**: Define a clean, unified surface grammar that supports both operational presentations (`def ... := П ... ⊢ ...`) and type-theoretic checks (`check ...`).
- **Phase 2**: Document the AST structures of the three core engines to establish the source and target representations.
- **Phase 3**: Establish explicit translation maps from the operational AST (`dan.ml`) to the theoretical ASTs (`simplicialtt.ml` and `dirtt.ml`).
- **Phase 4**: Provide a human-readable visual verification guide demonstrating how a proof (like composition of quasi-isomorphisms) is transported to a concrete operational object (like the path category).
- **Phase 5**: Integrate derived categories library into Simplicial Type Theory base library (`derived.ulrik`) and verify it.

## 6. Integration of Derived Categories into Simplicial Type Theory

### 6.1 Placement Decision

The standalone `derived.ml` script and decided to integrate its definitions and theorems into the **Simplicial Type Theory (Ulrik)** base library under `library/ulrik/derived.ulrik`. 

- **Rationale**: The structures in `derived.ml` (Category, Complexes, Morphisms, Quasi-Isomorphisms, Shifts, and Triangles) are expressed using standard dependent type-theoretic constructs ($\Pi$-types, $\Sigma$-types, Identity types, and structural pairs). They do not require the directed interval $\mathbb{I}$ or the linear polarities and quadraticality restrictions of Directed Type Theory (Mike/Dirtt). Hence, Simplicial Type Theory provides the most natural and direct fit.

### 6.2 Mapping to Simplicial Type Theory (`derived.ulrik`)

To match the golden middle of typechecking:

1. Primitives (like `Category`, `AbelianStructure`, `Complex`, `DerivedCategory`, etc.) are declared as dependent types. `Category` is represented as a nested Sigma type of objects, hom-spaces, composition, and identity.
2. The composition of quasi-isomorphisms and the existence of a triangle are represented as typechecking assertions (`check` statements) in `derived.ulrik`, referencing the parameterized category signatures.
3. The new module was appended to the base library index [book.ulrik](file:///Users/tonpa/depot/groupoid/ulrik/library/ulrik/book.ulrik), validating the entire theoretical library.

