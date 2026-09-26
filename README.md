# F1 — Γ-sets, hyper-additive structures and 𝔽₁-modules in Lean 4

This repository is a [Lean 4](https://lean-lang.org/) / [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization of the basic theory of **Segal's Γ-sets** viewed as **modules over the "field with one
element" 𝔽₁**, following the point of view of Connes–Consani and, more specifically, of the recent
work of Luqiao Xu on the *hyper-additive* structure of 𝔽₁-modules.

The files contain **no `sorry` and no axioms** beyond those of Lean/Mathlib.

A detailed mathematical account (definitions, statements, proof sketches and the correspondence
with Lean names) is in [`doc/F1-formalization.tex`](doc/F1-formalization.tex).

---

## 1. The mathematical idea in one page

Let `N` be the category of pointed finite sets `n₊ = {0, 1, …, n}` (pointed at `0`) and pointed
maps. This is Segal's category `Γᵒᵖ`. A **Γ-set** is a functor `X : N ⥤ Set_*` with `X(0₊) = *`.

* An ordinary commutative monoid `M` gives a Γ-set `HM`, with `HM(n₊) = Mⁿ`, where a pointed map
  `f : n₊ → m₊` acts by `(f_* a)_j = Σ_{f(i) = j} a_i`. This is the **Eilenberg–Mac Lane** functor,
  and it is *fully faithful*: commutative monoids sit inside Γ-sets.
* The tautological Γ-set `𝕊 : n₊ ↦ n₊` (called `F1` in the code) plays the role of 𝔽₁ itself: it is
  the unit of the smash product of Γ-sets. So Γ-sets are "𝔽₁-modules".

What is the *addition* of a Γ-set `X`? Its "elements" are `X(1₊)`. An element `z ∈ X(n₊)` has `n`
coordinates `X(p_j)(z) ∈ X(1₊)` (via the projections `p_j : n₊ → 1₊`) and a total sum
`X(σ)(z) ∈ X(1₊)` (via the fold map `σ : n₊ → 1₊`). So one defines the **n-ary hyper-sum**

```
v₁ ⊞ ⋯ ⊞ vₙ  :=  { X(σ)(z)  |  z ∈ X(n₊),  X(p_j)(z) = v_j for all j }  ⊆  X(1₊).
```

This is a *multivalued* operation: the sum may be empty (in `𝕊`, `1 + 1` has no value) or have many
values. For `X = HM` it is the singleton `{v₁ + ⋯ + vₙ}`. Xu [X1] observed that these
hyper-operations are not strictly associative but satisfy a **law of generalized associativity**,
and used it to build an extension of scalars `− ⊗_{𝔽₁} ℤ` left adjoint to `H`.

This repository formalizes this circle of ideas, with an axiomatic notion of **`F1module`**:
a set with `n`-ary hyper-operations, a zero, and a regrouping (hyper-associativity) axiom.

## 2. Main results

| Result | Lean name | File |
|---|---|---|
| `HM : AddCommMonCat ⥤ GammaSet` is full and faithful | `HMFunctor.Full`, `HMFunctor.Faithful` | `HM.lean` |
| The spherical functor `X ↦ (n₊ ↦ X ∧ n₊)` is left adjoint to evaluation at `1₊` on Γ-sets | `GammaSet.adj : Sph₀ ⊣ Ev₁` | `spherical_adjunction.lean` |
| …but this adjunction is **false** on non-reduced functors `N ⥤ Pointed` | `GammaSet.not_adj` | `ConstGamma.lean` |
| Points of a Γ-set carry a hyper-additive structure, functorially (for *weak* morphisms) | `GammaSet.toHyperAddCat` | `GammaHyperAdd.lean` |
| Commutative monoids embed fully faithfully into hyper-additive structures | `AddMonCat.toHyperAddCat` (`Full`, `Faithful`) | `HyperAdd.lean` |
| **Generalized associativity**: the points of *every* Γ-set form an `F1module` | `GammaSet.hadd_assoc`, `instance : F1module X.Points` | `GammaF1Module.lean` |
| Subsets of `{1,…,n}` with disjoint union form an `F1module` `𝒫(n)` | `Subsets.instF1module` | `Subsets.lean` |
| **Nerve**: the points functor `GammaSet ⥤ F1moduleCat` has a right adjoint `M ↦ (n₊ ↦ Hom(𝒫(n), M))` | `Nerve.adj` | `Nerve.lean` |
| **Enveloping monoid**: `F1moduleCat ⥤ AddCommMonCat` is left adjoint to the inclusion | `F1moduleCat.envAdj` | `F1moduleAddCommMonCat.lean` |
| Smash product (Day convolution) makes `GammaSet` a **monoidal category** with unit `𝕊` | `instance : MonoidalCategory GammaSet` | `GammaMonoidal.lean` |

Composing the last adjunctions gives, at the level of commutative monoids, the analogue of Xu's
extension of scalars `− ⊗_{𝔽₁} ℤ ⊣ H` [X1, §4] (the composite is not yet assembled as a single
Lean statement; see *Status* below).

## 3. Overview of the files

The dependency order is roughly the order below.

**Foundations**

* `N.lean` — the category `N ≃ Γᵒᵖ` of pointed finite sets `n₊`; special maps: fold `map_add`,
  projections `map_proj`, `toZero`, `fromZero`, points `pt i : 1₊ ⟶ n₊`.
* `Smash.lean` — product and smash product `X ⋀ Y` of pointed types, universal property, functoriality.
* `Gamma.lean` — pre-Γ-sets (`N ⥤ Pointed`), the reducedness condition `F(0₊) = *`, the category
  `GammaSet`, and the unit Γ-set `F1 = 𝕊`.
* `NMonoidal.lean` — the smash product on `N`, realised as `m₊ ∧ n₊ = (m·n)₊` via an explicit
  encoding; associators, unitors and symmetry of `N`.

**Examples of Γ-sets and adjunctions**

* `HM.lean` — the Eilenberg–Mac Lane Γ-set `HM` of a commutative monoid; full faithfulness.
* `spherical.lean` — the spherical functor `S X = X ⋀ (−)`.
* `spherical_adjunction.lean` — `Sph₀ ⊣ Ev₁` on Γ-sets.
* `ConstGamma.lean` — the constant functor `F_A` shows that reducedness is essential.

**Hyper-additive structures and 𝔽₁-modules**

* `HyperAdd.lean` — the class `HyperAdd` (n-ary hyper-operations `hadd n : (Fin n → M) → Set M`),
  *weak* morphisms `f '' hadd n x ⊆ hadd n (f ∘ x)`, the category `HyperAddCat`.
* `HyperAddStrict.lean` — the same with *strict* morphisms (`=` instead of `⊆`). This is an
  alternative to `HyperAdd.lean` (it defines the same names), kept to document why the weak
  version is the right one.
* `F1Modules.lean` — the class `F1module` (zero + hyper-associativity) and its morphisms.
* `F1moduleCat.lean` — the bundled category `F1moduleCat` and the functors
  `GammaSet.toF1moduleCat` and `AddCommMonCat.toF1moduleCat`.
* `GammaHyperAdd.lean` — the hyper-sum on the points of a Γ-set and the functor to `HyperAddCat`.
* `GammaF1Module.lean` — proof of generalized associativity: points of Γ-sets are `F1module`s.
* `Subsets.lean` — the model `F1module` `𝒫(n)`.
* `Nerve.lean` — the nerve of an `F1module` and the adjunction `points ⊣ Nerve`.
* `F1moduleAddCommMonCat.lean` — the enveloping commutative monoid and `env ⊣ inclusion`.

**Monoidal structure**

* `GammaMonoidal.lean` — the smash product of Γ-sets as an explicit colimit, bimorphisms and
  trimorphisms, associator, unitors, pentagon and triangle.

## 4. Some design choices worth knowing

* **Γ-sets are reduced.** A Γ-object in a pointed category must preserve the zero object, i.e.
  `X(0₊) = *`. The file `ConstGamma.lean` proves that, without this condition, the basic adjunction
  `Sph ⊣ Ev` fails: every natural transformation `S X ⟶ F_A` into a constant functor is trivial.
* **Weak morphisms of hyper-structures.** A morphism of Γ-sets `α : X ⟶ Y` only gives
  `α(v₁ ⊞ ⋯ ⊞ vₙ) ⊆ α(v₁) ⊞ ⋯ ⊞ α(vₙ)`. Equality fails already for the Hurewicz map `𝕊 ⟶ Hℕ`:
  in `𝕊` the sum `1 ⊞ 1` is empty, while in `Hℕ` it is `{2}`. On ordinary monoids an inclusion of
  singletons is an equality, so nothing is lost there.
* **Nerve levels are all weak maps** `𝒫(n) → M`, not only zero-preserving ones; the adjunction
  `points ⊣ Nerve` needs this.
* **Smash products in `N`** are encoded as `(m·n)₊` rather than as a quotient, so that all maps of
  `N` stay concrete functions on `Fin`; equalities of maps are checked on encoded pairs.

## 5. Status and future work

* `GammaMonoidal.lean` proves that `GammaSet` is **monoidal**. The symmetric structure and the
  internal hom (closedness), announced in the header of the file, are not formalized yet.
* The composite adjunction `Γ-sets ⇄ commutative monoids` and the identification
  `Nerve(M) ≅ HM` for a commutative monoid `M` are not yet stated in Lean.
* Group completion (to reach abelian groups, as in [X1]), 𝔽₁-algebras as monoids for the smash
  product, and localization / affine schemes as in [X2] are natural next steps.

## 6. Building

```bash
lake exe cache get   # download Mathlib's compiled files
lake build
```

## 7. References

* **[X1]** Luqiao Xu, *Hyper-Operations and Extension of Scalars from 𝔽₁ to ℤ*, arXiv:2604.24568 (2026).
* **[X2]** Luqiao Xu, *Localization and Affine Schemes over 𝔽₁*, arXiv:2607.04843 (2026).
* **[CC1]** A. Connes, C. Consani, *Absolute algebra and Segal's Γ-rings: au dessous de Spec(ℤ)*,
  J. Number Theory 162 (2016), 518–551.
* **[CC2]** A. Connes, C. Consani, *On absolute algebraic geometry, the affine case*,
  Adv. Math. 390 (2021).
* **[Se]** G. Segal, *Categories and cohomology theories*, Topology 13 (1974), 293–312.
* **[Ly]** M. Lydakis, *Smash products and Γ-spaces*, Math. Proc. Cambridge Philos. Soc. 126 (1999), 311–328.
* **[BF]** A. K. Bousfield, E. M. Friedlander, *Homotopy theory of Γ-spaces, spectra, and
  bisimplicial sets*, LNM 658 (1978), 80–130.
* **[Da]** B. Day, *On closed categories of functors*, LNM 137 (1970), 1–38.
* **[De]** A. Deitmar, *Schemes over 𝔽₁*, in *Number Fields and Function Fields*, Progr. Math. 239 (2005), 87–100.
* **[Ju]** J. Jun, *Algebraic geometry over hyperrings*, Adv. Math. 323 (2018), 142–192.
* **[Mathlib]** The mathlib Community, *The Lean mathematical library*, CPP 2020.
