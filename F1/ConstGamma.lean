import F1.spherical_adjunction

/-!
# The constant pre-Γ-set `F_A`, and why `Sph ⊣ Ev` fails on all of `preGammaSet`

This file makes precise the warning at the top of `F1.spherical_adjunction`.

For a pointed type `A` let `F_A : preGammaSet` be the **constant** pre-Γ-set

* `F_A n₊ = A` for every `n`,
* `F_A f = 𝟙 A` for every `f : n₊ ⟶ m₊`.

It is a pre-Γ-set (a functor `N ⥤ Pointed`), but it is *not* a Γ-set unless `A = *`, because
`F_A 0₊ = A`.

**Main point.** `Nat (S X, F_A)` is a single point, for *every* pointed `X` and *every* `A`:

* `GammaSet.constGamma_app_eq_point` : every `α : S X ⟶ F_A` is constant at the base point;
* `GammaSet.hom_constGamma_eq`       : any two `α β : S X ⟶ F_A` are equal;
* `GammaSet.uniqueHomConstGamma`     : `Unique (S X ⟶ F_A)`;
* `GammaSet.homConstGammaEquivUnit`  : `(S X ⟶ F_A) ≃ Unit`.

The mechanism is naturality along the *zero* endomorphism `z : n₊ ⟶ n₊` (`N.zeroHom n n`, which
factors through `0₊`).  On the spherical side `S X` does see this map non-trivially: since
`(S X).map z = 𝟙 X ⋀ z`, it sends `⟦x, i⟧ ↦ ⟦x, 0⟧ = *`.  On the constant side `F_A z = 𝟙 A` sees
nothing.  Naturality therefore forces

`α n ⟦x, i⟧ = α n ((𝟙 X ⋀ z) ⟦x, i⟧) = α n (*) = *`.

Meanwhile `Hom (X, Ev F_A) = Hom (X, A)` is *not* a single point in general: already for
`X = A = 1₊` it contains the identity and the zero map.  So there is no bijection
`(S X ⟶ F) ≃ (X ⟶ F 1₊)` natural or otherwise (`GammaSet.no_homEquiv`), hence no adjunction
`Sph ⊣ Ev` (`GammaSet.not_adj`).  Restricting to `GammaSet` removes `F_A` from the picture
(`GammaSet.not_reduced_constGamma`), which is exactly why `GammaSet.adj` can exist.

Style follows `F1.spherical_adjunction`: levels are `n m : ℕ`, `N.unmk` is used wherever a tactic
hands back an `n : N`, and no category-level step uses `rw` — `congrArg`, `Eq.trans` and `rfl`
only ever need definitional equality.
-/

universe u

open CategoryTheory Pointed preGammaSet N

namespace Pointed

/-- The zero map of pointed types: everything is sent to the base point. -/
def zeroHom (X Y : Pointed.{0}) : X ⟶ Y where
  toFun := fun _ => Y.point
  map_point := rfl

@[simp] lemma zeroHom_toFun (X Y : Pointed.{0}) (x : X.X) :
    Pointed.Hom.toFun (zeroHom X Y) x = Y.point := rfl

end Pointed

namespace N

/-- The zero map `n₊ ⟶ m₊` of `N`: the constant map at the base point, written as the composite
`n₊ ⟶ 0₊ ⟶ m₊`.  For `n = m` this is the endomorphism `z` used in the counterexample. -/
def zeroHom (n m : ℕ) : mk n ⟶ mk m := toZero n ≫ fromZero m

@[simp] lemma zeroHom_apply (n m : ℕ) (i : Fin (n + 1)) :
    Pointed.Hom.toFun (zeroHom n m) i = (0 : Fin (m + 1)) := rfl

/-- `pt 0 : 1₊ ⟶ n₊` is the zero map, in the sense of `zeroHom`. -/
lemma pt_zero_eq_zeroHom (n : ℕ) : pt (0 : Fin (n + 1)) = zeroHom 1 n := pt_zero n

end N

namespace GammaSet

/-! ## The constant pre-Γ-set -/

/-- **The constant pre-Γ-set** `F_A` at a pointed type `A`: `n₊ ↦ A`, with every map of `N` acting
as the identity of `A`.  (This is the constant functor `N ⥤ Pointed` at `A`.) -/
def constGamma (A : Pointed.{0}) : preGammaSet where
  obj _ := A
  map _ := 𝟙 A
  map_id _ := rfl
  map_comp _ _ := (Category.id_comp (𝟙 A)).symm

@[simp] lemma constGamma_obj (A : Pointed.{0}) (n : ℕ) :
    (constGamma A).obj (N.mk n) = A := rfl

@[simp] lemma constGamma_map (A : Pointed.{0}) {n m : ℕ} (f : N.mk n ⟶ N.mk m) :
    (constGamma A).map f = 𝟙 A := rfl

/-- Evaluation at level `1` of the constant pre-Γ-set is `A` itself, so the right-hand side of the
would-be adjunction is `Hom (X, A)`. -/
@[simp] lemma Ev_constGamma (A : Pointed.{0}) : Ev.obj (constGamma A) = A := rfl

/-! ### `F_A` is reduced only in the trivial case -/

/-- `F_A` is a Γ-set (reduced) exactly when `A` is a single point, since `F_A 0₊ = A`. -/
theorem constGamma_reduced_iff (A : Pointed.{0}) :
    Reduced (constGamma A) ↔ ∀ a : A.X, a = A.point := Iff.rfl

/-- As soon as `A` has a point other than its base point, `F_A` is not reduced: this is why the
counterexample disappears in `GammaSet`. -/
theorem not_reduced_constGamma {A : Pointed.{0}} {a : A.X} (ha : a ≠ A.point) :
    ¬ Reduced (constGamma A) := fun h => ha (h a)

/-! ## `S X` kills the zero map -/

/-- The spherical pre-Γ-set sends the zero map to the constant map at the base point: at level `n`
we have `(S X).map z = 𝟙 X ⋀ z`, and `⟦x, 0⟧` is the base point of `X ⋀ m₊` because `(x, 0)` lies
in the wedge.  *No* hypothesis on `X` is needed. -/
lemma S_map_zeroHom (X : Pointed.{0}) (n m : ℕ) (z : ((S X).obj (N.mk n)).X) :
    Pointed.Hom.toFun ((S X).map (N.zeroHom n m)) z = ((S X).obj (N.mk m)).point := by
  refine Quotient.inductionOn z ?_
  rintro ⟨x, i⟩
  exact Smash.eq_point_of_isWedge X (toPointed m₊) (p := (x, (0 : Fin (m + 1)))) (Or.inr rfl)

/-! ## `Nat (S X, F_A)` is a single point -/

section

variable {X A : Pointed.{0}}

/-- **The counterexample.**  Every morphism of pre-Γ-sets `α : S X ⟶ F_A` is constant at the base
point of `A`.

Proof: naturality of `α` along the zero endomorphism `z : n₊ ⟶ n₊` reads
`(S X).map z ≫ α n = α n ≫ F_A z`.  The right-hand side is `α n` because `F_A z = 𝟙 A`, and the
left-hand side kills everything because `(S X).map z` lands on the base point (`S_map_zeroHom`),
which `α n` preserves. -/
theorem constGamma_app_eq_point (α : S X ⟶ constGamma A) (n : ℕ)
    (z : ((S X).obj (N.mk n)).X) :
    Pointed.Hom.toFun (NatTrans.app α (N.mk n)) z = A.point := by
  -- naturality of `α` along `N.zeroHom n n`, evaluated at `z`
  have hnat : Pointed.Hom.toFun
        ((S X).map (N.zeroHom n n) ≫ NatTrans.app α (N.mk n)) z
      = Pointed.Hom.toFun
        (NatTrans.app α (N.mk n) ≫ (constGamma A).map (N.zeroHom n n)) z :=
    congrArg
      (fun g : (S X).obj (N.mk n) ⟶ (constGamma A).obj (N.mk n) => Pointed.Hom.toFun g z)
      (NatTrans.naturality α (N.zeroHom n n))
  -- the left-hand side is `α n (base point) = base point`
  have hL : Pointed.Hom.toFun ((S X).map (N.zeroHom n n) ≫ NatTrans.app α (N.mk n)) z
      = A.point :=
    (congrArg (Pointed.Hom.toFun (NatTrans.app α (N.mk n))) (S_map_zeroHom X n n z)).trans
      (Pointed.Hom.map_point (NatTrans.app α (N.mk n)))
  -- the right-hand side is `α n z`, since `F_A` does not move
  have hR : Pointed.Hom.toFun
        (NatTrans.app α (N.mk n) ≫ (constGamma A).map (N.zeroHom n n)) z
      = Pointed.Hom.toFun (NatTrans.app α (N.mk n)) z := rfl
  exact hR.symm.trans (hnat.symm.trans hL)

/-- The zero morphism of pre-Γ-sets `S X ⟶ F_A`: constant at the base point of `A`.  By
`constGamma_app_eq_point` it is the *only* one. -/
def zeroNat (X A : Pointed.{0}) : S X ⟶ constGamma A where
  app n := Pointed.zeroHom ((S X).obj n) A
  naturality := by
    intro n m f
    apply Pointed.hom_ext'
    intro z
    rfl

@[simp] lemma zeroNat_app (X A : Pointed.{0}) (n : ℕ) :
    NatTrans.app (zeroNat X A) (N.mk n) = Pointed.zeroHom ((S X).obj (N.mk n)) A := rfl

/-- Any two morphisms `S X ⟶ F_A` agree: `Nat (S X, F_A)` has at most one element. -/
theorem hom_constGamma_eq (α β : S X ⟶ constGamma A) : α = β := by
  apply preGammaSet.hom_ext
  intro n
  apply Pointed.hom_ext'
  intro z
  exact (constGamma_app_eq_point α (N.unmk n) z).trans
    (constGamma_app_eq_point β (N.unmk n) z).symm

instance subsingletonHomConstGamma : Subsingleton (S X ⟶ constGamma A) :=
  ⟨fun α β => hom_constGamma_eq α β⟩

end

/-- **`Nat (S X, F_A)` is a single point**: it is inhabited by the zero morphism, and that is the
only element. -/
def uniqueHomConstGamma (X A : Pointed.{0}) : Unique (S X ⟶ constGamma A) where
  default := zeroNat X A
  uniq α := hom_constGamma_eq α (zeroNat X A)

/-- The same statement as an equivalence with the one-point type. -/
def homConstGammaEquivUnit (X A : Pointed.{0}) : (S X ⟶ constGamma A) ≃ Unit where
  toFun _ := ()
  invFun _ := zeroNat X A
  left_inv α := hom_constGamma_eq (zeroNat X A) α
  right_inv _ := rfl

/-! ## The other side: `Hom (X, F_A 1₊)` is not a single point -/

/-- On `1₊` the identity and the zero map differ (they disagree on `1`), so `Hom (1₊, 1₊)` has at
least two elements. -/
theorem id_ne_zeroHom :
    (𝟙 (toPointed 1₊)) ≠ Pointed.zeroHom (toPointed 1₊) (toPointed 1₊) := by
  intro h
  have h1 : (1 : Fin 2) = (0 : Fin 2) :=
    congrArg (fun g : (toPointed 1₊) ⟶ (toPointed 1₊) => Pointed.Hom.toFun g (1 : Fin 2)) h
  exact absurd h1 (by decide)

/-! ## Consequence: no adjunction on all of `preGammaSet` -/

/-- There is no hom-set bijection `(S X ⟶ F) ≃ (X ⟶ F 1₊)` valid for all pre-Γ-sets `F`: take
`X = 1₊` and `F = F_(1₊)`.  The left-hand side is a single point, while the right-hand side
contains both `𝟙` and the zero map. -/
theorem no_homEquiv
    (e : ∀ (X : Pointed.{0}) (F : preGammaSet), (S X ⟶ F) ≃ (X ⟶ F.obj (N.mk 1))) : False := by
  have h : (e (toPointed 1₊) (constGamma (toPointed 1₊))).symm (𝟙 (toPointed 1₊))
      = (e (toPointed 1₊) (constGamma (toPointed 1₊))).symm
          (Pointed.zeroHom (toPointed 1₊) (toPointed 1₊)) :=
    hom_constGamma_eq _ _
  exact id_ne_zeroHom ((e (toPointed 1₊) (constGamma (toPointed 1₊))).symm.injective h)

/-- **The spherical functor is not left adjoint to evaluation at level `1`** on all pre-Γ-sets.
(Stated for `EvPre`, which is `Ev` viewed as a functor `preGammaSet ⥤ Pointed`; the two are
definitionally equal, so this rules out `Sph ⊣ Ev` as well.) -/
theorem not_adj (adj : Sph ⊣ EvPre) : False :=
  no_homEquiv (fun X F => adj.homEquiv X F)

/-! ## Sanity checks -/

example (A : Pointed.{0}) (n : ℕ) : (constGamma A).obj (N.mk n) = A := rfl

example (A : Pointed.{0}) : EvPre.obj (constGamma A) = A := rfl

example (X A : Pointed.{0}) (α : S X ⟶ constGamma A) : α = zeroNat X A :=
  hom_constGamma_eq α (zeroNat X A)

-- the spherical Γ-set is *not* of the form `F_A` unless everything is trivial:
-- `S X 0₊ = *` while `F_A 0₊ = A`
example (X : Pointed.{0}) : Reduced (S X) := S_reduced X

end GammaSet
