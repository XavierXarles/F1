import F1.N
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
/-! # Pre-Γ-sets and Γ-sets

`preGammaSet` is the bare functor category `N ⥤ Pointed`: a *pre*-Γ-set, i.e. a pointed-set
valued functor on `N = Γᵒᵖ` with **no condition at level `0`**.

Segal's Γ-sets are more restrictive: a Γ-object of a pointed category is a functor `Γᵒᵖ ⥤ C`
*preserving the base point*, and since `0₊` is the zero object of `Γᵒᵖ` and `*` the zero object
of `Sets_*`, that condition reads `F 0₊ = *`.  Those are the reduced pre-Γ-sets, bundled here as
the structure `GammaSet`, and they are the objects for which `Sph ⊣ Ev` holds
(`F1.spherical_adjunction`); on all of `preGammaSet` the adjunction fails, see `F1.ConstGamma`.

Everything downstream (`F1.HM`, `F1.GammaHyperAdd`, `F1.GammaF1Module`, `F1.F1moduleCat`) works
with `GammaSet`; `preGammaSet` is scaffolding, used to build Γ-sets and to state the
counterexample.
-/


universe u

open CategoryTheory

namespace Pointed

/-- Two morphisms of pointed types are equal as soon as the underlying functions agree. -/
theorem hom_ext' {X Y : Pointed.{0}} {f g : X ⟶ Y}
    (h : ∀ x, Pointed.Hom.toFun f x = Pointed.Hom.toFun g x) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  have hfg : f = g := funext h
  subst hfg
  rfl

/-- The underlying function of a composite. -/
theorem comp_toFun {X Y Z : Pointed.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.X) :
    Pointed.Hom.toFun (f ≫ g) x = Pointed.Hom.toFun g (Pointed.Hom.toFun f x) := rfl

/-- The underlying function of the identity. -/
theorem id_toFun {X : Pointed.{0}} (x : X.X) : Pointed.Hom.toFun (𝟙 X) x = x := rfl

end Pointed

namespace N

/-- `pt 1 = 𝟙 1₊`. -/
lemma pt_one : pt (1 : Fin 2) = 𝟙 (mk 1) := by
  apply Pointed.hom_ext'
  intro j
  change ptFun (1 : Fin 2) j = j
  have aux : ∀ k : Fin 2, ptFun (1 : Fin 2) k = k := by decide
  exact aux j

/-- `pt 0` is the zero map, i.e. it factors through `0₊`.  This is the only place where
reducedness of a pre-Γ-set will be needed. -/
lemma pt_zero (n : ℕ) : pt (0 : Fin (n + 1)) = toZero 1 ≫ fromZero n := by
  apply Pointed.hom_ext'
  intro j
  change ptFun (0 : Fin (n + 1)) j = (0 : Fin (n + 1))
  simp [ptFun]

/-- Postcomposing `pt i` with `f` picks out `f i`.  This is the naturality of `pt`. -/
lemma pt_comp {n m : ℕ} (i : Fin (n + 1)) (f : mk n ⟶ mk m) :
    pt i ≫ f = pt (Pointed.Hom.toFun f i) := by
  apply Pointed.hom_ext'
  intro j
  change f.toFun (ptFun i j) = ptFun (Pointed.Hom.toFun f i) j
  by_cases hj : j = (0 : Fin 2)
  · rw [hj]
    rw [ptFun_zero i]
    exact Pointed.Hom.map_point f
  · rw [ptFun_of_ne i hj, ptFun_of_ne (f.toFun i) hj]

end N


/-! ## Pre-Γ-sets -/

/-- A **pre-Γ-set**: a functor `N ⥤ Pointed`, with no condition imposed at level `0`.
Segal's Γ-sets are the reduced ones, bundled below as `GammaSet`. -/
abbrev preGammaSet : Type _ := N ⥤ Pointed.{0}

instance : Category preGammaSet :=
  inferInstanceAs (Category (N ⥤ Pointed.{0}))

namespace preGammaSet

/-- Two morphisms of pre-Γ-sets are equal as soon as all their components agree.  Since a
morphism of `GammaSet`s *is* a morphism of the underlying pre-Γ-sets, this serves both
categories. -/
theorem hom_ext {F G : preGammaSet} {α β : F ⟶ G}
    (h : ∀ n, NatTrans.app α n = NatTrans.app β n) : α = β := by
  obtain ⟨a, ha⟩ := α
  obtain ⟨b, hb⟩ := β
  have hab : a = b := funext h
  subst hab
  rfl

/-! ### Reducedness -/

/-- A pre-Γ-set is *reduced* — equivalently, it preserves the base point, i.e. it is a Γ-set in
Segal's sense — when `F 0₊` is a single point. -/
def Reduced (F : N ⥤ Pointed.{0}) : Prop :=
  ∀ x : (F.obj (N.mk 0)).X, x = (F.obj (N.mk 0)).point

/-- Unfolding of `Reduced`, so that `hF` is never applied through the definition. -/
theorem Reduced.eq_point {F : N ⥤ Pointed.{0}} (hF : Reduced F) (x : (F.obj (N.mk 0)).X) :
    x = (F.obj (N.mk 0)).point := hF x

/-- For a reduced pre-Γ-set the map induced by `pt 0 : 1₊ ⟶ n₊` (the zero map) is constant at
the basepoint, since it factors through `F 0₊ = *`. -/
theorem Reduced.map_pt_zero {F : N ⥤ Pointed.{0}} (hF : Reduced F) (n : ℕ)
    (y : (F.obj (N.mk 1)).X) :
    Pointed.Hom.toFun (F.map (N.pt (0 : Fin (n + 1)))) y = (F.obj (N.mk n)).point := by
  -- `F (pt 0) = F (fromZero) ∘ F (toZero)`
  have hmap : F.map (N.pt (0 : Fin (n + 1)))
      = F.map (N.toZero 1) ≫ F.map (N.fromZero n) :=
    (congrArg (fun g : N.mk 1 ⟶ N.mk n => F.map g) (N.pt_zero n)).trans
      (F.map_comp (N.toZero 1) (N.fromZero n))
  have h1 : Pointed.Hom.toFun (F.map (N.pt (0 : Fin (n + 1)))) y
      = Pointed.Hom.toFun (F.map (N.fromZero n))
          (Pointed.Hom.toFun (F.map (N.toZero 1)) y) :=
    congrArg (fun g : F.obj (N.mk 1) ⟶ F.obj (N.mk n) => Pointed.Hom.toFun g y) hmap
  -- the inner value lives in `F 0₊`, hence is the basepoint
  exact h1.trans ((congrArg (Pointed.Hom.toFun (F.map (N.fromZero n)))
      (hF.eq_point (Pointed.Hom.toFun (F.map (N.toZero 1)) y))).trans
    (Pointed.Hom.map_point (F.map (N.fromZero n))))

end preGammaSet

/-! ## Γ-sets -/

/-- **The category of Γ-sets** in Segal's sense: the reduced pre-Γ-sets, spelled out by hand as
a full subcategory of `preGammaSet` (in the same style as `N`). -/
structure GammaSet where
  /-- the underlying pre-Γ-set -/
  F : preGammaSet
  /-- the base-point-preservation condition `F 0₊ = *` -/
  reduced : preGammaSet.Reduced F

namespace GammaSet

instance : Category GammaSet where
  Hom A B := A.F ⟶ B.F
  id A := 𝟙 A.F
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- The inclusion of Γ-sets into pre-Γ-sets. -/
def incl : GammaSet ⥤ (N ⥤ Pointed.{0}) where
  obj A := A.F
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] lemma incl_obj (A : GammaSet) : incl.obj A = A.F := rfl

end GammaSet

/-- The tautological Γ-set `n₊ ↦ n₊`, i.e. the sphere `𝕊`.  It is reduced because `0₊` is a
single point. -/
def F1 : GammaSet where
  F :=
    { obj := fun n => n.toPointed
      map := fun f => f
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  reduced := fun x => N.fin1_eq_zero x
