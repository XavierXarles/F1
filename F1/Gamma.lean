import F1.N
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
/-! Definition of GammaSpace -/


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
reducedness of a Γ-space will be needed. -/
lemma pt_zero (n : ℕ) : pt (0 : Fin (n + 1)) = toZero 1 ≫ fromZero n := by
  apply Pointed.hom_ext'
  intro j
  change ptFun (0 : Fin (n + 1)) j = (0 : Fin (n + 1))
  simp [ptFun]

/-- Postcomposing `pt i` with `f` picks out `f i`.  This is the naturality of `pt`. -/
lemma pt_comp {n m : ℕ} (i : Fin (n + 1)) (f : mk n ⟶ mk m) :
    pt i ≫ f = pt (Pointed.Hom.toFun f i) := by
  apply Pointed.hom_ext'
  simp_rw [PointedFin, mk]
  intro j
  change f.toFun (ptFun (n:=n) i j) = ptFun (Pointed.Hom.toFun f i) j
  by_cases hj : j = (0 : Fin 2)
  · rw [hj]
    rw [ptFun_zero i]
    exact Pointed.Hom.map_point f
  · rw [ptFun_of_ne i hj, ptFun_of_ne (f.toFun i) hj]

end N


abbrev GammaSpace : Type _ := N ⥤ Pointed.{0}

instance : Category GammaSpace :=
  inferInstanceAs (Category (N ⥤ Pointed.{0}))

/-- The tautological Γ-space: `n₊ ↦ n₊`. -/
def F1 : GammaSpace where
  obj n := PointedFin n
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

namespace GammaSpace

/-- Two morphisms of Γ-spaces are equal as soon as all their components agree. -/
theorem hom_ext {F G : GammaSpace} {α β : F ⟶ G}
    (h : ∀ n, NatTrans.app α n = NatTrans.app β n) : α = β := by
  obtain ⟨a, ha⟩ := α
  obtain ⟨b, hb⟩ := β
  have hab : a = b := funext h
  subst hab
  rfl

end GammaSpace
