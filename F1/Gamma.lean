import F1.N
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
/-! Definition of GammaSpace -/


universe u

open CategoryTheory



def GammaSpace : Type _ := N ⥤ Pointed.{u}

instance : Category GammaSpace.{u} :=
  inferInstanceAs (Category (N ⥤ Pointed.{u}))

/-- The tautological Γ-space: `n₊ ↦ n₊`. -/
def F1 : GammaSpace.{0} where
  obj n := PointedFin n
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl
