import F1.N
import F1.Gamma
import F1.Smash
import Init.Data.Fin.Lemmas
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.Functor.Category

/-! The spherical functor-/

universe u

open CategoryTheory Pointed

namespace GammaSpace

def S (X : Pointed.{0}) : GammaSpace where
  obj := fun n =>  X ⋀ (PointedFin n)
  map := fun {_ _} f => Smash.map (Hom.id X) (N.toFun f)
  map_id := fun _ => Smash.map_id
  map_comp := fun {_ _ _} f g =>
  Smash.map_comp (Hom.id X) (Hom.id X) (N.toFun f) (N.toFun g)

namespace S

variable (X Y : Pointed.{0})

/-- A pointed map `h : X ⟶ Y` induces a morphism of Γ-spaces `S X ⟶ S Y`, smashing with the
identity of `n₊` at each level.  (This is your `hMap`, with the naturality square filled in:
both composites send the class of `(x, i)` to the class of `(h x, f i)`.) -/
def hMap {X Y : Pointed.{0}} (h : X ⟶ Y) : S X ⟶ S Y where
  app n := Smash.map h (Hom.id (PointedFin n))
  naturality := by
    intro n m f
    apply Pointed.hom_ext'
    intro z
    refine Quotient.inductionOn z ?_
    rintro ⟨x, i⟩
    rfl

@[simp] lemma hMap_app {X Y : Pointed.{0}} (h : X ⟶ Y) (n : ℕ) :
    NatTrans.app (hMap h) n = Smash.map h (Hom.id (PointedFin n)) := rfl

lemma hMap_id (X : Pointed.{0}) : hMap (𝟙 X) = 𝟙 (S X) := by
  apply GammaSpace.hom_ext
  intro n
  apply Pointed.hom_ext'
  intro z
  refine Quotient.inductionOn z ?_
  rintro ⟨x, i⟩
  rfl

lemma hMap_comp {X Y Z : Pointed.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    hMap (f ≫ g) = hMap f ≫ hMap g := by
  apply GammaSpace.hom_ext
  intro n
  apply Pointed.hom_ext'
  intro z
  refine Quotient.inductionOn z ?_
  rintro ⟨x, i⟩
  rfl

end S

/-- **The spherical functor** `Pointed ⥤ GammaSpace`, `X ↦ (n₊ ↦ X ⋀ n₊)`. -/
def Sph : Pointed.{0} ⥤ GammaSpace where
  obj X := S X
  map h := S.hMap h
  map_id X := S.hMap_id X
  map_comp f g := S.hMap_comp f g

@[simp] lemma Sph_obj (X : Pointed.{0}) : Sph.obj X = S X := rfl

@[simp] lemma Sph_map {X Y : Pointed.{0}} (h : X ⟶ Y) : Sph.map h = S.hMap h := rfl

end GammaSpace
