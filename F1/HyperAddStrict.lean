import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Function

/-!
# The category of hyper-additive structures

A `HyperAdd M` structure equips `M` with, for every `n : ℕ`, an `n`-ary *hyperoperation*
`hadd n : (Fin n → M) → Set M`, thought of as the set of possible values of the sum of an
`n`-tuple.

A morphism is a map `f : X → Y` which is *strongly* compatible with the hyperoperations:
`f '' hadd n x = hadd n (f ∘ x)`.

For *weak* morphisms just replace `=` by `⊆` in `HyperAdd.Hom.map_hadd`; every proof below
still works after replacing `Set.image_comp` rewriting by `Set.image_subset` and
`subset_trans`.
-/

universe u

/-- A structure with an `n`-ary hyperoperation for every `n : ℕ`. -/
class HyperAdd (M : Type u) where
  /-- `hadd n x` is the set of possible values of the sum of the tuple `x : Fin n → M`. -/
  hadd (n : ℕ) : (Fin n → M) → Set M

instance AddCommMonoid.hyperadd (M : Type u) [AddCommMonoid M] : HyperAdd M where
  hadd := fun n a => Set.singleton (∑ (i : Fin n), a i)

export HyperAdd (hadd)

namespace HyperAdd

/-- A morphism of `HyperAdd` structures: a map compatible with all the hyperoperations. -/
structure Hom (X Y : Type u) [HyperAdd X] [HyperAdd Y] : Type u where
  /-- the underlying map -/
  toFun : X → Y
  /-- compatibility with the hyperoperations -/
  map_hadd : ∀ (n : ℕ) (x : Fin n → X), toFun '' hadd n x = hadd n (toFun ∘ x)

namespace Hom

variable {X Y Z W : Type u} [HyperAdd X] [HyperAdd Y] [HyperAdd Z] [HyperAdd W]

theorem toFun_injective : Function.Injective (toFun : Hom X Y → (X → Y)) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ rfl
  rfl

instance : FunLike (Hom X Y) X Y := ⟨toFun, toFun_injective⟩

@[simp] theorem toFun_eq_coe (f : Hom X Y) : f.toFun = ⇑f := rfl

@[ext] theorem ext {f g : Hom X Y} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

/-- The point-free form of the compatibility condition. -/
theorem image_comp_hadd (f : Hom X Y) (n : ℕ) :
    Set.image f ∘ hadd (M := X) n = hadd (M := Y) n ∘ (fun x : Fin n → X => ⇑f ∘ x) :=
  funext fun x => f.map_hadd n x

@[simp] theorem image_hadd (f : Hom X Y) (n : ℕ) (x : Fin n → X) :
    f '' hadd n x = hadd n (⇑f ∘ x) :=
  f.map_hadd n x

/-- The identity morphism. -/
protected def id (X : Type u) [HyperAdd X] : Hom X X where
  toFun := _root_.id
  map_hadd n x := by simp

/-- Composition of morphisms. -/
protected def comp (g : Hom Y Z) (f : Hom X Y) : Hom X Z where
  toFun := g.toFun ∘ f.toFun
  map_hadd n x := by
    rw [Set.image_comp, f.map_hadd, g.map_hadd, Function.comp_assoc]

@[simp] theorem coe_id : ⇑(Hom.id X) = _root_.id := rfl

@[simp] theorem coe_comp (g : Hom Y Z) (f : Hom X Y) : ⇑(g.comp f) = ⇑g ∘ ⇑f := rfl

@[simp] theorem id_apply (x : X) : Hom.id X x = x := rfl

@[simp] theorem comp_apply (g : Hom Y Z) (f : Hom X Y) (x : X) : g.comp f x = g (f x) := rfl

theorem id_comp (f : Hom X Y) : (Hom.id Y).comp f = f := rfl

theorem comp_id (f : Hom X Y) : f.comp (Hom.id X) = f := rfl

theorem comp_assoc (h : Hom Z W) (g : Hom Y Z) (f : Hom X Y) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

end Hom

end HyperAdd


/-! ## The bundled category

We follow the current Mathlib convention for concrete categories: the categorical hom type is a
one-field wrapper `HyperAddCat.Hom` around the `FunLike` type `HyperAdd.Hom`, and the
`ConcreteCategory` instance records how to pass between the two.  The wrapper keeps `X ⟶ Y` from
being (reducibly) a `FunLike` type, which would give two competing coercions to functions. -/

open CategoryTheory

/-- A type bundled with a `HyperAdd` structure. -/
structure HyperAddCat : Type (u + 1) where
  /-- the underlying type -/
  carrier : Type u
  [str : HyperAdd carrier]

attribute [instance] HyperAddCat.str

namespace HyperAddCat

instance : CoeSort HyperAddCat (Type u) := ⟨carrier⟩

attribute [coe] carrier

/-- Bundle a type with its `HyperAdd` structure. -/
abbrev of (M : Type u) [HyperAdd M] : HyperAddCat := ⟨M⟩

@[simp] theorem coe_of (M : Type u) [HyperAdd M] : (of M : Type u) = M := rfl

/-- The type of morphisms in `HyperAddCat`. -/
structure Hom (X Y : HyperAddCat.{u}) : Type u where
  /-- the underlying `HyperAdd.Hom` -/
  hom' : HyperAdd.Hom X Y

instance : Category HyperAddCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨HyperAdd.Hom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory HyperAddCat.{u} (fun X Y => HyperAdd.Hom X Y) where
  hom f := f.hom'
  ofHom f := ⟨f⟩
  hom_ofHom _ := rfl
  ofHom_hom _ := rfl
  id_apply _ := rfl
  comp_apply _ _ _ := rfl

/-- The `HyperAdd.Hom` underlying a morphism of `HyperAddCat`. -/
abbrev Hom.hom {X Y : HyperAddCat.{u}} (f : X ⟶ Y) : HyperAdd.Hom X Y :=
  ConcreteCategory.hom (C := HyperAddCat) f

/-- Promote a `HyperAdd.Hom` to a morphism of `HyperAddCat`. -/
abbrev ofHom {X Y : Type u} [HyperAdd X] [HyperAdd Y] (f : HyperAdd.Hom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := HyperAddCat) f

@[ext] theorem hom_ext {X Y : HyperAddCat.{u}} {f g : X ⟶ Y} (h : ∀ x, f.hom x = g.hom x) :
    f = g := by
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  exact congrArg Hom.mk (HyperAdd.Hom.ext h)

@[simp] theorem hom_id {X : HyperAddCat.{u}} : (𝟙 X : X ⟶ X).hom = HyperAdd.Hom.id X := rfl

@[simp] theorem hom_comp {X Y Z : HyperAddCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp] theorem id_apply (X : HyperAddCat.{u}) (x : X) : (𝟙 X : X ⟶ X).hom x = x := rfl

@[simp] theorem comp_apply {X Y Z : HyperAddCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).hom x = g.hom (f.hom x) := rfl

@[simp] theorem hom_ofHom {X Y : Type u} [HyperAdd X] [HyperAdd Y] (f : HyperAdd.Hom X Y) :
    (ofHom f).hom = f := rfl

@[simp] theorem ofHom_hom {X Y : HyperAddCat.{u}} (f : X ⟶ Y) : ofHom f.hom = f := rfl

/-- Morphisms really are compatible with the hyperoperations. -/
theorem image_hadd {X Y : HyperAddCat.{u}} (f : X ⟶ Y) (n : ℕ) (x : Fin n → X) :
    f.hom '' hadd n x = hadd n (⇑f.hom ∘ x) :=
  f.hom.map_hadd n x

-- The forgetful functor and its faithfulness now come from the `ConcreteCategory` instance:
-- `CategoryTheory.forget HyperAddCat.{u}`.

end HyperAddCat


/-! ## A sanity-check example

The "free" hyperoperation `hadd n x = Set.range x` makes *every* map a morphism, so this gives
a functor `Type u ⥤ HyperAddCat.{u}` (left adjoint to the forgetful functor, in fact). -/

namespace HyperAdd

/-- Every type carries the hyperoperation sending a tuple to its range. -/
@[instance_reducible]
def rangeHyperAdd (M : Type u) : HyperAdd M where
  hadd _ x := Set.range x

attribute [local instance] rangeHyperAdd

/-- With the range hyperoperation, every map is a morphism. -/
def ofMap {X Y : Type u} (f : X → Y) : Hom X Y where
  toFun := f
  map_hadd n x := by
    rw [hadd,hadd, rangeHyperAdd, rangeHyperAdd]
    simp only [@Set.range_comp]

end HyperAdd



namespace AddMonoid

/-- The `HyperAdd` structure on an additive monoid: `hadd n x` is the singleton containing the
(ordered) sum of the tuple `x`.

This is a global instance, so every `AddMonoid` is a `HyperAdd`.  If you would rather choose
some other hyperoperation on a monoid, make this `scoped instance` (or a plain `def`) instead. -/
instance toHyperAdd (M : Type u) [AddMonoid M] : HyperAdd M where
  hadd _ x := {(List.ofFn x).sum}

variable {M : Type u} [AddMonoid M]

@[simp] theorem hadd_eq {n : ℕ} (x : Fin n → M) : hadd n x = {(List.ofFn x).sum} := rfl

@[simp] theorem hadd_zero (x : Fin 0 → M) : hadd 0 x = {0} := by simp

theorem hadd_two (x : Fin 2 → M) : hadd 2 x = {x 0 + x 1} := by
  simp [List.ofFn_succ, Fin.succ_zero_eq_one]

/-- In a commutative monoid the hyperoperation is the usual `Finset` sum. -/
theorem hadd_eq_sum {M : Type u} [AddCommMonoid M] {n : ℕ} (x : Fin n → M) :
    hadd n x = {∑ i, x i} := by
  rw [hadd_eq, List.sum_ofFn]

end AddMonoid

/-- An additive monoid hom is a morphism of the associated `HyperAdd` structures. -/
def AddMonoidHom.toHyperAddHom {M N : Type u} [AddMonoid M] [AddMonoid N] (f : M →+ N) :
    HyperAdd.Hom M N where
  toFun := f
  map_hadd n x := by
    rw [AddMonoid.hadd_eq, AddMonoid.hadd_eq, Set.image_singleton, map_list_sum, List.map_ofFn]

@[simp] theorem AddMonoidHom.coe_toHyperAddHom {M N : Type u} [AddMonoid M] [AddMonoid N]
    (f : M →+ N) : ⇑f.toHyperAddHom = ⇑f := rfl

/-- Conversely, any morphism between the hyperstructures of two additive monoids is additive:
`map_hadd` at `n = 0` gives `g 0 = 0`, and at `n = 2` gives `g (a + b) = g a + g b`. -/
def HyperAdd.Hom.toAddMonoidHom {M N : Type u} [AddMonoid M] [AddMonoid N]
    (g : HyperAdd.Hom M N) : M →+ N where
  toFun := g
  map_zero' := by
    have h := g.map_hadd 0 Fin.elim0
    rw [AddMonoid.hadd_zero, AddMonoid.hadd_zero, Set.image_singleton] at h
    simpa [Set.singleton_eq_singleton_iff] using h
  map_add' a b := by
    have h := g.map_hadd 2 ![a, b]
    rw [AddMonoid.hadd_two, AddMonoid.hadd_two, Set.image_singleton] at h
    simpa [Set.singleton_eq_singleton_iff] using h

@[simp] theorem HyperAdd.Hom.coe_toAddMonoidHom {M N : Type u} [AddMonoid M] [AddMonoid N]
    (g : HyperAdd.Hom M N) : ⇑g.toAddMonoidHom = ⇑g := rfl

/-! ### The functor -/

open CategoryTheory

/-- The functor sending an additive monoid to its hyper-additive structure. -/
def AddMonCat.toHyperAddCat : AddMonCat.{u} ⥤ HyperAddCat.{u} where
  obj M := HyperAddCat.of M
  map f := HyperAddCat.ofHom f.hom.toHyperAddHom
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

@[simp] theorem AddMonCat.toHyperAddCat_obj (M : AddMonCat.{u}) :
    toHyperAddCat.obj M = HyperAddCat.of M := rfl

@[simp] theorem AddMonCat.toHyperAddCat_map_apply {M N : AddMonCat.{u}} (f : M ⟶ N) (x : M) :
    (toHyperAddCat.map f).hom x = f.hom x := rfl

instance : AddMonCat.toHyperAddCat.{u}.Faithful where
  map_injective {_ _ _ _} h := by
    ext x
    exact congrArg (fun φ => HyperAddCat.Hom.hom φ x) h

instance : AddMonCat.toHyperAddCat.{u}.Full where
  -- The type ascriptions `(M := (X : Type u))` are needed: without them Lean tries to synthesize
  -- `AddMonoid ↑(toHyperAddCat.obj X)`, and instance search will not unfold `Functor.obj`.
  -- Unification will, so naming the arguments turns the problem into a defeq check.
  map_surjective {X Y} g :=
    ⟨AddMonCat.ofHom (HyperAdd.Hom.toAddMonoidHom (M := (X : Type u)) (N := (Y : Type u)) g.hom),
      by ext x; rfl⟩

/-- The same for commutative monoids, by composing with the forgetful functor. -/
def AddCommMonCat.toHyperAddCat : AddCommMonCat.{u} ⥤ HyperAddCat.{u} :=
  forget₂ AddCommMonCat AddMonCat ⋙ AddMonCat.toHyperAddCat
