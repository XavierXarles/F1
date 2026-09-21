import F1.GammaF1Module

/-!
# The category of `F1module`s

`F1moduleCat` is built exactly like `HyperAddCat`: an object is a type together with an
`F1module` structure, and a morphism is a (weak) morphism `HyperAdd.Hom` of the underlying
hyper-additive structures, wrapped in a one-field structure `F1moduleCat.Hom` so that `X ⟶ Y`
is not reducibly a `FunLike` type.

Since the morphisms are literally those of `HyperAddCat`, the forgetful functor

`F1moduleCat.toHyperAddCat : F1moduleCat ⥤ HyperAddCat`

is full and faithful: `F1moduleCat` is the full subcategory of `HyperAddCat` spanned by the
objects whose hyperoperations satisfy `hadd_assoc`.  Both `AddMonCat.toHyperAddCat` (for
commutative monoids) and `GammaSpace.toHyperAddCat` factor through it; the Γ-space case is
`GammaSpace.toF1moduleCat` below, which exists thanks to `GammaSpace.hadd_assoc`.
-/

universe u

open CategoryTheory

/-- A type bundled with an `F1module` structure. -/
structure F1moduleCat : Type (u + 1) where
  /-- the underlying type -/
  carrier : Type u
  [str : F1module carrier]

attribute [instance] F1moduleCat.str

namespace F1moduleCat

instance : CoeSort F1moduleCat (Type u) := ⟨carrier⟩

attribute [coe] carrier

/-- Bundle a type with its `F1module` structure. -/
abbrev of (M : Type u) [F1module M] : F1moduleCat := ⟨M⟩

@[simp] theorem coe_of (M : Type u) [F1module M] : (of M : Type u) = M := rfl

/-- The type of morphisms in `F1moduleCat`: morphisms of the underlying `HyperAdd`
structures. -/
structure Hom (X Y : F1moduleCat.{u}) : Type u where
  /-- the underlying `HyperAdd.Hom` -/
  hom' : HyperAdd.Hom X Y

instance : Category F1moduleCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨HyperAdd.Hom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory F1moduleCat.{u} (fun X Y => HyperAdd.Hom X Y) where
  hom f := f.hom'
  ofHom f := ⟨f⟩
  hom_ofHom _ := rfl
  ofHom_hom _ := rfl
  id_apply _ := rfl
  comp_apply _ _ _ := rfl

/-- The `HyperAdd.Hom` underlying a morphism of `F1moduleCat`. -/
abbrev Hom.hom {X Y : F1moduleCat.{u}} (f : X ⟶ Y) : HyperAdd.Hom X Y :=
  ConcreteCategory.hom (C := F1moduleCat) f

/-- Promote a `HyperAdd.Hom` to a morphism of `F1moduleCat`. -/
abbrev ofHom {X Y : Type u} [F1module X] [F1module Y] (f : HyperAdd.Hom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := F1moduleCat) f

@[ext] theorem hom_ext {X Y : F1moduleCat.{u}} {f g : X ⟶ Y} (h : ∀ x, f.hom x = g.hom x) :
    f = g := by
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  exact congrArg Hom.mk (HyperAdd.Hom.ext h)

@[simp] theorem hom_id {X : F1moduleCat.{u}} : (𝟙 X : X ⟶ X).hom = HyperAdd.Hom.id X := rfl

@[simp] theorem hom_comp {X Y Z : F1moduleCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp] theorem id_apply (X : F1moduleCat.{u}) (x : X) : (𝟙 X : X ⟶ X).hom x = x := rfl

@[simp] theorem comp_apply {X Y Z : F1moduleCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).hom x = g.hom (f.hom x) := rfl

@[simp] theorem hom_ofHom {X Y : Type u} [F1module X] [F1module Y] (f : HyperAdd.Hom X Y) :
    (ofHom f).hom = f := rfl

@[simp] theorem ofHom_hom {X Y : F1moduleCat.{u}} (f : X ⟶ Y) : ofHom f.hom = f := rfl

/-- Morphisms are (weakly) compatible with the hyperoperations. -/
theorem image_hadd_subset {X Y : F1moduleCat.{u}} (f : X ⟶ Y) (n : ℕ) (x : Fin n → X) :
    f.hom '' hadd n x ⊆ hadd n (⇑f.hom ∘ x) :=
  f.hom.map_hadd n x

/-! ## The forgetful functor to `HyperAddCat` -/

/-- Forgetting `hadd_assoc`.  This is the inclusion of a full subcategory: see the `Full` and
`Faithful` instances below. -/
def toHyperAddCat : F1moduleCat.{u} ⥤ HyperAddCat.{u} where
  obj X := HyperAddCat.of X
  map f := HyperAddCat.ofHom f.hom
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

@[simp] theorem toHyperAddCat_obj (X : F1moduleCat.{u}) :
    toHyperAddCat.obj X = HyperAddCat.of X := rfl

@[simp] theorem toHyperAddCat_map_apply {X Y : F1moduleCat.{u}} (f : X ⟶ Y) (x : X) :
    (toHyperAddCat.map f).hom x = f.hom x := rfl

instance : toHyperAddCat.{u}.Faithful where
  map_injective {_ _ _ _} h := by
    ext x
    exact congrArg (fun φ => HyperAddCat.Hom.hom φ x) h

instance : toHyperAddCat.{u}.Full where
  -- A morphism of `HyperAddCat` between two `F1module`s *is* a morphism of `F1moduleCat`:
  -- nothing has to be checked, the hom types agree on the nose.
  map_surjective {X Y} g :=
    ⟨(⟨HyperAddCat.Hom.hom g⟩ : Hom X Y), by ext x; rfl⟩

end F1moduleCat

/-! ## Commutative monoids and Γ-spaces as `F1module`s -/

/-- The hyper-additive structure of a commutative monoid is an `F1module`
(`AddCommMonoid.F1module`), so `AddCommMonCat.toHyperAddCat` factors through
`F1moduleCat`. -/
def AddCommMonCat.toF1moduleCat : AddCommMonCat.{u} ⥤ F1moduleCat.{u} where
  obj M := F1moduleCat.of M
  map f := F1moduleCat.ofHom f.hom.toHyperAddHom
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

namespace GammaSpace

/-- **The Γ-space functor, refined.** The points of a Γ-space form an `F1module`
(`GammaSpace.hadd_assoc`), so the functor of the previous file lifts to `F1moduleCat`. -/
def toF1moduleCat : GammaSpace ⥤ F1moduleCat.{0} where
  obj X := F1moduleCat.of X.Points
  map α := F1moduleCat.ofHom (hyperAddHom α)
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

@[simp] theorem toF1moduleCat_obj (X : GammaSpace) :
    toF1moduleCat.obj X = F1moduleCat.of X.Points := rfl

@[simp] theorem toF1moduleCat_map_apply {X Y : GammaSpace} (α : X ⟶ Y) (x : X.Points) :
    (toF1moduleCat.map α).hom x = onPoints α x := rfl

/-- Forgetting the `F1module` structure gives back `GammaSpace.toHyperAddCat`, on objects. -/
theorem toHyperAddCat_obj_eq (X : GammaSpace) :
    F1moduleCat.toHyperAddCat.obj (toF1moduleCat.obj X) = toHyperAddCat.obj X := rfl

/-- … and on morphisms. -/
theorem toHyperAddCat_map_eq {X Y : GammaSpace} (α : X ⟶ Y) (x : X.Points) :
    (F1moduleCat.toHyperAddCat.map (toF1moduleCat.map α)).hom x
      = (toHyperAddCat.map α).hom x := rfl

end GammaSpace
