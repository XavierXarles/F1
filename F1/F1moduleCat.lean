import F1.GammaF1Module

/-!
# The category of `F1module`s

`F1moduleCat` is built exactly like `HyperAddCat`: an object is a type together with an
`F1module` structure, and a morphism is an `F1module.Hom`, i.e. a (weak) morphism of the
underlying hyper-additive structures *which preserves the zero*, wrapped in a one-field structure
`F1moduleCat.Hom` so that `X ⟶ Y` is not reducibly a `FunLike` type.

The forgetful functor

`F1moduleCat.toHyperAddCat : F1moduleCat ⥤ HyperAddCat`

is faithful, but no longer full: a morphism of `HyperAddCat` between two `F1module`s is a
morphism of `F1moduleCat` exactly when it preserves the zero (`F1moduleCat.homOfHyperAdd`).

Both `AddCommMonCat.toHyperAddCat` and `GammaSpace.toHyperAddCat` factor through `F1moduleCat`:
additive homs preserve `0`, and components of morphisms of Γ-spaces preserve basepoints.
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

/-- The type of morphisms in `F1moduleCat`: zero-preserving weak morphisms. -/
structure Hom (X Y : F1moduleCat.{u}) : Type u where
  /-- the underlying `F1module.Hom` -/
  hom' : F1module.Hom X Y

instance : Category F1moduleCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨F1module.Hom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory F1moduleCat.{u} (fun X Y => F1module.Hom X Y) where
  hom f := f.hom'
  ofHom f := ⟨f⟩
  hom_ofHom _ := rfl
  ofHom_hom _ := rfl
  id_apply _ := rfl
  comp_apply _ _ _ := rfl

/-- The `F1module.Hom` underlying a morphism of `F1moduleCat`. -/
abbrev Hom.hom {X Y : F1moduleCat.{u}} (f : X ⟶ Y) : F1module.Hom X Y :=
  ConcreteCategory.hom (C := F1moduleCat) f

/-- Promote an `F1module.Hom` to a morphism of `F1moduleCat`. -/
abbrev ofHom {X Y : Type u} [F1module X] [F1module Y] (f : F1module.Hom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := F1moduleCat) f

@[ext] theorem hom_ext {X Y : F1moduleCat.{u}} {f g : X ⟶ Y} (h : ∀ x, f.hom x = g.hom x) :
    f = g := by
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  exact congrArg Hom.mk (F1module.Hom.ext h)

@[simp] theorem hom_id {X : F1moduleCat.{u}} : (𝟙 X : X ⟶ X).hom = F1module.Hom.id X := rfl

@[simp] theorem hom_comp {X Y Z : F1moduleCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp] theorem id_apply (X : F1moduleCat.{u}) (x : X) : (𝟙 X : X ⟶ X).hom x = x := rfl

@[simp] theorem comp_apply {X Y Z : F1moduleCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).hom x = g.hom (f.hom x) := rfl

@[simp] theorem hom_ofHom {X Y : Type u} [F1module X] [F1module Y] (f : F1module.Hom X Y) :
    (ofHom f).hom = f := rfl

@[simp] theorem ofHom_hom {X Y : F1moduleCat.{u}} (f : X ⟶ Y) : ofHom f.hom = f := rfl

/-- Morphisms are (weakly) compatible with the hyperoperations. -/
theorem image_hadd_subset {X Y : F1moduleCat.{u}} (f : X ⟶ Y) (n : ℕ) (x : Fin n → X) :
    f.hom '' hadd n x ⊆ hadd n (⇑f.hom ∘ x) :=
  f.hom.map_hadd n x

/-- Morphisms preserve the zero. -/
@[simp] theorem map_zero {X Y : F1moduleCat.{u}} (f : X ⟶ Y) :
    f.hom (F1module.zero : X) = (F1module.zero : Y) :=
  f.hom.map_zero

/-! ## The forgetful functor to `HyperAddCat` -/

/-- Forgetting the zero and `hadd_assoc`.  Faithful, but not full: see `homOfHyperAdd`. -/
def toHyperAddCat : F1moduleCat.{u} ⥤ HyperAddCat.{u} where
  obj X := HyperAddCat.of X
  map f := HyperAddCat.ofHom f.hom.toHom
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

/-- A morphism of `HyperAddCat` between two `F1module`s which preserves the zero is a morphism
of `F1moduleCat`.  This describes the image of `toHyperAddCat` on morphisms. -/
def homOfHyperAdd {X Y : F1moduleCat.{u}}
    (g : toHyperAddCat.obj X ⟶ toHyperAddCat.obj Y)
    (hg : g.hom (F1module.zero : X) = (F1module.zero : Y)) : X ⟶ Y :=
  (⟨⟨g.hom, hg⟩⟩ : Hom X Y)

@[simp] theorem toHyperAddCat_map_homOfHyperAdd {X Y : F1moduleCat.{u}}
    (g : toHyperAddCat.obj X ⟶ toHyperAddCat.obj Y)
    (hg : g.hom (F1module.zero : X) = (F1module.zero : Y)) :
    toHyperAddCat.map (homOfHyperAdd g hg) = g := by
  ext x; rfl

end F1moduleCat

/-! ## Commutative monoids and Γ-spaces as `F1module`s -/

/-- The hyper-additive structure of a commutative monoid is an `F1module` with zero `0`
(`AddCommMonoid.F1module`), and additive homs preserve `0`, so `AddCommMonCat.toHyperAddCat`
factors through `F1moduleCat`. -/
def AddCommMonCat.toF1moduleCat : AddCommMonCat.{u} ⥤ F1moduleCat.{u} where
  obj M := F1moduleCat.of M
  map f := F1moduleCat.ofHom f.hom.toF1moduleHom
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

namespace GammaSet

variable {X Y : GammaSet}

/-- The morphism of `F1module`s induced by a morphism of Γ-spaces: `hyperAddHom α`, which
preserves the zero since `α 1₊` is a pointed map. -/
def f1moduleHom (α : X ⟶ Y) : F1module.Hom X.Points Y.Points where
  toHom := hyperAddHom α
  map_zero' := Pointed.Hom.map_point (NatTrans.app α (N.mk 1))

@[simp] theorem coe_f1moduleHom (α : X ⟶ Y) : ⇑(f1moduleHom α) = onPoints α := rfl

/-- **The Γ-space functor, refined.** The points of a Γ-space form an `F1module`
(`GammaSpace.hadd_assoc`, `GammaSpace.point_mem_hadd`), so the functor of the previous file
lifts to `F1moduleCat`. -/
def toF1moduleCat : GammaSet ⥤ F1moduleCat.{0} where
  obj X := F1moduleCat.of X.Points
  map α := F1moduleCat.ofHom (f1moduleHom α)
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

@[simp] theorem toF1moduleCat_obj (X : GammaSet) :
    toF1moduleCat.obj X = F1moduleCat.of X.Points := rfl

@[simp] theorem toF1moduleCat_map_apply (α : X ⟶ Y) (x : X.Points) :
    (toF1moduleCat.map α).hom x = onPoints α x := rfl

/-- Forgetting the `F1module` structure gives back `GammaSpace.toHyperAddCat`, on objects. -/
theorem toHyperAddCat_obj_eq (X : GammaSet) :
    F1moduleCat.toHyperAddCat.obj (toF1moduleCat.obj X) = toHyperAddCat.obj X := rfl

/-- … and on morphisms. -/
theorem toHyperAddCat_map_eq (α : X ⟶ Y) (x : X.Points) :
    (F1moduleCat.toHyperAddCat.map (toF1moduleCat.map α)).hom x
      = (toHyperAddCat.map α).hom x := rfl

end GammaSet
