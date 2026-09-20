import Mathlib.CategoryTheory.Category.Pointed

/-!
# The smash product of pointed types

For pointed types `(X, x₀)` and `(Y, y₀)` we define

* `Pointed.prod X Y`   : the product `X × Y`, pointed at `(x₀, y₀)`;
* `Pointed.smash X Y`  : the quotient of `X × Y` by the relation which identifies all of
  `({x₀} × Y) ∪ (X × {y₀})` (the *wedge*) to a single point, and relates nothing else.
  The base point is the class of `(x₀, y₀)`.

The relation `Pointed.SmashRel` is *already* an equivalence relation (being in the wedge is a
predicate, so transitivity is immediate), so we get a `Setoid` directly and can use `Quotient`
rather than `Quot` on a generated relation.

Main API: `Smash.mk`, `Smash.mk_eq_mk_iff`, `Smash.mk_eq_point_iff`, `Smash.ind`,
`Smash.lift` / `Smash.liftHom` (universal property) and `Smash.map` (functoriality).

Notation `X ⋀ Y` is `scoped` in `Pointed`, so `open Pointed` to use it.
-/

open CategoryTheory Pointed

universe u v

namespace Pointed

/-! ### The product of pointed types -/

/-- The product of two pointed types, pointed at the pair of base points.
This is the categorical product in `Pointed`. -/
def prod (X : Pointed.{u}) (Y : Pointed.{v}) : Pointed.{max u v} where
  X := X.X × Y.X
  point := (X.point, Y.point)

/-! ### The smash product -/

section
variable (X : Pointed.{u}) (Y : Pointed.{v})

/-- `IsWedge X Y p` says that `p : X × Y` lies in the wedge, i.e. one of its coordinates is a
base point. These are exactly the elements that get collapsed in the smash product. -/
def IsWedge (p : X.X × Y.X) : Prop :=
  p.1 = X.point ∨ p.2 = Y.point

theorem isWedge_point : IsWedge X Y (X.point, Y.point) := Or.inl rfl

/-- The relation on `X × Y` identifying any two elements of the wedge, and relating nothing
else. Since `IsWedge` is a predicate, this is already an equivalence relation. -/
def SmashRel (p q : X.X × Y.X) : Prop :=
  p = q ∨ (IsWedge X Y p ∧ IsWedge X Y q)

theorem smashRel_refl (p : X.X × Y.X) : SmashRel X Y p p := Or.inl rfl

theorem smashRel_symm {p q : X.X × Y.X} (h : SmashRel X Y p q) : SmashRel X Y q p := by
  rcases h with rfl | ⟨hp, hq⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hq, hp⟩

theorem smashRel_trans {p q r : X.X × Y.X} (h : SmashRel X Y p q) (h' : SmashRel X Y q r) :
    SmashRel X Y p r := by
  rcases h with rfl | ⟨hp, hq⟩
  · exact h'
  · rcases h' with rfl | ⟨-, hr⟩
    · exact Or.inr ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hr⟩

/-- The setoid on `X × Y` whose quotient is the smash product. -/
scoped instance smashSetoid : Setoid (X.X × Y.X) where
  r := SmashRel X Y
  iseqv :=
    { refl := smashRel_refl X Y
      symm := fun h => smashRel_symm X Y h
      trans := fun h h' => smashRel_trans X Y h h' }

/-- The smash product of two pointed types: the product `X × Y` with the wedge collapsed to a
single point, which is the base point. -/
def smash : Pointed.{max u v} where
  X := Quotient (smashSetoid X Y)
  point := Quotient.mk _ (X.point, Y.point)

end

@[nolint docBlame] scoped infixr:70 " ⋀ " => smash

namespace Smash

section
variable (X Y : Pointed.{u})

/-- The canonical map `X × Y → X ⋀ Y`. -/
def mk (p : X.X × Y.X) : (smash X Y).X := Quotient.mk _ p

theorem point_eq : (smash X Y).point = mk X Y (X.point, Y.point) := rfl

/-- Two elements of `X × Y` have the same class iff they are equal or both lie in the wedge. -/
theorem mk_eq_mk_iff {p q : X.X × Y.X} :
    mk X Y p = mk X Y q ↔ p = q ∨ (IsWedge X Y p ∧ IsWedge X Y q) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem eq_point_of_isWedge {p : X.X × Y.X} (h : IsWedge X Y p) :
    mk X Y p = (smash X Y).point :=
  Quotient.sound (Or.inr ⟨h, isWedge_point X Y⟩)

@[simp] theorem mk_point_left (b : Y.X) : mk X Y (X.point, b) = (smash X Y).point :=
  eq_point_of_isWedge X Y (Or.inl rfl)

@[simp] theorem mk_point_right (a : X.X) : mk X Y (a, Y.point) = (smash X Y).point :=
  eq_point_of_isWedge X Y (Or.inr rfl)

/-- The class of `p` is the base point exactly when `p` lies in the wedge: nothing else is
identified. -/
@[simp] theorem mk_eq_point_iff {p : X.X × Y.X} :
    mk X Y p = (smash X Y).point ↔ IsWedge X Y p := by
  refine ⟨fun h => ?_, eq_point_of_isWedge X Y⟩
  rw [point_eq, mk_eq_mk_iff] at h
  rcases h with rfl | ⟨hp, -⟩
  · exact isWedge_point X Y
  · exact hp

/-- Every element of `X ⋀ Y` is the class of some pair. -/
theorem ind {motive : (smash X Y).X → Prop} (h : ∀ p, motive (mk X Y p))
    (z : (smash X Y).X) : motive z :=
  Quotient.ind h z

/-- Universal property: a map on `X × Y` which is constant on the wedge descends to `X ⋀ Y`. -/
def lift {Z : Sort v} (f : X.X × Y.X → Z)
    (hl : ∀ b : Y.X, f (X.point, b) = f (X.point, Y.point))
    (hr : ∀ a : X.X, f (a, Y.point) = f (X.point, Y.point)) :
    (smash X Y).X → Z := by
  have key : ∀ p, IsWedge X Y p → f p = f (X.point, Y.point) := by
    rintro ⟨a, b⟩ hp
    replace hp : a = X.point ∨ b = Y.point := hp
    rcases hp with rfl | rfl
    · exact hl b
    · exact hr a
  refine Quotient.lift f ?_
  intro p q h
  replace h : p = q ∨ (IsWedge X Y p ∧ IsWedge X Y q) := h
  rcases h with rfl | ⟨hp, hq⟩
  · rfl
  · rw [key p hp, key q hq]

@[simp] theorem lift_mk {Z : Sort v} (f : X.X × Y.X → Z)
    (hl : ∀ b : Y.X, f (X.point, b) = f (X.point, Y.point))
    (hr : ∀ a : X.X, f (a, Y.point) = f (X.point, Y.point)) (p : X.X × Y.X) :
    lift X Y f hl hr (mk X Y p) = f p := rfl

/-- The quotient map, as a morphism of pointed types `X × Y ⟶ X ⋀ Y`. -/
def mkHom : Pointed.Hom (prod X Y) (smash X Y) where
  toFun := mk X Y
  map_point := rfl

/-- Universal property for pointed maps: a pointed map on `X × Y` killing the wedge descends
to a pointed map on `X ⋀ Y`. -/
def liftHom {Z : Pointed.{u}} (f : Pointed.Hom (prod X Y) Z)
    (hf : ∀ p : X.X × Y.X, IsWedge X Y p → f.toFun p = Z.point) :
      Pointed.Hom (smash X Y) Z where
  toFun := lift X Y f.toFun
    (fun b => by rw [hf (X.point, b) (Or.inl rfl), hf (X.point, Y.point) (isWedge_point X Y)])
    (fun a => by rw [hf (a, Y.point) (Or.inr rfl), hf (X.point, Y.point) (isWedge_point X Y)])
  map_point := f.map_point

end

section
variable {X X' Y Y' : Pointed.{u}}

/-- The function underlying `Smash.map`. -/
def mapFun (f : Pointed.Hom X X') (g : Pointed.Hom Y Y') : (smash X Y).X → (smash X' Y').X :=
  lift X Y (fun p => mk X' Y' (f.toFun p.1, g.toFun p.2))
    (fun b => by simp [f.map_point])
    (fun a => by simp [g.map_point])

@[simp] theorem mapFun_mk (f : Pointed.Hom X X') (g : Pointed.Hom Y Y') (p : X.X × Y.X) :
    mapFun f g (mk X Y p) = mk X' Y' (f.toFun p.1, g.toFun p.2) := rfl

/-- The morphism `X ⋀ Y ⟶ X' ⋀ Y'` induced by a pair of pointed maps. -/
def map (f : Pointed.Hom X X') (g : Pointed.Hom Y Y') : Pointed.Hom (smash X Y) (smash X' Y') where
  toFun := mapFun f g
  map_point := by
    change mapFun f g (mk X Y (X.point, Y.point)) = (smash X' Y').point
    rw [@mapFun_mk, point_eq, f.map_point,g.map_point]

@[simp]
lemma map_id : map (Hom.id X) (Hom.id Y) = Hom.id (X ⋀ Y) := by
  ext z
  induction z using Quotient.inductionOn
  rfl

lemma map_comp {X'' Y'' : Pointed.{u}} (f : Pointed.Hom X X')
    (f' : Pointed.Hom X' X'') (g : Pointed.Hom Y Y') (g' : Pointed.Hom Y' Y'') :
    map (f.comp f') (g.comp g') = (map f g).comp (map f' g') := by
  ext z
  induction z using Quotient.inductionOn
  rfl

@[simps]
def smashFunctor : Pointed.{u} × Pointed.{u} ⥤ Pointed.{u} where
  obj XY := XY.1 ⋀ XY.2
  map fg := Smash.map fg.1 fg.2
  map_id _ := Smash.map_id
  map_comp _ _ := Smash.map_comp _ _ _ _


end

end Smash

end Pointed
