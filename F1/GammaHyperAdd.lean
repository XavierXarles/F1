import F1.F1Modules
import F1.Gamma

/-!
# The hyper-additive structure of a Γ-set

A Γ-set `X` has a set of *points* `X.Points = X 1₊`, and every `z : X n₊` has `n`
projections `X.proj i z : X.Points` and a total sum `X.add n z : X.Points` (the images of `z`
under the maps `N.map_proj i` and `N.map_add n`).  We declare `w` to be *a* sum of a tuple
`v : Fin n → X.Points` when `w = X.add n z` for some `z : X n₊` whose projections are the
`v i`:

`X.hadd n v = X.add n '' X.vect v`.

This is the hyperoperation of the `HyperAdd` structure on `X.Points`, and the assignment is
functorial: `GammaSet.toHyperAddCat : GammaSet ⥤ HyperAddCat.{0}`.

## Weak versus strong morphisms

Functoriality only holds for *weak* morphisms, i.e. with `HyperAdd.Hom.map_hadd` stated as

`f '' hadd n x ⊆ hadd n (f ∘ x)`.

Indeed, naturality of `α : X ⟶ Y` transports a lift `z` of `v` to a lift `α_n z` of
`f ∘ v`, which gives the inclusion (`hyperAddHom` below); but a lift of `f ∘ v` in `Y` need
not come from `X`, and the reverse inclusion genuinely fails.  For the Hurewicz map
`α : F1 ⟶ HM ℕ` (`i.succ ↦ eᵢ`, so `f : Fin 2 → ℕ`, `1 ↦ 1`) and `v = (1, 1)`:

* `F1.vect v = {z : Fin 3 | z = 1 ∧ z = 2} = ∅`, so `F1.hadd 2 v = ∅`
  (in `𝔽₁` the sum `1 + 1` is undefined);
* `(HM ℕ).hadd 2 v = {2}`.

## Implementation notes

A Γ-set is the bundled structure `GammaSet` of `F1.Gamma`, so its levels and structure maps are
read off the underlying pre-Γ-set: `X.F.obj (N.mk n)` and `X.F.map f`.  A morphism `X ⟶ Y` of
Γ-sets *is* a natural transformation `X.F ⟶ Y.F`, which is why `NatTrans.app` and
`NatTrans.naturality` apply to it directly.

`Pointed.Hom` carries no `FunLike` instance, so structure maps are applied as
`Pointed.Hom.toFun (X.F.map f) z`, as elsewhere in this project.  All category-level proofs are
`rfl`/`congrArg`, which is what crosses `N`/`ℕ` and `GammaSet`/`preGammaSet` safely.
-/

open CategoryTheory Pointed

namespace GammaSet

section Structure

variable (X : GammaSet)

/-- The value of `X` at `n₊`. -/
abbrev Level (n : ℕ) : Type 0 := (X.F.obj (N.mk n)).X

/-- The points of `X`, i.e. its value at `1₊`. -/
abbrev Points : Type 0 := X.Level 1

/-- The projection to the `j`-th coordinate of `X.Level n`,
where the coordinates go from `0` to `n-1`. -/
def proj {n : ℕ} (j : Fin n) : X.Level n → X.Points :=
  fun z => Pointed.Hom.toFun (X.F.map (N.map_proj j)) z

/-- The addition map from `X.Level n` to `X.Points`. -/
def add (n : ℕ) : X.Level n → X.Points :=
  fun z => Pointed.Hom.toFun (X.F.map (N.map_add n)) z

/-- Given a vector `v` of points, the set of elements of `X.Level n` whose
`i`-th projection is the `i`-th coordinate of `v`: the *lifts* of `v`. -/
def vect {n : ℕ} (v : Fin n → X.Points) : Set (X.Level n) :=
  {z : X.Level n | ∀ i : Fin n, v i = X.proj i z}

/-- Given a vector `v` of points, the set of points which are the sum of a lift of `v`. -/
def hadd (n : ℕ) (v : Fin n → X.Points) : Set X.Points :=
  Set.image (X.add n) (X.vect v)

theorem mem_vect_iff {n : ℕ} (v : Fin n → X.Points) (z : X.Level n) :
    z ∈ X.vect v ↔ ∀ i, v i = X.proj i z := Iff.rfl

/-- `w` is a sum of `v` exactly when it is the total sum of some lift of `v`. -/
theorem mem_hadd_iff {n : ℕ} (v : Fin n → X.Points) (w : X.Points) :
    w ∈ X.hadd n v ↔ ∃ z : X.Level n, (∀ i, v i = X.proj i z) ∧ X.add n z = w := Iff.rfl

theorem mem_hadd {n : ℕ} {v : Fin n → X.Points} {z : X.Level n}
    (hz : ∀ i, v i = X.proj i z) : X.add n z ∈ X.hadd n v := ⟨z, hz, rfl⟩

/-- The hyper-additive structure on the points of a Γ-set. -/
@[instance_reducible]
def HyperAdd : _root_.HyperAdd X.Points where
  hadd n := X.hadd n

end Structure

attribute [instance] GammaSet.HyperAdd

/-! ## Morphisms -/

section Morphisms

variable {X Y : GammaSet}

/-- The map on points (= level `1`) induced by a morphism of Γ-sets. -/
def onPoints (α : X ⟶ Y) (x : X.Points) : Y.Points :=
  Pointed.Hom.toFun (NatTrans.app α (N.mk 1)) x

/-- Naturality of `α`, written on elements: the components of `α` commute with every
structure map of the Γ-sets. -/
theorem app_act (α : X ⟶ Y) {n m : ℕ} (f : N.mk n ⟶ N.mk m) (z : X.Level n) :
    Pointed.Hom.toFun (NatTrans.app α (N.mk m)) (Pointed.Hom.toFun (X.F.map f) z)
      = Pointed.Hom.toFun (Y.F.map f) (Pointed.Hom.toFun (NatTrans.app α (N.mk n)) z) :=
  congrArg (fun g : X.F.obj (N.mk n) ⟶ Y.F.obj (N.mk m) => Pointed.Hom.toFun g z)
    (NatTrans.naturality α f)

/-- Morphisms of Γ-sets commute with the projections. -/
theorem onPoints_proj (α : X ⟶ Y) {n : ℕ} (j : Fin n) (z : X.Level n) :
    onPoints α (X.proj j z)
      = Y.proj j (Pointed.Hom.toFun (NatTrans.app α (N.mk n)) z) :=
  app_act α (N.map_proj j) z

/-- Morphisms of Γ-sets commute with the addition maps. -/
theorem onPoints_add (α : X ⟶ Y) (n : ℕ) (z : X.Level n) :
    onPoints α (X.add n z)
      = Y.add n (Pointed.Hom.toFun (NatTrans.app α (N.mk n)) z) :=
  app_act α (N.map_add n) z

/-- A morphism of Γ-sets sends a lift of `v` to a lift of `onPoints α ∘ v`. -/
theorem mem_vect_app (α : X ⟶ Y) {n : ℕ} {v : Fin n → X.Points} {z : X.Level n}
    (hz : ∀ i, v i = X.proj i z) (i : Fin n) :
    (onPoints α ∘ v) i = Y.proj i (Pointed.Hom.toFun (NatTrans.app α (N.mk n)) z) :=
  (congrArg (onPoints α) (hz i)).trans (onPoints_proj α i z)

/-- **The key computation.** A morphism of Γ-sets induces a *weak* morphism of
hyper-additive structures on points: a sum of `v` is carried to a sum of `onPoints α ∘ v`.

The reverse inclusion is false in general: see the module docstring. -/
def hyperAddHom (α : X ⟶ Y) : _root_.HyperAdd.Hom X.Points Y.Points where
  toFun := onPoints α
  map_hadd n v := by
    change onPoints α '' X.hadd n v ⊆ Y.hadd n (onPoints α ∘ v)
    rw [Set.image_subset_iff]
    intro w hw
    obtain ⟨z, hz, rfl⟩ := (X.mem_hadd_iff v w).mp hw
    change onPoints α (X.add n z) ∈ Y.hadd n (onPoints α ∘ v)
    rw [onPoints_add α n z]
    exact Y.mem_hadd (mem_vect_app α hz)

@[simp] theorem coe_hyperAddHom (α : X ⟶ Y) : ⇑(hyperAddHom α) = onPoints α := rfl

theorem hyperAddHom_id (X : GammaSet) :
    hyperAddHom (𝟙 X) = _root_.HyperAdd.Hom.id X.Points := rfl

theorem hyperAddHom_comp {Z : GammaSet} (α : X ⟶ Y) (β : Y ⟶ Z) :
    hyperAddHom (α ≫ β) = (hyperAddHom β).comp (hyperAddHom α) := rfl

end Morphisms

/-! ## The functor -/

/-- **The hyper-additive-structure functor.** A Γ-set `X` is sent to its points `X 1₊`,
equipped with the hyperoperation "`hadd n v` = the sums of the lifts of `v` to level `n`", and
a morphism of Γ-sets is sent to its component at level `1`. -/
def toHyperAddCat : GammaSet ⥤ _root_.HyperAddCat.{0} where
  obj X := _root_.HyperAddCat.of X.Points
  map α := _root_.HyperAddCat.ofHom (hyperAddHom α)
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

@[simp] theorem toHyperAddCat_obj (X : GammaSet) :
    toHyperAddCat.obj X = _root_.HyperAddCat.of X.Points := rfl

@[simp] theorem toHyperAddCat_map_apply {X Y : GammaSet} (α : X ⟶ Y) (x : X.Points) :
    (toHyperAddCat.map α).hom x = onPoints α x := rfl


end GammaSet
