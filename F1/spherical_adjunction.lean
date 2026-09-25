import F1.spherical
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The spherical functor is left adjoint to evaluation at level `1`

**Warning.** `Sph ⊣ Ev` is *false* on `preGammaSet = N ⥤ Pointed` as defined in `F1.Gamma`:
if `F` is the constant functor at a pointed type `A`, then for any `α : S X ⟶ F` and any `x, i`,
naturality along the zero map `z : n₊ ⟶ n₊` gives
`α n ⟦x, i⟧ = α n ((id ⋀ z) ⟦x, i⟧) = α n (basepoint) = basepoint`,
so `Nat (S X, F)` is a single point while `Hom (X, F 1₊) = Hom (X, A)` is not.  See
`F1.ConstGamma` for this counterexample in full.

This is not a defect of Segal's theory but of `preGammaSet`: a Γ-object of a pointed category is
a functor `Γᵒᵖ ⥤ C` *preserving the base point*, and as `0₊` is the zero object of `Γᵒᵖ` that
condition reads `F 0₊ = *`.  The constant functor at `A ≠ *` is therefore not a Γ-set at all, and
`preGammaSet` is strictly larger than Segal's category.  On `GammaSet` (`F1.Gamma`) everything
works:

* `preGammaSet.Reduced F` : `F 0₊` has a single element;
* `GammaSet`              : the category of Γ-sets;
* `GammaSet.Sph₀ : Pointed ⥤ GammaSet` : the spherical functor (`S X` *is* reduced);
* `GammaSet.Ev₁ : GammaSet ⥤ Pointed`  : evaluation at level `1`;
* `GammaSet.adj : Sph₀ ⊣ Ev₁`.

Reducedness is used exactly once: `N.pt 0 : 1₊ ⟶ n₊` factors through `0₊`, so `F (pt 0)` is
constant at the basepoint; this is what lets the formula `⟦x, i⟧ ↦ F (pt i) (φ x)` descend from
`X × n₊` to the smash product `X ⋀ n₊`.

The unit of the adjunction is `x ↦ ⟦x, 1⟧ : X ⟶ X ⋀ 1₊` (`GammaSet.unitMap`), and the counit at
level `n` is `⟦y, i⟧ ↦ F (pt i) y`.

Everything follows the discipline documented in `F1.spherical`: statements use `n m : ℕ` and
`N ⥤ Pointed.{0}`, all level implicits are explicit, `N.unmk` is used wherever a tactic produces
an `n : N`, and no category-level proof uses `rw` — `congrArg`, `Eq.trans` and `exact` need only
definitional equality, which is what crosses `N`/`ℕ` and `preGammaSet`/`N ⥤ Pointed` safely.
-/

universe u

open CategoryTheory Pointed preGammaSet N

namespace GammaSet

/-! ## Evaluation at level 1 -/

/-- Evaluation of a pre-Γ-set at `1₊`. -/
def Ev : (N ⥤ Pointed.{0}) ⥤ Pointed.{0} where
  obj F := F.obj (N.mk 1)
  map α := NatTrans.app α (N.mk 1)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- … which is a functor `preGammaSet ⥤ Pointed`, definitionally. -/
def EvPre : preGammaSet ⥤ Pointed.{0} := Ev

/-! ## Reducedness and the spherical pre-Γ-set

`preGammaSet.Reduced`, `Reduced.eq_point` and `Reduced.map_pt_zero` are in `F1.Gamma`, together
with the category `GammaSet` itself. -/

/-- Functoriality along `pt`: `F (pt (f i)) = F f ∘ F (pt i)`. -/
theorem map_pt_comp (F : N ⥤ Pointed.{0}) {n m : ℕ} (i : Fin (n + 1))
    (f : N.mk n ⟶ N.mk m) (y : (F.obj (N.mk 1)).X) :
    Pointed.Hom.toFun (F.map (N.pt (Pointed.Hom.toFun f i))) y
      = Pointed.Hom.toFun (F.map f) (Pointed.Hom.toFun (F.map (N.pt i)) y) := by
  have hmap : F.map (N.pt (Pointed.Hom.toFun f i))
      = F.map (N.pt i) ≫ F.map f :=
    (congrArg (fun g : N.mk 1 ⟶ N.mk m => F.map g) (N.pt_comp i f).symm).trans
      (F.map_comp (N.pt i) f)
  exact congrArg (fun g : F.obj (N.mk 1) ⟶ F.obj (N.mk m) => Pointed.Hom.toFun g y) hmap

/-- The spherical pre-Γ-set is reduced, hence a Γ-set: `X ⋀ 0₊ = *`. -/
theorem S_reduced (X : Pointed.{0}) : Reduced (S X) := by
  intro x
  refine Quotient.inductionOn x ?_
  rintro ⟨a, i⟩
  exact Smash.eq_point_of_isWedge X (N.toPointed (N.mk 0)) (Or.inr (N.fin1_eq_zero i))

/-! ## Evaluation and the spherical functor, on Γ-sets -/

/-- Evaluation at level `1`, on Γ-sets. -/
def Ev₁ : GammaSet ⥤ Pointed.{0} := incl ⋙ Ev

/-- The spherical functor, viewed as landing in Γ-sets. -/
def Sph₀ : Pointed.{0} ⥤ GammaSet where
  obj X := ⟨S X, S_reduced X⟩
  map h := S.hMap h
  map_id X := S.hMap_id X
  map_comp f g := S.hMap_comp f g

@[simp] lemma Ev₁_obj (A : GammaSet) : Ev₁.obj A = A.F.obj (N.mk 1) := rfl

@[simp] lemma Ev₁_map {A B : GammaSet} (α : A ⟶ B) :
    Ev₁.map α = NatTrans.app α (N.mk 1) := rfl

/-! ## The two directions of the bijection -/

/-- The unit map `X ⟶ X ⋀ 1₊`, `x ↦ ⟦x, 1⟧`.  (It is in fact an isomorphism.) -/
def unitMap (X : Pointed.{0}) : X ⟶ X ⋀ (toPointed (N.mk 1)) where
  toFun x := Smash.mk X (toPointed (N.mk 1)) (x, (1 : Fin 2))
  map_point := Smash.mk_point_left X (toPointed (N.mk 1)) (1 : Fin 2)

/-- From a morphism of pre-Γ-sets `S X ⟶ F`, the pointed map `X ⟶ F 1₊`: evaluate at level `1`
and precompose with the unit. -/
def toPt {X : Pointed.{0}} {F : N ⥤ Pointed.{0}} (α : S X ⟶ F) : X ⟶ F.obj (N.mk 1) :=
  unitMap X ≫ NatTrans.app α (N.mk 1)

section Extend

variable {X : Pointed.{0}} {F : N ⥤ Pointed.{0}}

/-- The formula `(x, i) ↦ F (pt i) (φ x)` on `X × n₊`, which will descend to `X ⋀ n₊`. -/
def extendFun (φ : X ⟶ F.obj (N.mk 1)) (n : ℕ) (p : X.X × (toPointed (N.mk n)).X) :
    (F.obj (N.mk n)).X :=
  Pointed.Hom.toFun (F.map (N.pt p.2)) (Pointed.Hom.toFun φ p.1)

/-- The formula kills `{x₀} × n₊` (no hypothesis needed). -/
lemma extendFun_point_left (φ : X ⟶ F.obj (N.mk 1)) (n : ℕ)
    (b : (toPointed (N.mk n)).X) :
    extendFun φ n (X.point, b) = (F.obj (N.mk n)).point :=
  (congrArg (Pointed.Hom.toFun (F.map (N.pt b))) (Pointed.Hom.map_point φ)).trans
    (Pointed.Hom.map_point (F.map (N.pt b)))

/-- The formula kills `X × {0}` — *this* is where reducedness of `F` is used. -/
lemma extendFun_point_right (hF : Reduced F) (φ : X ⟶ F.obj (N.mk 1)) (n : ℕ) (a : X.X) :
    extendFun φ n (a, 0) = (F.obj n₊).point :=
  hF.map_pt_zero n (Pointed.Hom.toFun φ a)

/-- The level `n` component of the morphism of pre-Γ-sets extending `φ : X ⟶ F 1₊`. -/
def extendApp (hF : Reduced F) (φ : X ⟶ F.obj (N.mk 1)) (n : ℕ) :
    (S X).obj n₊ ⟶ F.obj n₊ where
  toFun := Smash.lift X (toPointed (N.mk n)) (extendFun φ n)
    (fun b => (extendFun_point_left φ n b).trans (extendFun_point_left φ n _).symm)
    (fun a => (extendFun_point_right hF φ n a).trans (extendFun_point_left φ n _).symm)
  map_point := extendFun_point_left φ n _

@[simp] lemma extendApp_mk (hF : Reduced F) (φ : X ⟶ F.obj (N.mk 1)) (n : ℕ)
    (p : X.X × (toPointed n₊).X) :
    Pointed.Hom.toFun (extendApp hF φ n) (Smash.mk X (toPointed n₊) p) = extendFun φ n p := rfl

/-- Naturality of `extendApp`, on an element. -/
lemma extendApp_naturality_apply (φ : X ⟶ F.obj (N.mk 1)) (n m : ℕ)
    (f : N.mk n ⟶ N.mk m) (a : X.X) (i : Fin (n + 1)) :
    extendFun φ m (a, Pointed.Hom.toFun f i)
      = Pointed.Hom.toFun (F.map f) (extendFun φ n (a, i)) :=
  map_pt_comp F i f (Pointed.Hom.toFun φ a)

/-- Naturality of `extendApp`.  Stated with `n m : ℕ`, so that `ofPt` below never computes with
an `N`-typed level. -/
lemma extendApp_naturality (hF : Reduced F) (φ : X ⟶ F.obj (N.mk 1)) (n m : ℕ)
    (f : N.mk n ⟶ N.mk m) :
    (S X).map f ≫ extendApp hF φ m = extendApp hF φ n ≫ F.map f := by
  apply Pointed.hom_ext'
  intro z
  refine Quotient.inductionOn z ?_
  rintro ⟨a, i⟩
  exact extendApp_naturality_apply φ n m f a i

/-- From a pointed map `φ : X ⟶ F 1₊`, the morphism of pre-Γ-sets `S X ⟶ F` given at level `n` by
`⟦x, i⟧ ↦ F (pt i) (φ x)`. -/
def ofPt (hF : Reduced F) (φ : X ⟶ F.obj (N.mk 1)) : S X ⟶ F where
  app n := extendApp hF φ n.as
  naturality := by
    intro n m f
    exact extendApp_naturality hF φ (N.as n) (N.as m) f

@[simp] lemma ofPt_app (hF : Reduced F) (φ : X ⟶ F.obj (N.mk 1)) (n : ℕ) :
    NatTrans.app (ofPt hF φ) (N.mk n) = extendApp hF φ n := rfl

/-! ### The two round trips -/

/-- `ofPt (toPt α) = α`, on an element: this is naturality of `α` along `pt i : 1₊ ⟶ n₊`. -/
lemma extendApp_toPt_apply (α : S X ⟶ F) (n : ℕ) (x : X.X) (i : Fin (n + 1)) :
    extendFun (toPt α) n (x, i)
      = Pointed.Hom.toFun (NatTrans.app α (N.mk n)) (Smash.mk X (toPointed n₊) (x, i)) := by
  -- `(S X) (pt i) ≫ α n = α 1 ≫ F (pt i)`, applied to `⟦x, 1⟧`
  have key := congrArg
    (fun g : (S X).obj (N.mk 1) ⟶ F.obj (N.mk n) =>
      Pointed.Hom.toFun g (Smash.mk X (toPointed 1₊) (x, (1 : Fin 2))))
    (NatTrans.naturality α (N.pt i))
  -- `(S X) (pt i) ⟦x, 1⟧ = ⟦x, i⟧`, since `ptFun i 1 = i`
  have h2 : Pointed.Hom.toFun ((S X).map (N.pt i))
      (Smash.mk X (toPointed 1₊) (x, (1 : Fin 2))) = Smash.mk X (toPointed n₊) (x, i) :=
    congrArg (fun j : Fin (n + 1) => Smash.mk X (toPointed n₊) (x, j)) (N.ptFun_one i)
  exact key.symm.trans (congrArg (Pointed.Hom.toFun (NatTrans.app α (N.mk n))) h2)

lemma extendApp_toPt (hF : Reduced F) (α : S X ⟶ F) (n : ℕ) :
    extendApp hF (toPt α) n = NatTrans.app α (N.mk n) := by
  apply Pointed.hom_ext'
  intro z
  refine Quotient.inductionOn z ?_
  rintro ⟨x, i⟩
  exact extendApp_toPt_apply α n x i

lemma toPt_ofPt (hF : Reduced F) (φ : X ⟶ F.obj (N.mk 1)) : toPt (ofPt hF φ) = φ := by
  apply Pointed.hom_ext'
  intro x
  -- `toPt (ofPt φ) x = F (pt 1) (φ x)` and `pt 1 = 𝟙`
  have hmap : F.map (N.pt (1 : Fin 2)) = 𝟙 (F.obj (N.mk 1)) :=
    (congrArg (fun g : N.mk 1 ⟶ N.mk 1 => F.map g) N.pt_one).trans (F.map_id (N.mk 1))
  exact congrArg
    (fun g : F.obj (N.mk 1) ⟶ F.obj (N.mk 1) =>
      Pointed.Hom.toFun g (Pointed.Hom.toFun φ x)) hmap

lemma ofPt_toPt (hF : Reduced F) (α : S X ⟶ F) : ofPt hF (toPt α) = α := by
  apply preGammaSet.hom_ext
  intro n
  exact extendApp_toPt hF α (N.unmk n)

lemma ofPt_comp_left {X' : Pointed.{0}} (hF : Reduced F) (f : X' ⟶ X)
    (φ : X ⟶ F.obj (N.mk 1)) : ofPt hF (f ≫ φ) = S.hMap f ≫ ofPt hF φ := by
  apply preGammaSet.hom_ext
  intro n
  apply Pointed.hom_ext'
  intro z
  refine Quotient.inductionOn z ?_
  rintro ⟨x, i⟩
  rfl

end Extend

/-! ## The adjunction -/

/-- **The hom-set bijection**: for a reduced pre-Γ-set `F`, morphisms `S X ⟶ F` correspond to
pointed maps `X ⟶ F 1₊`. -/
def homEquivOfReduced (X : Pointed.{0}) {F : N ⥤ Pointed.{0}} (hF : Reduced F) :
    (S X ⟶ F) ≃ (X ⟶ F.obj (N.mk 1)) where
  toFun := toPt
  invFun := ofPt hF
  left_inv := ofPt_toPt hF
  right_inv := toPt_ofPt hF

/-- **The adjunction**: the spherical functor is left adjoint to evaluation at level `1`. -/
def adj : Sph₀ ⊣ Ev₁ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X A => homEquivOfReduced X A.reduced
      homEquiv_naturality_left_symm := fun f φ => ofPt_comp_left _ f φ
      -- `toPt (α ≫ β) = toPt α ≫ β 1₊`: both send `x` to `β (α ⟦x, 1⟧)`.
      homEquiv_naturality_right := by
        intro X A A' α β
        apply Pointed.hom_ext'
        intro x
        rfl }

/-! ## Sanity checks -/

example (X : Pointed.{0}) : Ev₁.obj (Sph₀.obj X) = X ⋀ toPointed 1₊ := rfl

example (X : Pointed.{0}) (A : GammaSet) (φ : X ⟶ A.F.obj (N.mk 1)) (x : X.X)
    (n : ℕ) (i : Fin (n + 1)) :
    Pointed.Hom.toFun (NatTrans.app (ofPt A.reduced φ) (N.mk n))
        (Smash.mk X (toPointed n₊) (x, i))
      = Pointed.Hom.toFun (A.F.map (N.pt i)) (Pointed.Hom.toFun φ x) := rfl

end GammaSet
