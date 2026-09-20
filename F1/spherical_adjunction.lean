import F1.spherical
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The spherical functor is left adjoint to evaluation at level `1`

**Warning.** `Sph ⊣ Ev` is *false* for `GammaSpace = N ⥤ Pointed` as defined in `F1.Gamma`:
if `F` is the constant functor at a pointed type `A`, then for any `α : S X ⟶ F` and any `x, i`,
naturality along the zero map `z : n₊ ⟶ n₊` gives
`α n ⟦x, i⟧ = α n ((id ⋀ z) ⟦x, i⟧) = α n (basepoint) = basepoint`,
so `Nat (S X, F)` is a single point while `Hom (X, F 1₊) = Hom (X, A)` is not.

The standard fix (Segal) is to restrict to *reduced* Γ-spaces, those with `F 0₊ = *`:

* `GammaSpace.Reduced F` : `F 0₊` has a single element;
* `RedGammaSpace`       : the category of reduced Γ-spaces;
* `GammaSpace.Sph₀ : Pointed ⥤ RedGammaSpace` : the spherical functor (`S X` *is* reduced);
* `GammaSpace.Ev₁ : RedGammaSpace ⥤ Pointed`  : evaluation at level `1`;
* `GammaSpace.adj : Sph₀ ⊣ Ev₁`.

Reducedness is used exactly once: `N.pt 0 : 1₊ ⟶ n₊` factors through `0₊`, so `F (pt 0)` is
constant at the basepoint; this is what lets the formula `⟦x, i⟧ ↦ F (pt i) (φ x)` descend from
`X × n₊` to the smash product `X ⋀ n₊`.

The unit of the adjunction is `x ↦ ⟦x, 1⟧ : X ⟶ X ⋀ 1₊` (`GammaSpace.unitMap`), and the counit at
level `n` is `⟦y, i⟧ ↦ F (pt i) y`.

Everything follows the discipline documented in `F1.spherical`: statements use `n m : ℕ` and
`N ⥤ Pointed.{0}`, all level implicits are explicit, `N.unmk` is used wherever a tactic produces
an `n : N`, and no category-level proof uses `rw` — `congrArg`, `Eq.trans` and `exact` need only
definitional equality, which is what crosses `N`/`ℕ` and `GammaSpace`/`N ⥤ Pointed` safely.
-/

universe u

open CategoryTheory Pointed

namespace GammaSpace

/-! ## Evaluation at level 1 -/

/-- Evaluation of a Γ-space at `1₊`. -/
def Ev : (N ⥤ Pointed.{0}) ⥤ Pointed.{0} where
  obj F := F.obj (N.mk 1)
  map α := NatTrans.app α (N.mk 1)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- … which is a functor `GammaSpace ⥤ Pointed`, definitionally. -/
def EvGamma : GammaSpace ⥤ Pointed.{0} := Ev

/-! ## Reduced Γ-spaces -/

/-- A Γ-space is *reduced* when `F 0₊` is a single point. -/
def Reduced (F : N ⥤ Pointed.{0}) : Prop :=
  ∀ x : (F.obj (N.mk 0)).X, x = (F.obj (N.mk 0)).point

/-- Unfolding of `Reduced`, so that `hF` is never applied through the definition. -/
theorem Reduced.eq_point {F : N ⥤ Pointed.{0}} (hF : Reduced F) (x : (F.obj (N.mk 0)).X) :
    x = (F.obj (N.mk 0)).point := hF x

/-- For a reduced Γ-space the map induced by `pt 0 : 1₊ ⟶ n₊` (the zero map) is constant at the
basepoint, since it factors through `F 0₊ = *`. -/
theorem Reduced.map_pt_zero {F : N ⥤ Pointed.{0}} (hF : Reduced F) (n : ℕ)
    (y : (F.obj (N.mk 1)).X) :
    Pointed.Hom.toFun (F.map (N.pt (n := n) (0 : Fin (n + 1)))) y = (F.obj (N.mk n)).point := by
  -- `F (pt 0) = F (fromZero) ∘ F (toZero)`
  have hmap : F.map (N.pt (n := n) (0 : Fin (n + 1)))
      = F.map (N.toZero 1) ≫ F.map (N.fromZero n) :=
    (congrArg (fun g : N.mk 1 ⟶ N.mk n => F.map g) (N.pt_zero n)).trans
      (F.map_comp (N.toZero 1) (N.fromZero n))
  have h1 : Pointed.Hom.toFun (F.map (N.pt (n := n) (0 : Fin (n + 1)))) y
      = Pointed.Hom.toFun (F.map (N.fromZero n))
          (Pointed.Hom.toFun (F.map (N.toZero 1)) y) :=
    congrArg (fun g : F.obj (N.mk 1) ⟶ F.obj (N.mk n) => Pointed.Hom.toFun g y) hmap
  -- the inner value lives in `F 0₊`, hence is the basepoint
  exact h1.trans ((congrArg (Pointed.Hom.toFun (F.map (N.fromZero n)))
      (hF.eq_point (Pointed.Hom.toFun (F.map (N.toZero 1)) y))).trans
    (Pointed.Hom.map_point (F.map (N.fromZero n))))

/-- Functoriality along `pt`: `F (pt (f i)) = F f ∘ F (pt i)`. -/
theorem map_pt_comp (F : N ⥤ Pointed.{0}) {n m : ℕ} (i : Fin (n + 1))
    (f : N.mk n ⟶ N.mk m) (y : (F.obj (N.mk 1)).X) :
    Pointed.Hom.toFun (F.map (N.pt (n := m) (Pointed.Hom.toFun f i))) y
      = Pointed.Hom.toFun (F.map f) (Pointed.Hom.toFun (F.map (N.pt (n := n) i)) y) := by
  have hmap : F.map (N.pt (n := m) (Pointed.Hom.toFun f i))
      = F.map (N.pt (n := n) i) ≫ F.map f :=
    (congrArg (fun g : N.mk 1 ⟶ N.mk m => F.map g) (N.pt_comp i f).symm).trans
      (F.map_comp (N.pt (n := n) i) f)
  exact congrArg (fun g : F.obj (N.mk 1) ⟶ F.obj (N.mk m) => Pointed.Hom.toFun g y) hmap

/-- The spherical Γ-space is reduced: `X ⋀ 0₊ = *`. -/
theorem S_reduced (X : Pointed.{0}) : Reduced (S X) := by
  intro x
  refine Quotient.inductionOn x ?_
  rintro ⟨a, i⟩
  exact Smash.eq_point_of_isWedge X (PointedFin 0) (Or.inr (N.fin1_eq_zero i))

end GammaSpace

/-- The category of reduced Γ-spaces: a full subcategory of `GammaSpace`, spelled out by hand
(in the same style as `N`). -/
structure RedGammaSpace where
  /-- the underlying Γ-space -/
  F : N ⥤ Pointed.{0}
  /-- the reducedness condition `F 0₊ = *` -/
  reduced : GammaSpace.Reduced F

namespace RedGammaSpace

instance : Category RedGammaSpace where
  Hom A B := A.F ⟶ B.F
  id A := 𝟙 A.F
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- The inclusion of reduced Γ-spaces into all Γ-spaces. -/
def incl : RedGammaSpace ⥤ (N ⥤ Pointed.{0}) where
  obj A := A.F
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

end RedGammaSpace

namespace GammaSpace

/-- Evaluation at level `1`, on reduced Γ-spaces. -/
def Ev₁ : RedGammaSpace ⥤ Pointed.{0} := RedGammaSpace.incl ⋙ Ev

/-- The spherical functor, viewed as landing in reduced Γ-spaces. -/
def Sph₀ : Pointed.{0} ⥤ RedGammaSpace where
  obj X := ⟨S X, S_reduced X⟩
  map h := S.hMap h
  map_id X := S.hMap_id X
  map_comp f g := S.hMap_comp f g

@[simp] lemma Ev₁_obj (A : RedGammaSpace) : Ev₁.obj A = A.F.obj (N.mk 1) := rfl

@[simp] lemma Ev₁_map {A B : RedGammaSpace} (α : A ⟶ B) :
    Ev₁.map α = NatTrans.app α (N.mk 1) := rfl

/-! ## The two directions of the bijection -/

/-- The unit map `X ⟶ X ⋀ 1₊`, `x ↦ ⟦x, 1⟧`.  (It is in fact an isomorphism.) -/
def unitMap (X : Pointed.{0}) : X ⟶ X ⋀ (PointedFin 1) where
  toFun x := Smash.mk X (PointedFin 1) (x, (1 : Fin 2))
  map_point := Smash.mk_point_left X (PointedFin 1) (1 : Fin 2)

/-- From a morphism of Γ-spaces `S X ⟶ F`, the pointed map `X ⟶ F 1₊`: evaluate at level `1`
and precompose with the unit. -/
def toPt {X : Pointed.{0}} {F : N ⥤ Pointed.{0}} (α : S X ⟶ F) : X ⟶ F.obj (N.mk 1) :=
  unitMap X ≫ NatTrans.app α (N.mk 1)

section Extend

variable {X : Pointed.{0}} {F : N ⥤ Pointed.{0}}

/-- The formula `(x, i) ↦ F (pt i) (φ x)` on `X × n₊`, which will descend to `X ⋀ n₊`. -/
def extendFun (φ : X ⟶ F.obj (N.mk 1)) (n : ℕ) (p : X.X × (PointedFin n).X) :
    (F.obj (N.mk n)).X :=
  Pointed.Hom.toFun (F.map (N.pt (n := n) p.2)) (Pointed.Hom.toFun φ p.1)

/-- The formula kills `{x₀} × n₊` (no hypothesis needed). -/
lemma extendFun_point_left (φ : X ⟶ F.obj (N.mk 1)) (n : ℕ) (b : (PointedFin n).X) :
    extendFun φ n (X.point, b) = (F.obj (N.mk n)).point :=
  (congrArg (Pointed.Hom.toFun (F.map (N.pt (n := n) b))) (Pointed.Hom.map_point φ)).trans
    (Pointed.Hom.map_point (F.map (N.pt (n := n) b)))

/-- The formula kills `X × {0}` — *this* is where reducedness of `F` is used. -/
lemma extendFun_point_right (hF : Reduced F) (φ : X ⟶ F.obj (N.mk 1)) (n : ℕ) (a : X.X) :
    extendFun φ n (a, (PointedFin n).point) = (F.obj (N.mk n)).point :=
  hF.map_pt_zero n (Pointed.Hom.toFun φ a)

/-- The level `n` component of the morphism of Γ-spaces extending `φ : X ⟶ F 1₊`. -/
def extendApp (hF : Reduced F) (φ : X ⟶ F.obj (N.mk 1)) (n : ℕ) :
    (S X).obj (N.mk n) ⟶ F.obj (N.mk n) where
  toFun := Smash.lift X (PointedFin n) (extendFun φ n)
    (fun b => (extendFun_point_left φ n b).trans (extendFun_point_left φ n _).symm)
    (fun a => (extendFun_point_right hF φ n a).trans (extendFun_point_left φ n _).symm)
  map_point := extendFun_point_left φ n _

@[simp] lemma extendApp_mk (hF : Reduced F) (φ : X ⟶ F.obj (N.mk 1)) (n : ℕ)
    (p : X.X × (PointedFin n).X) :
    Pointed.Hom.toFun (extendApp hF φ n) (Smash.mk X (PointedFin n) p) = extendFun φ n p := rfl

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

/-- From a pointed map `φ : X ⟶ F 1₊`, the morphism of Γ-spaces `S X ⟶ F` given at level `n` by
`⟦x, i⟧ ↦ F (pt i) (φ x)`. -/
def ofPt (hF : Reduced F) (φ : X ⟶ F.obj (N.mk 1)) : S X ⟶ F where
  app n := extendApp hF φ (N.unmk n)
  naturality := by
    intro n m f
    exact extendApp_naturality hF φ (N.unmk n) (N.unmk m) f

@[simp] lemma ofPt_app (hF : Reduced F) (φ : X ⟶ F.obj (N.mk 1)) (n : ℕ) :
    NatTrans.app (ofPt hF φ) (N.mk n) = extendApp hF φ n := rfl

/-! ### The two round trips -/

/-- `ofPt (toPt α) = α`, on an element: this is naturality of `α` along `pt i : 1₊ ⟶ n₊`. -/
lemma extendApp_toPt_apply (α : S X ⟶ F) (n : ℕ) (x : X.X) (i : Fin (n + 1)) :
    extendFun (toPt α) n (x, i)
      = Pointed.Hom.toFun (NatTrans.app α (N.mk n)) (Smash.mk X (PointedFin n) (x, i)) := by
  -- `(S X) (pt i) ≫ α n = α 1 ≫ F (pt i)`, applied to `⟦x, 1⟧`
  have key := congrArg
    (fun g : (S X).obj (N.mk 1) ⟶ F.obj (N.mk n) =>
      Pointed.Hom.toFun g (Smash.mk X (PointedFin 1) (x, (1 : Fin 2))))
    (NatTrans.naturality α (N.pt (n := n) i))
  -- `(S X) (pt i) ⟦x, 1⟧ = ⟦x, i⟧`, since `ptFun i 1 = i`
  have h2 : Pointed.Hom.toFun ((S X).map (N.pt (n := n) i))
      (Smash.mk X (PointedFin 1) (x, (1 : Fin 2))) = Smash.mk X (PointedFin n) (x, i) :=
    congrArg (fun j : Fin (n + 1) => Smash.mk X (PointedFin n) (x, j)) (N.ptFun_one i)
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
  have hmap : F.map (N.pt (n := 1) (1 : Fin 2)) = 𝟙 (F.obj (N.mk 1)) :=
    (congrArg (fun g : N.mk 1 ⟶ N.mk 1 => F.map g) N.pt_one).trans (F.map_id (N.mk 1))
  exact congrArg
    (fun g : F.obj (N.mk 1) ⟶ F.obj (N.mk 1) =>
      Pointed.Hom.toFun g (Pointed.Hom.toFun φ x)) hmap

lemma ofPt_toPt (hF : Reduced F) (α : S X ⟶ F) : ofPt hF (toPt α) = α := by
  apply GammaSpace.hom_ext
  intro n
  exact extendApp_toPt hF α (N.unmk n)

lemma ofPt_comp_left {X' : Pointed.{0}} (hF : Reduced F) (f : X' ⟶ X)
    (φ : X ⟶ F.obj (N.mk 1)) : ofPt hF (f ≫ φ) = S.hMap f ≫ ofPt hF φ := by
  apply GammaSpace.hom_ext
  intro n
  apply Pointed.hom_ext'
  intro z
  refine Quotient.inductionOn z ?_
  rintro ⟨x, i⟩
  rfl

end Extend

/-! ## The adjunction -/

/-- **The hom-set bijection**: for a reduced Γ-space `F`, morphisms of Γ-spaces `S X ⟶ F`
correspond to pointed maps `X ⟶ F 1₊`. -/
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

example (X : Pointed.{0}) : Ev₁.obj (Sph₀.obj X) = X ⋀ PointedFin 1 := rfl

example (X : Pointed.{0}) (A : RedGammaSpace) (φ : X ⟶ A.F.obj (N.mk 1)) (x : X.X)
    (n : ℕ) (i : Fin (n + 1)) :
    Pointed.Hom.toFun (NatTrans.app (ofPt A.reduced φ) (N.mk n))
        (Smash.mk X (PointedFin n) (x, i))
      = Pointed.Hom.toFun (A.F.map (N.pt (n := n) i)) (Pointed.Hom.toFun φ x) := rfl

end GammaSpace
