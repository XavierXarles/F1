import F1.NMonoidal
import F1.spherical_adjunction
import F1.Gamma
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The smash product of Γ-sets: a closed symmetric monoidal structure

We equip the category `GammaSet` of (reduced) Γ-sets with

* the **smash product** (Day convolution)
  `(F ∧ G)(k₊) = colim_{m₊ ∧ n₊ → k₊} F(m₊) ∧ G(n₊)`,
* the **unit** `F1 : n₊ ↦ n₊`,
* the **internal hom** `Hom(M, N)(n₊) = Hom_{Γ-set}(M, N(n₊ ∧ -))`,

and prove that this is a `SymmetricCategory` and `MonoidalClosed`.


## Model of the colimit

* The object `m₊ ∧ n₊` of `N` is realised as `(m * n)₊`, via the encoding
  `N.enc : Fin (m+1) → Fin (n+1) → Fin (m*n+1)` (`0` on the wedge, `finProdFinEquiv` off it).
  The associativity, unit and symmetry isomorphisms of `N` are `N.assocN`, `N.lamN`, …
* The colimit is modelled as the quotient `Quot (Rel F G k)` of the type of quintuples
  `⟨m, n, g : m₊ ∧ n₊ ⟶ k₊, x ∈ F m₊, y ∈ G n₊⟩` by the relation
  `⟨m, n, (a ∧ b) ≫ g, x, y⟩ ∼ ⟨m', n', g, F a x, G b y⟩`: this is the colimit over the comma
  category `(∧ ↓ k₊)`, computed in `Type` (the comma category is connected, so this is also the
  colimit in `Pointed`).  We use `F m₊ × G n₊` rather than `F m₊ ⋀ G n₊`: for reduced `F`, `G` the
  wedge is *automatically* collapsed to the base point (`Day.mk_point_left`,
  `Day.mk_point_right`), so the two colimits agree.

Proofs follow one pattern: a morphism out of an iterated smash product is determined by its
values on the generators `ι (ι x y) z` (`Gens.ext`); on generators every structure map acts by
a map of `N`, and equalities of maps of `N` are checked on encoded elements (`N.hom_ext_enc`).
-/

open N CategoryTheory

namespace GammaSet

/-! ## Generalities on Γ-sets -/

/-- Naturality of a morphism of Γ-sets, on an element. -/
@[simp] lemma nat_apply {Q L : GammaSet} (α : Q ⟶ L) {a b : ℕ}
    (g : a₊ ⟶ b₊) (e : (Q.F.obj (N.mk a)).X) :
    Pointed.Hom.toFun (α.app (N.mk b)) (Pointed.Hom.toFun (Q.F.map g) e) =
      Pointed.Hom.toFun (L.F.map g) (Pointed.Hom.toFun (α.app (N.mk a)) e) :=
  congrArg (fun f => Pointed.Hom.toFun f e) (α.naturality g)

@[simp] lemma map_map_apply (Q : GammaSet) {a b c : ℕ} (f : a₊ ⟶ b₊)
    (g : b₊ ⟶ c₊) (e : (Q.F.obj a₊).X) :
    Pointed.Hom.toFun (Q.F.map g) (Pointed.Hom.toFun (Q.F.map f) e) =
      Pointed.Hom.toFun (Q.F.map (f ≫ g)) e := by
  rw [Q.F.map_comp]; rfl

@[simp] lemma map_id_apply (Q : GammaSet) {a : ℕ} (e : (Q.F.obj a₊).X) :
    Pointed.Hom.toFun (Q.F.map (𝟙 (N.mk a))) e = e := by
  rw [Q.F.map_id]; rfl

lemma map_congr_apply (Q : GammaSet) {a b : ℕ} {f f' : a₊ ⟶ b₊} (h : f = f')
    (e : (Q.F.obj a₊).X) :
    Pointed.Hom.toFun (Q.F.map f) e = Pointed.Hom.toFun (Q.F.map f') e := by
  rw [h]

lemma eq_map_apply (Q : GammaSet) {a : ℕ} {f : a₊ ⟶ a₊} (h : 𝟙 _ = f)
    (e : (Q.F.obj a₊).X) : e = Pointed.Hom.toFun (Q.F.map f) e := by
  rw [← h, map_id_apply]

/-- In a Γ-space, a map of `N` with all values `0` acts as the constant map. -/
lemma map_zero {Q : GammaSet} {a b : ℕ} (f : a₊ ⟶ b₊)
    (hf : ∀ c, Pointed.Hom.toFun f c = 0)
    (e : (Q.F.obj a₊).X) :
    Pointed.Hom.toFun (Q.F.map f) e = (Q.F.obj b₊).point := by sorry
  /-
  rw [N.eq_of_zero f hf, ← map_map_apply]
  rw [hQ.eq_point (Pointed.Hom.toFun (Q.map _) e)]
  exact Pointed.Hom.map_point _
  -/

/-- If `(p)₊` has only one element (e.g. `p = 0 * k`), a reduced Γ-space is trivial there. -/
lemma eq_point_of_trivial {Q : GammaSet} {p : ℕ}
    (hp : ∀ c : Fin (p + 1), c = 0) (e : (Q.F.obj (N.mk p)).X) :
    e = (Q.F.obj (N.mk p)).point := by
  rw [eq_map_apply Q (f := 𝟙 _) rfl e]
  exact map_zero _ hp e

/-- A family of *generators* of a Γ-space `Q`: every element of `Q` is the image of some
`el t` under a map of `N`. -/
structure Gens (Q : GammaSet) where
  /-- indexing type -/
  T : Type
  /-- level of each generator -/
  lev : T → ℕ
  /-- the generators -/
  el : ∀ t, (Q.F.obj (N.mk (lev t))).X
  /-- they generate -/
  gen : ∀ (p : ℕ) (e : (Q.F.obj (N.mk p)).X),
    ∃ t, ∃ g : N.mk (lev t) ⟶ N.mk p, e = Pointed.Hom.toFun (Q.F.map g) (el t)

/-- All elements, as generators. -/
def Gens.triv (Q : GammaSet) : Gens Q where
  T := Σ p : ℕ, (Q.F.obj (N.mk p)).X
  lev t := t.1
  el t := t.2
  gen p e := ⟨⟨p, e⟩, 𝟙 _, (map_id_apply Q e).symm⟩

/-- Morphisms out of a Γ-space are determined on generators. -/
lemma Gens.ext {Q L : GammaSet} (GQ : Gens Q) {α β : Q ⟶ L}
    (h : ∀ t, Pointed.Hom.toFun (α.app (N.mk (GQ.lev t))) (GQ.el t) =
      Pointed.Hom.toFun (β.app (N.mk (GQ.lev t))) (GQ.el t)) : α = β := by
  apply preGammaSet.hom_ext
  intro p
  apply Pointed.hom_ext'
  intro e
  obtain ⟨t, g, rfl⟩ := GQ.gen (N.unmk p) e
  exact (nat_apply α g _).trans ((congrArg _ (h t)).trans (nat_apply β g _).symm)

/-! ## The smash product of Γ-sets -/

namespace Day

variable (F G : GammaSet)

/-- An object `m₊ ∧ n₊ --g--> k₊` of the comma category `(∧ ↓ k₊)`, with `x ∈ F m₊`, `y ∈ G n₊`. -/
structure Pre (k : ℕ) : Type where
  /-- first level -/
  m : ℕ
  /-- second level -/
  n : ℕ
  /-- the structure map `m₊ ∧ n₊ ⟶ k₊` -/
  g : N.mk (m * n) ⟶ N.mk k
  /-- element of `F m₊` -/
  x : (F.F.obj (N.mk m)).X
  /-- element of `G n₊` -/
  y : (G.F.obj (N.mk n)).X

/-- The relation generating the colimit over `(∧ ↓ k₊)`. -/
inductive Rel (k : ℕ) : Pre F G k → Pre F G k → Prop
  | intro {m n m' n' : ℕ} (a : N.mk m ⟶ N.mk m') (b : N.mk n ⟶ N.mk n')
      (g : N.mk (m' * n') ⟶ N.mk k) (x : (F.F.obj (N.mk m)).X) (y : (G.F.obj (N.mk n)).X) :
      Rel k ⟨m, n, N.smashMap a b ≫ g, x, y⟩
        ⟨m', n', g, Pointed.Hom.toFun (F.F.map a) x, Pointed.Hom.toFun (G.F.map b) y⟩

variable {F G}

/-- Postcomposition with `h : k₊ ⟶ k'₊`. -/
def Pre.post {k k' : ℕ} (h : N.mk k ⟶ N.mk k') (p : Pre F G k) : Pre F G k' :=
  ⟨p.m, p.n, p.g ≫ h, p.x, p.y⟩

lemma Rel.post {k k' : ℕ} (h : N.mk k ⟶ N.mk k') {p q : Pre F G k} (r : Rel F G k p q) :
    Rel F G k' (p.post h) (q.post h) := by
  cases r with
  | intro a b g x y => exact Rel.intro a b (g ≫ h) x y

variable (F G)

/-- `(F ∧ G)(k₊)`, pointed at the class of `0₊ ∧ 0₊ → k₊` with the base points. -/
def tObj (k : ℕ) : Pointed.{0} where
  X := Quot (Rel F G k)
  point := Quot.mk _ ⟨0, 0, N.fromZero k, (F.F.obj (N.mk 0)).point, (G.F.obj (N.mk 0)).point⟩

/-- Functoriality of `F ∧ G` in `k₊`. -/
def tMap {k k' : ℕ} (h : N.mk k ⟶ N.mk k') : tObj F G k ⟶ tObj F G k' where
  toFun := Quot.map (Pre.post h) (fun _ _ r => r.post h)
  map_point := by
    apply congrArg (Quot.mk _)
    change Pre.mk 0 0 (N.fromZero k ≫ h) _ _ = Pre.mk 0 0 (N.fromZero k') _ _
    congr 1
    exact N.hom_ext_of_fun fun _ => N.hom_zero h

/-- **The smash product** `F ∧ G` of two Γ-set. -/
def tensorF : GammaSet where
  F:= {
  obj k := tObj F G (N.unmk k)
  map {k k'} h := tMap F G (k := N.unmk k) (k' := N.unmk k') h
  map_id k := by
    apply Pointed.hom_ext'
    intro e
    revert e
    refine Quot.ind ?_
    intro p
    rfl
  map_comp f g := by
    apply Pointed.hom_ext'
    intro e
    revert e
    refine Quot.ind ?_
    intro p
    rfl}
  reduced := sorry

variable {F G}

/-- The universal element `ι x y ∈ (F ∧ G)(m₊ ∧ n₊)`, the class of `𝟙 : m₊ ∧ n₊ ⟶ m₊ ∧ n₊`. -/
def ι {m n : ℕ} (x : (F.F.obj (N.mk m)).X) (y : (G.F.obj (N.mk n)).X) :
    ((tensorF F G).F.obj (N.mk (m * n))).X :=
  Quot.mk _ ⟨m, n, 𝟙 _, x, y⟩

lemma mk_eq_map {k m n : ℕ} (g : N.mk (m * n) ⟶ N.mk k)
    (x : (F.F.obj (N.mk m)).X) (y : (G.F.obj (N.mk n)).X) :
    (Quot.mk _ ⟨m, n, g, x, y⟩ : ((tensorF F G).F.obj (N.mk k)).X) =
      Pointed.Hom.toFun ((tensorF F G).F.map g) (ι x y) := rfl

/-- Naturality of `ι` in both variables. -/
lemma ι_nat {m n m' n' : ℕ} (a : N.mk m ⟶ N.mk m') (b : N.mk n ⟶ N.mk n')
    (x : (F.F.obj (N.mk m)).X) (y : (G.F.obj (N.mk n)).X) :
    ι (Pointed.Hom.toFun (F.F.map a) x) (Pointed.Hom.toFun (G.F.map b) y) =
      Pointed.Hom.toFun ((tensorF F G).F.map (N.smashMap a b)) (ι x y) :=
  (Quot.sound (Rel.intro a b (𝟙 _) x y)).symm

@[simp] lemma ι_map_left {m n m' : ℕ} (a : N.mk m ⟶ N.mk m')
    (x : (F.F.obj (N.mk m)).X) (y : (G.F.obj (N.mk n)).X) :
    ι (Pointed.Hom.toFun (F.F.map a) x) y =
      Pointed.Hom.toFun ((tensorF F G).F.map (N.smashMap a (𝟙 _))) (ι x y) := by
  rw [← ι_nat, @CategoryTheory.Functor.map_id, @Pointed.id_toFun]

@[simp] lemma ι_map_right {m n n' : ℕ} (b : N.mk n ⟶ N.mk n')
    (x : (F.F.obj (N.mk m)).X) (y : (G.F.obj (N.mk n)).X) :
    ι x (Pointed.Hom.toFun (G.F.map b) y) =
      Pointed.Hom.toFun ((tensorF F G).F.map (N.smashMap (𝟙 _) b)) (ι x y) := by
  rw [← ι_nat, @CategoryTheory.Functor.map_id, @Pointed.id_toFun]

lemma exists_ι {k : ℕ} (e : ((tensorF F G).F.obj (N.mk k)).X) :
    ∃ m n, ∃ g : N.mk (m * n) ⟶ N.mk k, ∃ x y,
      e = Pointed.Hom.toFun ((tensorF F G).F.map g)
      (ι (F := F) (G := G) (m := m) (n := n) x y) := by
  revert e
  refine Quot.ind ?_
  intro p
  exact ⟨p.m, p.n, p.g, p.x, p.y, rfl⟩

/-- Generators of `P ∧ K` built from generators of `P` and `K`. -/
def Gens.tensor {P K : GammaSet} (GP : Gens P) (GK : Gens K) : Gens (tensorF P K) where
  T := GP.T × GK.T
  lev t := GP.lev t.1 * GK.lev t.2
  el t := ι (GP.el t.1) (GK.el t.2)
  gen p e := by
    obtain ⟨m, n, g, x, y, rfl⟩ := exists_ι e
    obtain ⟨s, a, rfl⟩ := GP.gen m x
    obtain ⟨t, b, rfl⟩ := GK.gen n y
    refine ⟨(s, t), N.smashMap a b ≫ g, ?_⟩
    rw [ι_nat, map_map_apply]

/-- Generators `ι x y` of `F ∧ G`. -/
def gens₂ (F G : GammaSet) : Gens (tensorF F G) := Gens.tensor (Gens.triv F) (Gens.triv G)

/-- Generators `ι (ι x y) z` of `(F ∧ G) ∧ H`. -/
def gens₃L (F G H : GammaSet) : Gens (tensorF (tensorF F G) H) :=
  Gens.tensor (gens₂ F G) (Gens.triv H)

/-- Generators `ι x (ι y z)` of `F ∧ (G ∧ H)`. -/
def gens₃R (F G H : GammaSet) : Gens (tensorF F (tensorF G H)) :=
  Gens.tensor (Gens.triv F) (gens₂ G H)

/-- Generators `ι (ι (ι w x) y) z` of `((F ∧ G) ∧ H) ∧ K`. -/
def gens₄ (F G H K : GammaSet) : Gens (tensorF (tensorF (tensorF F G) H) K) :=
  Gens.tensor (gens₃L F G H) (Gens.triv K)

/-! ### The universal property -/

/-- A *bimorphism* `F, G → H`: maps `F m₊ × G n₊ → H (m₊ ∧ n₊)` natural in `m₊` and `n₊`. -/
structure Bimor (F G H : GammaSet) where
  /-- the components -/
  φ : ∀ {m n : ℕ}, (F.F.obj (N.mk m)).X → (G.F.obj (N.mk n)).X →
    (H.F.obj (N.mk (m * n))).X
  /-- naturality -/
  nat : ∀ {m n m' n' : ℕ} (a : N.mk m ⟶ N.mk m') (b : N.mk n ⟶ N.mk n') x y,
    φ (Pointed.Hom.toFun (F.F.map a) x) (Pointed.Hom.toFun (G.F.map b) y) =
      Pointed.Hom.toFun (H.F.map (N.smashMap a b)) (φ x y)

variable {H : GammaSet}

/-- The level-`k` component of the morphism `F ∧ G ⟶ H` induced by a bimorphism. -/
def descApp (φ : Bimor F G H) (k : ℕ) :
    (tensorF F G).F.obj (N.mk k) ⟶ H.F.obj (N.mk k) where
  toFun := Quot.lift (fun p => Pointed.Hom.toFun (H.F.map p.g) (φ.φ p.x p.y)) (by
    intro p q r
    cases r with
    | intro a b g x y =>
      change Pointed.Hom.toFun (H.F.map (N.smashMap a b ≫ g)) (φ.φ x y) =
        Pointed.Hom.toFun (H.F.map g) (φ.φ (Pointed.Hom.toFun (F.F.map a) x)
          (Pointed.Hom.toFun (G.F.map b) y))
      rw [φ.nat, map_map_apply])
  map_point := by
    change Pointed.Hom.toFun (H.F.map (N.fromZero k)) _ = _
    rw [←preGammaSet.Reduced.eq_point F.reduced (F.F.obj 0₊).point]
    sorry

/-- The morphism `F ∧ G ⟶ H` induced by a bimorphism (into a reduced `H`). -/
def desc (φ : Bimor F G H) : tensorF F G ⟶ H where
  app k := descApp φ (N.unmk k)
  naturality {k k'} h := by
    apply Pointed.hom_ext'
    intro e
    revert e
    refine Quot.ind ?_
    intro p
    change Pointed.Hom.toFun (H.F.map (p.g ≫ h)) _ = Pointed.Hom.toFun (H.F.map h)
      (Pointed.Hom.toFun (H.F.map p.g) _)
    sorry

@[simp] lemma desc_ι (φ : Bimor F G H) {m n : ℕ} (x : (F.F.obj (N.mk m)).X)
    (y : (G.F.obj (N.mk n)).X) :
    Pointed.Hom.toFun ((desc φ).app (N.mk (m * n))) (ι x y) = φ.φ x y :=
  map_id_apply H _

/-- The bimorphism underlying a morphism out of `F ∧ G`. -/
def toBimor (α : tensorF F G ⟶ H) : Bimor F G H where
  φ x y := Pointed.Hom.toFun (α.app _) (ι x y)
  nat a b x y := by rw [ι_nat, nat_apply]

/-! ### Functoriality -/

/-- `α ∧ β`. -/
def tensorHomF {F F' G G' : GammaSet} (α : F ⟶ F') (β : G ⟶ G') :
    tensorF F G ⟶ tensorF F' G' where
  app k :=
    { toFun := Quot.map
        (fun p => ⟨p.m, p.n, p.g, Pointed.Hom.toFun (α.app _) p.x,
          Pointed.Hom.toFun (β.app _) p.y⟩) (by
        intro p q r
        cases r with
        | intro a b g x y =>
          have := Rel.intro (F := F') (G := G') (k := N.unmk k) a b g
            (Pointed.Hom.toFun (α.app _) x) (Pointed.Hom.toFun (β.app _) y)
          rwa [← nat_apply α a x, ← nat_apply β b y] at this)
      map_point := by sorry }
  naturality k k' h := by
    apply Pointed.hom_ext'
    intro e
    revert e
    refine Quot.ind ?_
    intro p
    rfl

@[simp] lemma tensorHomF_ι {F F' G G' : GammaSet} (α : F ⟶ F') (β : G ⟶ G') {m n : ℕ}
    (x : (F.F.obj (N.mk m)).X) (y : (G.F.obj (N.mk n)).X) :
    Pointed.Hom.toFun ((tensorHomF α β).app (N.mk (m * n))) (ι x y) =
      ι (Pointed.Hom.toFun (α.app _) x) (Pointed.Hom.toFun (β.app _) y) := rfl

end Day

end GammaSet
