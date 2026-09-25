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
    Pointed.Hom.toFun (Q.F.map f) e = (Q.F.obj b₊).point := by
  rw [N.eq_of_zero f hf, ← map_map_apply,
    Q.reduced.eq_point (Pointed.Hom.toFun (Q.F.map (N.toZero a)) e)]
  exact Pointed.Hom.map_point _

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
  reduced := by
    -- Every `⟨m, n, g, x, y⟩` over `0₊` is related to `⟨0, 0, 𝟙, F(0) x, G(0) y⟩`, since `g` is
    -- the unique map to `0₊` and hence factors as `(toZero m ∧ toZero n) ≫ 𝟙`; the latter is the
    -- base point because `F` and `G` are reduced.
    intro e
    revert e
    refine Quot.ind ?_
    rintro ⟨m, n, g, x, y⟩
    have hg : g = N.smashMap (N.toZero m) (N.toZero n) ≫ N.fromZero 0 :=
      N.hom_ext_of_fun fun c => (N.fin1_eq_zero _).trans (N.fin1_eq_zero _).symm
    subst hg
    refine (Quot.sound (Rel.intro (N.toZero m) (N.toZero n) (N.fromZero 0) x y)).trans ?_
    rw [F.reduced.eq_point (Pointed.Hom.toFun (F.F.map (N.toZero m)) x),
      G.reduced.eq_point (Pointed.Hom.toFun (G.F.map (N.toZero n)) y)]
    rfl

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
    -- `φ` of the base points lives in `H 0₊ = *`, and `H (fromZero k)` is pointed.
    have h := H.reduced.eq_point (φ.φ (F.F.obj (N.mk 0)).point (G.F.obj (N.mk 0)).point)
    exact (congrArg (Pointed.Hom.toFun (H.F.map (N.fromZero k))) h).trans
      (Pointed.Hom.map_point _)

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
    exact (map_map_apply H p.g h _).symm

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
      map_point := by
        apply congrArg (Quot.mk _)
        change Pre.mk 0 0 _ (Pointed.Hom.toFun (α.app (N.mk 0)) (F.F.obj (N.mk 0)).point)
            (Pointed.Hom.toFun (β.app (N.mk 0)) (G.F.obj (N.mk 0)).point) = Pre.mk 0 0 _ _ _
        rw [Pointed.Hom.map_point, Pointed.Hom.map_point] }
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

/-! ### Basic identities for `tensorHomF` -/

@[simp] lemma comp_app_apply {Q L M : GammaSet} (α : Q ⟶ L) (β : L ⟶ M) (k : N)
    (e : (Q.F.obj k).X) :
    Pointed.Hom.toFun ((α ≫ β : Q ⟶ M).app k) e =
      Pointed.Hom.toFun (β.app k) (Pointed.Hom.toFun (α.app k) e) := rfl

@[simp] lemma id_app_apply (Q : GammaSet) (k : N) (e : (Q.F.obj k).X) :
    Pointed.Hom.toFun ((𝟙 Q : Q ⟶ Q).app k) e = e := rfl

lemma tensorHomF_id (F G : GammaSet) : tensorHomF (𝟙 F) (𝟙 G) = 𝟙 (tensorF F G) := by
  apply preGammaSet.hom_ext
  intro k
  apply Pointed.hom_ext'
  intro e
  revert e
  refine Quot.ind ?_
  intro p
  rfl

lemma tensorHomF_comp {F₁ F₂ F₃ G₁ G₂ G₃ : GammaSet} (f₁ : F₁ ⟶ F₂) (g₁ : F₂ ⟶ F₃)
    (f₂ : G₁ ⟶ G₂) (g₂ : G₂ ⟶ G₃) :
    tensorHomF f₁ f₂ ≫ tensorHomF g₁ g₂ = tensorHomF (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  apply preGammaSet.hom_ext
  intro k
  apply Pointed.hom_ext'
  intro e
  revert e
  refine Quot.ind ?_
  intro p
  rfl

/-- A map of `N` equal to the identity acts trivially. -/
lemma map_eq_self (Q : GammaSet) {a : ℕ} {f : a₊ ⟶ a₊} (h : f = 𝟙 _)
    (e : (Q.F.obj a₊).X) : Pointed.Hom.toFun (Q.F.map f) e = e := by
  rw [h, map_id_apply]

/-- The computational half of `enc_ext`: after `apply N.hom_ext_enc; intro i j` (and any
decomposition of `i`, `j` as encodings), simplify both sides and split on `if`s. -/
macro "enc_fin" : tactic => `(tactic| (
  simp only [N.comp_toFun, N.id_toFun, N.smashMap_enc, N.assocN_enc, N.assocInvN_enc,
    N.lamN_enc, N.rhoN_enc, N.swapN_enc, N.incL_toFun, N.incR_toFun, N.pt_toFun,
    N.ofFun_toFun, N.hom_zero, N.enc_zero_left, N.enc_zero_right]
  try (split_ifs <;> simp_all)))

/-! ### The wedge is collapsed -/

/-- An element whose second coordinate is the base point is the base point. -/
lemma mk_point_right {k m n : ℕ} (g : N.mk (m * n) ⟶ N.mk k) (x : (F.F.obj (N.mk m)).X) :
    (Quot.mk _ ⟨m, n, g, x, (G.F.obj (N.mk n)).point⟩ : ((tensorF F G).F.obj (N.mk k)).X) =
      ((tensorF F G).F.obj (N.mk k)).point := by
  have hg : N.smashMap (𝟙 (N.mk m)) (N.fromZero n) ≫ g =
      N.smashMap (N.toZero m) (𝟙 (N.mk 0)) ≫ N.fromZero k := by
    apply N.hom_ext_enc
    intro i j
    rw [N.fin1_eq_zero j]
    simp
  have h1 := Quot.sound (Rel.intro (𝟙 (N.mk m)) (N.fromZero n) g x (G.F.obj (N.mk 0)).point)
  have h2 := Quot.sound (Rel.intro (N.toZero m) (𝟙 (N.mk 0)) (N.fromZero k) x
    (G.F.obj (N.mk 0)).point)
  rw [map_id_apply, Pointed.Hom.map_point] at h1
  rw [map_id_apply, F.reduced.eq_point (Pointed.Hom.toFun (F.F.map (N.toZero m)) x)] at h2
  refine h1.symm.trans ?_
  rw [hg]
  exact h2

/-- An element whose first coordinate is the base point is the base point. -/
lemma mk_point_left {k m n : ℕ} (g : N.mk (m * n) ⟶ N.mk k) (y : (G.F.obj (N.mk n)).X) :
    (Quot.mk _ ⟨m, n, g, (F.F.obj (N.mk m)).point, y⟩ : ((tensorF F G).F.obj (N.mk k)).X) =
      ((tensorF F G).F.obj (N.mk k)).point := by
  have hg : N.smashMap (N.fromZero m) (𝟙 (N.mk n)) ≫ g =
      N.smashMap (𝟙 (N.mk 0)) (N.toZero n) ≫ N.fromZero k := by
    apply N.hom_ext_enc
    intro i j
    rw [N.fin1_eq_zero i]
    simp
  have h1 := Quot.sound (Rel.intro (N.fromZero m) (𝟙 (N.mk n)) g (F.F.obj (N.mk 0)).point y)
  have h2 := Quot.sound (Rel.intro (𝟙 (N.mk 0)) (N.toZero n) (N.fromZero k)
    (F.F.obj (N.mk 0)).point y)
  rw [map_id_apply, Pointed.Hom.map_point] at h1
  rw [map_id_apply, G.reduced.eq_point (Pointed.Hom.toFun (G.F.map (N.toZero n)) y)] at h2
  refine h1.symm.trans ?_
  rw [hg]
  exact h2

@[simp] lemma ι_point_right {m n : ℕ} (x : (F.F.obj (N.mk m)).X) :
    ι (F := F) (G := G) x (G.F.obj (N.mk n)).point = ((tensorF F G).F.obj (N.mk (m * n))).point :=
  mk_point_right _ _

@[simp] lemma ι_point_left {m n : ℕ} (y : (G.F.obj (N.mk n)).X) :
    ι (F := F) (G := G) (F.F.obj (N.mk m)).point y = ((tensorF F G).F.obj (N.mk (m * n))).point :=
  mk_point_left _ _

/-! ### Trimorphisms and maps out of triple smash products -/

/-- A trimorphism `F, G, H → K`, with values in `K ((m₊ ∧ n₊) ∧ q₊)`. -/
structure TrimorL (F G H K : GammaSet) where
  /-- the components -/
  ψ : ∀ {m n q : ℕ}, (F.F.obj (N.mk m)).X → (G.F.obj (N.mk n)).X →
    (H.F.obj (N.mk q)).X → (K.F.obj (N.mk (m * n * q))).X
  /-- naturality -/
  nat : ∀ {m n q m' n' q' : ℕ} (a : N.mk m ⟶ N.mk m') (b : N.mk n ⟶ N.mk n')
    (c : N.mk q ⟶ N.mk q') x y z,
    ψ (Pointed.Hom.toFun (F.F.map a) x) (Pointed.Hom.toFun (G.F.map b) y)
        (Pointed.Hom.toFun (H.F.map c) z) =
      Pointed.Hom.toFun (K.F.map (N.smashMap (N.smashMap a b) c)) (ψ x y z)

/-- A trimorphism `F, G, H → K`, with values in `K (m₊ ∧ (n₊ ∧ q₊))`. -/
structure TrimorR (F G H K : GammaSet) where
  /-- the components -/
  ψ : ∀ {m n q : ℕ}, (F.F.obj (N.mk m)).X → (G.F.obj (N.mk n)).X →
    (H.F.obj (N.mk q)).X → (K.F.obj (N.mk (m * (n * q)))).X
  /-- naturality -/
  nat : ∀ {m n q m' n' q' : ℕ} (a : N.mk m ⟶ N.mk m') (b : N.mk n ⟶ N.mk n')
    (c : N.mk q ⟶ N.mk q') x y z,
    ψ (Pointed.Hom.toFun (F.F.map a) x) (Pointed.Hom.toFun (G.F.map b) y)
        (Pointed.Hom.toFun (H.F.map c) z) =
      Pointed.Hom.toFun (K.F.map (N.smashMap a (N.smashMap b c))) (ψ x y z)

variable {K : GammaSet}

/-- The bimorphism `F ∧ G, H → K` induced by a trimorphism. -/
def TrimorL.bimor (ψ : TrimorL F G H K) : Bimor (tensorF F G) H K where
  φ {k q} e z := Quot.lift
    (fun p => Pointed.Hom.toFun (K.F.map (N.smashMap p.g (𝟙 (N.mk q)))) (ψ.ψ p.x p.y z))
    (by
      intro p p' r
      cases r with
      | intro a b g x y =>
        change Pointed.Hom.toFun (K.F.map (N.smashMap (N.smashMap a b ≫ g) (𝟙 _))) _ =
          Pointed.Hom.toFun (K.F.map (N.smashMap g (𝟙 _)))
            (ψ.ψ (Pointed.Hom.toFun (F.F.map a) x) (Pointed.Hom.toFun (G.F.map b) y) z)
        have h := ψ.nat a b (𝟙 _) x y z
        rw [map_id_apply] at h
        rw [h, map_map_apply]
        apply map_congr_apply
        apply N.hom_ext_enc
        intro i j
        obtain ⟨i, i', rfl⟩ := N.enc_surj i
        enc_fin) e
  nat {k q k' q'} a c e z := by
    revert e
    refine Quot.ind (fun (p : Pre F G k) => ?_)
    change Pointed.Hom.toFun (K.F.map (N.smashMap (p.g ≫ a) (𝟙 _)))
        (ψ.ψ p.x p.y (Pointed.Hom.toFun (H.F.map c) z)) =
      Pointed.Hom.toFun (K.F.map (N.smashMap a c))
        (Pointed.Hom.toFun (K.F.map (N.smashMap p.g (𝟙 _))) (ψ.ψ p.x p.y z))
    have h := ψ.nat (𝟙 _) (𝟙 _) c p.x p.y z
    rw [map_id_apply, map_id_apply] at h
    rw [h, map_map_apply, map_map_apply]
    apply map_congr_apply
    apply N.hom_ext_enc
    intro i j
    obtain ⟨i, i', rfl⟩ := N.enc_surj i
    enc_fin

/-- The bimorphism `F, G ∧ H → K` induced by a trimorphism. -/
def TrimorR.bimor (ψ : TrimorR F G H K) : Bimor F (tensorF G H) K where
  φ {m k} x e := Quot.lift
    (fun p => Pointed.Hom.toFun (K.F.map (N.smashMap (𝟙 (N.mk m)) p.g)) (ψ.ψ x p.x p.y))
    (by
      intro p p' r
      cases r with
      | intro a b g y z =>
        change Pointed.Hom.toFun (K.F.map (N.smashMap (𝟙 _) (N.smashMap a b ≫ g))) _ =
          Pointed.Hom.toFun (K.F.map (N.smashMap (𝟙 _) g))
            (ψ.ψ x (Pointed.Hom.toFun (G.F.map a) y) (Pointed.Hom.toFun (H.F.map b) z))
        have h := ψ.nat (𝟙 _) a b x y z
        rw [map_id_apply] at h
        rw [h, map_map_apply]
        apply map_congr_apply
        apply N.hom_ext_enc
        intro i j
        obtain ⟨j, j', rfl⟩ := N.enc_surj j
        enc_fin) e
  nat {m k m' k'} a c x e := by
    revert e
    refine Quot.ind (fun (p : Pre G H k) => ?_)
    change Pointed.Hom.toFun (K.F.map (N.smashMap (𝟙 _) (p.g ≫ c)))
        (ψ.ψ (Pointed.Hom.toFun (F.F.map a) x) p.x p.y) =
      Pointed.Hom.toFun (K.F.map (N.smashMap a c))
        (Pointed.Hom.toFun (K.F.map (N.smashMap (𝟙 _) p.g)) (ψ.ψ x p.x p.y))
    have h := ψ.nat a (𝟙 _) (𝟙 _) x p.x p.y
    rw [map_id_apply, map_id_apply] at h
    rw [h, map_map_apply, map_map_apply]
    apply map_congr_apply
    apply N.hom_ext_enc
    intro i j
    obtain ⟨j, j', rfl⟩ := N.enc_surj j
    enc_fin

/-- The morphism `(F ∧ G) ∧ H ⟶ K` induced by a trimorphism. -/
def descL (ψ : TrimorL F G H K) : tensorF (tensorF F G) H ⟶ K := desc ψ.bimor

/-- The morphism `F ∧ (G ∧ H) ⟶ K` induced by a trimorphism. -/
def descR (ψ : TrimorR F G H K) : tensorF F (tensorF G H) ⟶ K := desc ψ.bimor

lemma descL_ι (ψ : TrimorL F G H K) {m n q : ℕ} (x : (F.F.obj (N.mk m)).X)
    (y : (G.F.obj (N.mk n)).X) (z : (H.F.obj (N.mk q)).X) :
    Pointed.Hom.toFun ((descL ψ).app (N.mk (m * n * q))) (ι (ι x y) z) = ψ.ψ x y z := by
  rw [descL, desc_ι]
  change Pointed.Hom.toFun (K.F.map (N.smashMap (𝟙 _) (𝟙 _))) (ψ.ψ x y z) = _
  rw [N.smashMap_id, map_id_apply]

lemma descR_ι (ψ : TrimorR F G H K) {m n q : ℕ} (x : (F.F.obj (N.mk m)).X)
    (y : (G.F.obj (N.mk n)).X) (z : (H.F.obj (N.mk q)).X) :
    Pointed.Hom.toFun ((descR ψ).app (N.mk (m * (n * q)))) (ι x (ι y z)) = ψ.ψ x y z := by
  rw [descR, desc_ι]
  change Pointed.Hom.toFun (K.F.map (N.smashMap (𝟙 _) (𝟙 _))) (ψ.ψ x y z) = _
  rw [N.smashMap_id, map_id_apply]

/-! ### The associator -/

variable (F G H)

/-- `x, y, z ↦ ι x (ι y z)`, transported to `(m₊ ∧ n₊) ∧ q₊`. -/
def assocHomT : TrimorL F G H (tensorF F (tensorF G H)) where
  ψ x y z := Pointed.Hom.toFun ((tensorF F (tensorF G H)).F.map (N.assocInvN _ _ _)) (ι x (ι y z))
  nat a b c x y z := by
    rw [ι_nat b c, ι_nat a (N.smashMap b c), map_map_apply, map_map_apply]
    apply map_congr_apply
    apply N.hom_ext_enc
    intro i j
    obtain ⟨j, j', rfl⟩ := N.enc_surj j
    enc_fin

/-- `x, y, z ↦ ι (ι x y) z`, transported to `m₊ ∧ (n₊ ∧ q₊)`. -/
def assocInvT : TrimorR F G H (tensorF (tensorF F G) H) where
  ψ x y z := Pointed.Hom.toFun ((tensorF (tensorF F G) H).F.map (N.assocN _ _ _)) (ι (ι x y) z)
  nat a b c x y z := by
    rw [ι_nat a b, ι_nat (N.smashMap a b) c, map_map_apply, map_map_apply]
    apply map_congr_apply
    apply N.hom_ext_enc
    intro i j
    obtain ⟨i, i', rfl⟩ := N.enc_surj i
    enc_fin

variable {F G H}

@[simp] lemma assocHom_ι {m n q : ℕ} (x : (F.F.obj (N.mk m)).X)
    (y : (G.F.obj (N.mk n)).X) (z : (H.F.obj (N.mk q)).X) :
    Pointed.Hom.toFun ((descL (assocHomT F G H)).app (N.mk (m * n * q))) (ι (ι x y) z) =
      Pointed.Hom.toFun ((tensorF F (tensorF G H)).F.map (N.assocInvN m n q)) (ι x (ι y z)) :=
  descL_ι _ x y z

@[simp] lemma assocInv_ι {m n q : ℕ} (x : (F.F.obj (N.mk m)).X)
    (y : (G.F.obj (N.mk n)).X) (z : (H.F.obj (N.mk q)).X) :
    Pointed.Hom.toFun ((descR (assocInvT F G H)).app (N.mk (m * (n * q)))) (ι x (ι y z)) =
      Pointed.Hom.toFun ((tensorF (tensorF F G) H).F.map (N.assocN m n q)) (ι (ι x y) z) :=
  descR_ι _ x y z

variable (F G H)

/-- **The associator** `(F ∧ G) ∧ H ≅ F ∧ (G ∧ H)`. -/
def associator : tensorF (tensorF F G) H ≅ tensorF F (tensorF G H) where
  hom := descL (assocHomT F G H)
  inv := descR (assocInvT F G H)
  hom_inv_id := by
    apply Gens.ext (gens₃L F G H)
    rintro ⟨⟨⟨m, x⟩, ⟨n, y⟩⟩, ⟨q, z⟩⟩
    dsimp only [gens₃L, gens₂, Gens.tensor, Gens.triv]
    simp only [comp_app_apply, id_app_apply, assocHom_ι, nat_apply, assocInv_ι, map_map_apply]
    apply map_eq_self
    apply N.hom_ext_enc
    intro i j
    obtain ⟨i, i', rfl⟩ := N.enc_surj i
    enc_fin
  inv_hom_id := by
    apply Gens.ext (gens₃R F G H)
    rintro ⟨⟨m, x⟩, ⟨⟨n, y⟩, ⟨q, z⟩⟩⟩
    dsimp only [gens₃R, gens₂, Gens.tensor, Gens.triv]
    simp only [comp_app_apply, id_app_apply, assocHom_ι, nat_apply, assocInv_ι, map_map_apply]
    apply map_eq_self
    apply N.hom_ext_enc
    intro i j
    obtain ⟨j, j', rfl⟩ := N.enc_surj j
    enc_fin

variable {F G H}

@[simp] lemma associator_hom_ι {m n q : ℕ} (x : (F.F.obj (N.mk m)).X)
    (y : (G.F.obj (N.mk n)).X) (z : (H.F.obj (N.mk q)).X) :
    Pointed.Hom.toFun ((associator F G H).hom.app (N.mk (m * n * q))) (ι (ι x y) z) =
      Pointed.Hom.toFun ((tensorF F (tensorF G H)).F.map (N.assocInvN m n q)) (ι x (ι y z)) :=
  descL_ι _ x y z

/-! ### The unitors -/

/-- The generator `1 ∈ F1(1₊)`.  It is given this name (rather than written `(1 : Fin 2)`) so
that its type is syntactically `(F1.F.obj 1₊).X`, which is what the lemmas about `ι` expect. -/
def one₁ : (F1.F.obj (N.mk 1)).X := (1 : Fin 2)


/-- `F1` is the free Γ-set on `1 ∈ F1(1₊)`: `ι i y` is `ι 1 y` pushed along `pt i ∧ 𝟙`. -/
lemma ι_F1_left {m n : ℕ} (i : (F1.F.obj (N.mk m)).X) (y : (G.F.obj (N.mk n)).X) :
    ι (F := F1) (G := G) (m := m) i y =
      Pointed.Hom.toFun ((tensorF F1 G).F.map (N.smashMap (N.pt (X := N.mk m) i) (𝟙 _)))
        (ι (F := F1) (G := G) (m := 1) one₁ y) := by
  have h := ι_nat (F := F1) (G := G) (N.pt (X := N.mk m) i) (𝟙 _) one₁ y
  rw [map_id_apply] at h
  exact (congrArg (fun t => ι (F := F1) (G := G) t y)
    (N.pt_apply_one (X := N.mk m) i).symm).trans h

lemma ι_F1_right {m n : ℕ} (x : (F.F.obj (N.mk m)).X) (j : (F1.F.obj (N.mk n)).X) :
    ι (F := F) (G := F1) (n := n) x j =
      Pointed.Hom.toFun ((tensorF F F1).F.map (N.smashMap (𝟙 _) (N.pt (X := N.mk n) j)))
        (ι (F := F) (G := F1) (n := 1) x one₁) := by
  have h := ι_nat (F := F) (G := F1) (𝟙 _) (N.pt (X := N.mk n) j) x one₁
  rw [map_id_apply] at h
  exact (congrArg (fun t => ι (F := F) (G := F1) x t)
    (N.pt_apply_one (X := N.mk n) j).symm).trans h

variable (G)

/-- `i, y ↦ G(j ↦ (i, j)) y`. -/
def lamBimor : Bimor F1 G G where
  φ {m n} i y := Pointed.Hom.toFun (G.F.map (N.incL (m := m) (n := n) i)) y
  nat {m n m' n'} a b i y := by
    change Pointed.Hom.toFun (G.F.map (N.incL (Pointed.Hom.toFun a i)))
      (Pointed.Hom.toFun (G.F.map b) y) = _
    rw [map_map_apply, map_map_apply]
    apply map_congr_apply
    apply N.hom_ext_of_fun
    intro j
    exact (N.smashMap_enc a b i j).symm

/-- `y, j ↦ G(i ↦ (i, j)) y`. -/
def rhoBimor : Bimor G F1 G where
  φ {m n} y j := Pointed.Hom.toFun (G.F.map (N.incR (m := m) (n := n) j)) y
  nat {m n m' n'} a b y j := by
    change Pointed.Hom.toFun (G.F.map (N.incR (Pointed.Hom.toFun b j)))
      (Pointed.Hom.toFun (G.F.map a) y) = _
    rw [map_map_apply, map_map_apply]
    apply map_congr_apply
    apply N.hom_ext_of_fun
    intro i
    exact (N.smashMap_enc a b i j).symm

/-- `G ⟶ F1 ∧ G`, `y ↦ ι 1 y`. -/
def lamInv : G ⟶ tensorF F1 G where
  app k :=
    { toFun := fun y => Pointed.Hom.toFun ((tensorF F1 G).F.map (N.lamN (N.unmk k)))
        (ι (F := F1) (G := G) (m := 1) (n := N.unmk k) one₁ y)
      map_point := by
        change Pointed.Hom.toFun _ (ι (F := F1) (G := G) (m := 1) (n := N.unmk k) one₁
          (G.F.obj (N.mk (N.unmk k))).point) = _
        exact (congrArg (Pointed.Hom.toFun ((tensorF F1 G).F.map (N.lamN (N.unmk k))))
          (ι_point_right (F := F1) (G := G) (m := 1) (n := N.unmk k) one₁)).trans
          (Pointed.Hom.map_point _) }
  naturality := by
    rintro ⟨k⟩ ⟨k'⟩ h
    apply Pointed.hom_ext'
    intro y
    change Pointed.Hom.toFun ((tensorF F1 G).F.map (N.lamN k'))
        (ι (F := F1) (m := 1) one₁ (Pointed.Hom.toFun (G.F.map h) y)) =
      Pointed.Hom.toFun ((tensorF F1 G).F.map h)
        (Pointed.Hom.toFun ((tensorF F1 G).F.map (N.lamN k))
          (ι (F := F1) (m := 1) one₁ y))
    have H : N.smashMap (𝟙 (N.mk 1)) h ≫ N.lamN k' = N.lamN k ≫ h := by
      apply N.hom_ext_enc
      intro i j
      enc_fin
    exact (congrArg (Pointed.Hom.toFun ((tensorF F1 G).F.map (N.lamN k')))
      (ι_map_right (F := F1) h one₁ y)).trans
      ((map_map_apply _ _ _ _).trans ((map_congr_apply _ H _).trans
        (map_map_apply _ _ _ _).symm))

/-- `G ⟶ G ∧ F1`, `y ↦ ι y 1`. -/
def rhoInv : G ⟶ tensorF G F1 where
  app k :=
    { toFun := fun y => Pointed.Hom.toFun ((tensorF G F1).F.map (N.rhoN (N.unmk k)))
        (ι (F := G) (G := F1) (m := N.unmk k) (n := 1) y one₁)
      map_point := by
        change Pointed.Hom.toFun _ (ι (F := G) (G := F1) (m := N.unmk k) (n := 1)
          (G.F.obj (N.mk (N.unmk k))).point one₁) = _
        exact (congrArg (Pointed.Hom.toFun ((tensorF G F1).F.map (N.rhoN (N.unmk k))))
          (ι_point_left (F := G) (G := F1) (m := N.unmk k) (n := 1) one₁)).trans
          (Pointed.Hom.map_point _) }
  naturality := by
    rintro ⟨k⟩ ⟨k'⟩ h
    apply Pointed.hom_ext'
    intro y
    change Pointed.Hom.toFun ((tensorF G F1).F.map (N.rhoN k'))
        (ι (G := F1) (n := 1) (Pointed.Hom.toFun (G.F.map h) y) one₁) =
      Pointed.Hom.toFun ((tensorF G F1).F.map h)
        (Pointed.Hom.toFun ((tensorF G F1).F.map (N.rhoN k))
          (ι (G := F1) (n := 1) y one₁))
    have H : N.smashMap h (𝟙 (N.mk 1)) ≫ N.rhoN k' = N.rhoN k ≫ h := by
      apply N.hom_ext_enc
      intro i j
      enc_fin
    exact (congrArg (Pointed.Hom.toFun ((tensorF G F1).F.map (N.rhoN k')))
      (ι_map_left (G := F1) h y one₁)).trans
      ((map_map_apply _ _ _ _).trans ((map_congr_apply _ H _).trans
        (map_map_apply _ _ _ _).symm))

variable {G}

@[simp] lemma lam_ι {m n : ℕ} (i : (F1.F.obj (N.mk m)).X) (y : (G.F.obj (N.mk n)).X) :
    Pointed.Hom.toFun ((desc (lamBimor G)).app (N.mk (m * n))) (ι (F := F1) i y) =
      Pointed.Hom.toFun (G.F.map (N.incL (m := m) (n := n) i)) y :=
  desc_ι _ _ _

@[simp] lemma rho_ι {m n : ℕ} (y : (G.F.obj (N.mk m)).X) (j : (F1.F.obj (N.mk n)).X) :
    Pointed.Hom.toFun ((desc (rhoBimor G)).app (N.mk (m * n))) (ι (G := F1) y j) =
      Pointed.Hom.toFun (G.F.map (N.incR (m := m) (n := n) j)) y :=
  desc_ι _ _ _

@[simp] lemma lamInv_apply {n : ℕ} (y : (G.F.obj (N.mk n)).X) :
    Pointed.Hom.toFun ((lamInv G).app (N.mk n)) y =
      Pointed.Hom.toFun ((tensorF F1 G).F.map (N.lamN n)) (ι (F := F1) (m := 1) one₁ y) :=
  rfl

@[simp] lemma rhoInv_apply {n : ℕ} (y : (G.F.obj (N.mk n)).X) :
    Pointed.Hom.toFun ((rhoInv G).app (N.mk n)) y =
      Pointed.Hom.toFun ((tensorF G F1).F.map (N.rhoN n)) (ι (G := F1) (n := 1) y one₁) :=
  rfl

variable (G)

/-- **The left unitor** `F1 ∧ G ≅ G`. -/
def leftUnitor : tensorF F1 G ≅ G where
  hom := desc (lamBimor G)
  inv := lamInv G
  hom_inv_id := by
    apply Gens.ext (gens₂ F1 G)
    rintro ⟨⟨m, i⟩, ⟨n, y⟩⟩
    dsimp only [gens₂, Gens.tensor, Gens.triv]
    simp only [comp_app_apply, id_app_apply, lam_ι, lamInv_apply, ι_map_right, map_map_apply]
    rw [ι_F1_left (G := G) i y]
    apply map_congr_apply
    change Fin (m + 1) at i
    apply N.hom_ext_enc
    intro c j
    enc_fin
  inv_hom_id := by
    apply Gens.ext (Gens.triv G)
    rintro ⟨n, y⟩
    dsimp only [Gens.triv]
    simp only [comp_app_apply, id_app_apply, lam_ι, nat_apply, lamInv_apply, map_map_apply]
    apply map_eq_self
    apply N.hom_ext_of_fun
    intro j
    exact (N.lamN_enc (1 : Fin 2) j).trans (by simp)

/-- **The right unitor** `G ∧ F1 ≅ G`. -/
def rightUnitor : tensorF G F1 ≅ G where
  hom := desc (rhoBimor G)
  inv := rhoInv G
  hom_inv_id := by
    apply Gens.ext (gens₂ G F1)
    rintro ⟨⟨m, y⟩, ⟨n, j⟩⟩
    dsimp only [gens₂, Gens.tensor, Gens.triv]
    simp only [comp_app_apply, id_app_apply, rho_ι, rhoInv_apply, ι_map_left, map_map_apply]
    rw [ι_F1_right (F := G) y j]
    apply map_congr_apply
    change Fin (n + 1) at j
    apply N.hom_ext_enc
    intro i c
    enc_fin
  inv_hom_id := by
    apply Gens.ext (Gens.triv G)
    rintro ⟨n, y⟩
    dsimp only [Gens.triv]
    simp only [comp_app_apply, id_app_apply, rho_ι, nat_apply, rhoInv_apply, map_map_apply]
    apply map_eq_self
    apply N.hom_ext_of_fun
    intro j
    exact (N.rhoN_enc j (1 : Fin 2)).trans (by simp)

variable {G}

@[simp] lemma leftUnitor_hom_ι {m n : ℕ} (i : (F1.F.obj (N.mk m)).X) (y : (G.F.obj (N.mk n)).X) :
    Pointed.Hom.toFun ((leftUnitor G).hom.app (N.mk (m * n))) (ι (F := F1) i y) =
      Pointed.Hom.toFun (G.F.map (N.incL (m := m) (n := n) i)) y :=
  desc_ι _ _ _

@[simp] lemma rightUnitor_hom_ι {m n : ℕ} (y : (G.F.obj (N.mk m)).X) (j : (F1.F.obj (N.mk n)).X) :
    Pointed.Hom.toFun ((rightUnitor G).hom.app (N.mk (m * n))) (ι (G := F1) y j) =
      Pointed.Hom.toFun (G.F.map (N.incR (m := m) (n := n) j)) y :=
  desc_ι _ _ _

/-! ### Coherence -/

lemma associator_naturality {F₁ F₂ F₃ G₁ G₂ G₃ : GammaSet} (f₁ : F₁ ⟶ G₁) (f₂ : F₂ ⟶ G₂)
    (f₃ : F₃ ⟶ G₃) :
    tensorHomF (tensorHomF f₁ f₂) f₃ ≫ (associator G₁ G₂ G₃).hom =
      (associator F₁ F₂ F₃).hom ≫ tensorHomF f₁ (tensorHomF f₂ f₃) := by
  apply Gens.ext (gens₃L F₁ F₂ F₃)
  rintro ⟨⟨⟨m, x⟩, ⟨n, y⟩⟩, ⟨q, z⟩⟩
  dsimp only [gens₃L, gens₂, Gens.tensor, Gens.triv]
  simp only [comp_app_apply, tensorHomF_ι, associator_hom_ι, nat_apply]

lemma leftUnitor_naturality {X Y : GammaSet} (f : X ⟶ Y) :
    tensorHomF (𝟙 F1) f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
  apply Gens.ext (gens₂ F1 X)
  rintro ⟨⟨m, i⟩, ⟨n, x⟩⟩
  dsimp only [gens₂, Gens.tensor, Gens.triv]
  simp only [comp_app_apply, tensorHomF_ι, id_app_apply, leftUnitor_hom_ι, nat_apply]

lemma rightUnitor_naturality {X Y : GammaSet} (f : X ⟶ Y) :
    tensorHomF f (𝟙 F1) ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
  apply Gens.ext (gens₂ X F1)
  rintro ⟨⟨m, x⟩, ⟨n, j⟩⟩
  dsimp only [gens₂, Gens.tensor, Gens.triv]
  simp only [comp_app_apply, tensorHomF_ι, id_app_apply, rightUnitor_hom_ι, nat_apply]

lemma pentagon (W X Y Z : GammaSet) :
    tensorHomF (associator W X Y).hom (𝟙 Z) ≫ (associator W (tensorF X Y) Z).hom ≫
        tensorHomF (𝟙 W) (associator X Y Z).hom =
      (associator (tensorF W X) Y Z).hom ≫ (associator W X (tensorF Y Z)).hom := by
  apply Gens.ext (gens₄ W X Y Z)
  rintro ⟨⟨⟨⟨a, w⟩, ⟨b, x⟩⟩, ⟨c, y⟩⟩, ⟨d, z⟩⟩
  dsimp only [gens₄, gens₃L, gens₂, Gens.tensor, Gens.triv]
  simp only [comp_app_apply, tensorHomF_ι, id_app_apply, associator_hom_ι, nat_apply,
    ι_map_left, ι_map_right, map_map_apply]
  apply map_congr_apply
  apply N.hom_ext_enc
  intro i j
  obtain ⟨j, j', rfl⟩ := N.enc_surj j
  obtain ⟨j', j'', rfl⟩ := N.enc_surj j'
  enc_fin

lemma triangle (X Y : GammaSet) :
    (associator X F1 Y).hom ≫ tensorHomF (𝟙 X) (leftUnitor Y).hom =
      tensorHomF (rightUnitor X).hom (𝟙 Y) := by
  apply Gens.ext (gens₃L X F1 Y)
  rintro ⟨⟨⟨m, x⟩, ⟨n, i⟩⟩, ⟨q, y⟩⟩
  dsimp only [gens₃L, gens₂, Gens.tensor, Gens.triv]
  simp only [comp_app_apply, tensorHomF_ι, id_app_apply, associator_hom_ι, nat_apply,
    leftUnitor_hom_ι, rightUnitor_hom_ι, ι_map_left, ι_map_right, map_map_apply]
  apply map_congr_apply
  change Fin (n + 1) at i
  apply N.hom_ext_enc
  intro i j
  enc_fin

end Day

open MonoidalCategory

/-- The monoidal structure data on `GammaSet`: smash product, unit `F1`, … -/
instance : MonoidalCategoryStruct GammaSet where
  tensorObj := Day.tensorF
  whiskerLeft X _ _ f := Day.tensorHomF (𝟙 X) f
  whiskerRight f Y := Day.tensorHomF f (𝟙 Y)
  tensorHom := Day.tensorHomF
  tensorUnit := F1
  associator := Day.associator
  leftUnitor := Day.leftUnitor
  rightUnitor := Day.rightUnitor

/-- **`GammaSet` is a monoidal category** under the smash product. -/
instance : MonoidalCategory GammaSet where
  tensorHom_def f g := by
    change Day.tensorHomF f g = Day.tensorHomF f (𝟙 _) ≫ Day.tensorHomF (𝟙 _) g
    rw [Day.tensorHomF_comp, Category.comp_id, Category.id_comp]
  id_tensorHom_id := Day.tensorHomF_id
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := Day.tensorHomF_comp f₁ g₁ f₂ g₂
  whiskerLeft_id := Day.tensorHomF_id
  id_whiskerRight := Day.tensorHomF_id
  associator_naturality := Day.associator_naturality
  leftUnitor_naturality := Day.leftUnitor_naturality
  rightUnitor_naturality := Day.rightUnitor_naturality
  pentagon := Day.pentagon
  triangle := Day.triangle

end GammaSet
