import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Monoid
import F1.HyperAdd
/-!
# `F1module`s

An `F1module` is a `HyperAdd` structure with

* a distinguished element `zero`, which is a sum of any number of copies of itself
  (`zero_mem : ∀ k, zero ∈ hadd k (fun _ => zero)`; for `k = 0` this says `zero` is an empty sum),
  and which is the only empty sum (`eq_zero_of_mem_hadd_zero`);
* hyper-associativity `hadd_assoc`: a sum can always be computed by regrouping along a partition.

Morphisms (`F1module.Hom`) are the weak morphisms of `HyperAdd` structures which preserve `zero`.

The zero is what makes the points functor `GammaSpace ⥤ F1moduleCat` have a right adjoint:
the Γ-set attached to an `F1module` has to be pointed at every level.
-/

universe u

section HyperAdd

def HyperAdd.set (M : Type u) [HyperAdd M] (n : ℕ) : (Fin n → Set M) → Set M :=
   fun A => ⋃ (a : (i : Fin n) → (A i)), hadd n (fun i => (a i : M))

def HyperAdd.finset (M : Type u) [HyperAdd M] (n : ℕ) (F : Finset (Fin n)) : (F → Set M) → Set M :=
  fun A => ⋃ (a : (i : F) → (A i)), hadd F.card (fun i => (a ((F.orderIsoOfFin rfl) i) : M))

end HyperAdd

structure partition (n m : ℕ) where
  toFun : (Fin m) → (Finset (Fin n))
  isPar : ∀ i : (Fin n), ∃! j : (Fin m), i ∈ toFun j

class F1module (M : Type u) extends HyperAdd M where
  /-- the distinguished element -/
  zero : M
  /-- `zero` is a sum of any number (including none) of copies of itself -/
  zero_mem : ∀ k : ℕ, zero ∈ hadd k (fun _ => zero)
  /-- `zero` is the *only* empty sum -/
  eq_zero_of_mem_hadd_zero : ∀ (x : Fin 0 → M) (y : M), y ∈ hadd 0 x → y = zero
  /-- hyper-associativity: a sum can be regrouped along any partition -/
  hadd_assoc {n m : ℕ} (p : partition n m) (A : Fin n → (Set M)) :
    HyperAdd.set M n A ⊆ HyperAdd.set M m (fun i => HyperAdd.finset M n (p.toFun i) (fun f => A f))

/-- The hadd_assoc for a AddCommMonoid is exactly the statement that a sum over Fin n can be
regrouped according to a partition into blocks. -/
instance AddCommMonoid.F1module (M : Type u) [AddCommMonoid M] : F1module M where
  zero := 0
  zero_mem k := by
    rw [AddMonoid.hadd_eq_sum]
    simp
  eq_zero_of_mem_hadd_zero x y hy := by
    rw [AddMonoid.hadd_eq_sum] at hy
    simpa using hy
  hadd_assoc {n m} (p) (A) := by
    intro x hx
    simp only [HyperAdd.set, Set.mem_iUnion] at hx
    obtain ⟨a, hx⟩ := hx
    rw [AddMonoid.hadd_eq_sum] at hx
    change x = ∑ i, (a i : M) at hx
    -- The blocks of the partition cover `Fin n` and are pairwise disjoint
    have hUnion : Finset.univ.biUnion p.toFun = (Finset.univ : Finset (Fin n)) := by
      rw [Finset.eq_univ_iff_forall]
      intro i
      rw [Finset.mem_biUnion]
      obtain ⟨j, hj, _⟩ := p.isPar i
      exact ⟨j, Finset.mem_univ j, hj⟩
    have hDisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m))) p.toFun := by
      intro i _ j _ hij
      simp_rw [Finset.disjoint_left]
      intro k hki hkj
      obtain ⟨j0, _, hUniq⟩ := p.isPar k
      exact hij ((hUniq i hki).trans (hUniq j hkj).symm)
    -- Regroup the sum block by block
    have hsum : (∑ i : Fin n, (a i : M)) = ∑ j : Fin m, ∑ i ∈ p.toFun j, (a i : M) := by
      conv_lhs => rw [← hUnion]
      rw [Finset.sum_biUnion hDisj]
    -- A sum over a Finset equals a sum over its coercion to a subtype
    have hcoe : ∀ (s : Finset (Fin n)) (f : Fin n → M), (∑ i : s, f i) = ∑ i ∈ s, f i := by
      intro s f
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach s f
    simp only [HyperAdd.set, Set.mem_iUnion]
    refine ⟨fun j => ⟨∑ i ∈ p.toFun j, (a i : M), ?_⟩, ?_⟩
    · -- each block-sum lies in the corresponding `HyperAdd.finset`
      simp only [HyperAdd.finset, Set.mem_iUnion]
      refine ⟨fun i => a (i : Fin n), ?_⟩
      rw [AddMonoid.hadd_eq_sum]
      change (∑ i ∈ p.toFun j, (a i : M))
        = ∑ k : Fin (p.toFun j).card, (a (((p.toFun j).orderIsoOfFin rfl k : Fin n)) : M)
      rw [← hcoe (p.toFun j) (fun i => (a i : M))]
      exact (Equiv.sum_comp ((p.toFun j).orderIsoOfFin rfl).toEquiv
        (fun i => (a (i : Fin n) : M))).symm
    · rw [AddMonoid.hadd_eq_sum]
      change x = ∑ j : Fin m, ∑ i ∈ p.toFun j, (a i : M)
      rw [hx, hsum]

@[simp] theorem AddCommMonoid.F1module_zero (M : Type u) [AddCommMonoid M] :
    (F1module.zero : M) = 0 := rfl

/-! ## Morphisms of `F1module`s -/

namespace F1module

/-- A morphism of `F1module`s: a weak morphism of the hyper-additive structures which preserves
the zero. -/
structure Hom (X Y : Type u) [F1module X] [F1module Y] extends HyperAdd.Hom X Y where
  /-- the zero is preserved -/
  map_zero' : toFun (F1module.zero : X) = (F1module.zero : Y)

namespace Hom

variable {X Y Z W : Type u} [F1module X] [F1module Y] [F1module Z] [F1module W]

theorem toFun_injective : Function.Injective (fun f : Hom X Y => (f.toFun : X → Y)) := by
  rintro ⟨⟨f, hf⟩, hz⟩ ⟨⟨g, hg⟩, hz'⟩ h
  change f = g at h
  subst h
  rfl

instance : FunLike (Hom X Y) X Y where
  coe f := f.toFun
  coe_injective := toFun_injective

@[simp] theorem toFun_eq_coe (f : Hom X Y) : f.toFun = ⇑f := rfl

@[simp] theorem coe_toHom (f : Hom X Y) : ⇑f.toHom = ⇑f := rfl

@[ext] theorem ext {f g : Hom X Y} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

theorem map_zero (f : Hom X Y) : f (F1module.zero : X) = (F1module.zero : Y) := f.map_zero'

theorem mem_hadd_of_mem_hadd (f : Hom X Y) (n : ℕ) (x : Fin n → X) {a : X}
    (ha : a ∈ hadd n x) : f a ∈ hadd n (⇑f ∘ x) :=
  f.map_hadd n x ⟨a, ha, rfl⟩

/-- The identity morphism. -/
protected def id (X : Type u) [F1module X] : Hom X X where
  toHom := HyperAdd.Hom.id X
  map_zero' := rfl

/-- Composition of morphisms. -/
protected def comp (g : Hom Y Z) (f : Hom X Y) : Hom X Z where
  toHom := g.toHom.comp f.toHom
  map_zero' := (congrArg g.toFun f.map_zero').trans g.map_zero'

@[simp] theorem coe_id : ⇑(Hom.id X) = _root_.id := rfl

@[simp] theorem coe_comp (g : Hom Y Z) (f : Hom X Y) : ⇑(g.comp f) = ⇑g ∘ ⇑f := rfl

@[simp] theorem id_apply (x : X) : Hom.id X x = x := rfl

@[simp] theorem comp_apply (g : Hom Y Z) (f : Hom X Y) (x : X) : g.comp f x = g (f x) := rfl

theorem id_comp (f : Hom X Y) : (Hom.id Y).comp f = f := rfl

theorem comp_id (f : Hom X Y) : f.comp (Hom.id X) = f := rfl

theorem comp_assoc (h : Hom Z W) (g : Hom Y Z) (f : Hom X Y) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

end Hom

end F1module

/-- An additive monoid hom between commutative monoids is a morphism of `F1module`s. -/
def AddMonoidHom.toF1moduleHom {M N : Type u} [AddCommMonoid M] [AddCommMonoid N]
    (f : M →+ N) : F1module.Hom M N where
  toHom := f.toHyperAddHom
  map_zero' := f.map_zero

@[simp] theorem AddMonoidHom.coe_toF1moduleHom {M N : Type u} [AddCommMonoid M]
    [AddCommMonoid N] (f : M →+ N) : ⇑f.toF1moduleHom = ⇑f := rfl
