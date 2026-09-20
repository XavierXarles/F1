import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Monoid
import F1.HyperAdd
/-! Introducing HyperAdd and F1modules -/

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
  hadd_assoc {n m : ℕ} (p : partition n m) (A : Fin n → (Set M)) :
    HyperAdd.set M n A ⊆ HyperAdd.set M m (fun i => HyperAdd.finset M n (p.toFun i) (fun f => A f))

/-- The hadd_assoc for a AddCommMonoid is exactly the statement that a sum over Fin n can be
regrouped according to a partition into blocks. -/
instance AddCommMonoid.F1module (M : Type u) [AddCommMonoid M] : F1module M where
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
