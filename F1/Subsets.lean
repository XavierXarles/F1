import F1.F1Modules

/-!
# The `F1module` of subsets of `Fin n`

`𝒫(n) = Finset (Fin n)`, with the hyperoperation

`hadd k S = {⋃ᵢ S i}` if the `S i` are pairwise disjoint, `∅` otherwise,

and zero `∅`.  This is the value at `1₊` of the representable Γ-set `N(n₊, -)`: a pointed map
`n₊ ⟶ 1₊` is a subset of `{1, …, n}`, and a family of such maps has a lift to level `k` exactly
when the subsets are disjoint, with sum their union.  It is the model object from which the
right adjoint of `GammaSpace.toF1moduleCat` will be built, `R M (n₊) = Hom (𝒫(n), M)`.

We put the instances directly on `Finset (Fin n)`.  Note that under `open Pointwise`,
`Finset (Fin n)` may acquire an `AddMonoid` structure, and with it a second, different,
`HyperAdd` instance through `AddMonoid.toHyperAdd`; avoid mixing the two.
-/

open Finset

namespace Subsets

variable {n : ℕ}

/-- The hyperoperation on subsets: the disjoint union, if the family is disjoint. -/
def haddSet (k : ℕ) (S : Fin k → Finset (Fin n)) : Set (Finset (Fin n)) :=
  {T | Pairwise (fun i j => Disjoint (S i) (S j)) ∧ T = univ.biUnion S}

instance instHyperAdd : HyperAdd (Finset (Fin n)) where
  hadd := haddSet

theorem mem_hadd_iff {k : ℕ} {S : Fin k → Finset (Fin n)} {T : Finset (Fin n)} :
    T ∈ hadd k S ↔ Pairwise (fun i j => Disjoint (S i) (S j)) ∧ T = univ.biUnion S :=
  Iff.rfl

/-- A non-disjoint family has no sum. -/
theorem hadd_eq_empty {k : ℕ} {S : Fin k → Finset (Fin n)} {i j : Fin k} (hij : i ≠ j)
    (h : ¬ Disjoint (S i) (S j)) : hadd k S = ∅ := by
  ext T
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hT
  exact h ((mem_hadd_iff.mp hT).1 hij)

/-- The empty set is a sum of any number of copies of itself. -/
theorem empty_mem_hadd (k : ℕ) : (∅ : Finset (Fin n)) ∈ hadd k (fun _ => ∅) :=
  mem_hadd_iff.mpr ⟨fun _ _ _ => Finset.disjoint_empty_left _, by ext x; simp⟩

/-- **Hyper-associativity for subsets.**  If `x` is the disjoint union of the `a i`, then
regrouping along a partition `p`, the block unions `b j = ⋃_{i ∈ p j} a i` are disjoint unions
of the `a i` in each block, are pairwise disjoint, and have union `x`. -/
theorem hadd_assoc {k m : ℕ} (p : partition k m) (A : Fin k → Set (Finset (Fin n))) :
    HyperAdd.set (Finset (Fin n)) k A
      ⊆ HyperAdd.set (Finset (Fin n)) m
          (fun j => HyperAdd.finset (Finset (Fin n)) k (p.toFun j) fun f => A f) := by
  intro x hx
  simp only [HyperAdd.set, Set.mem_iUnion] at hx
  obtain ⟨a, hx⟩ := hx
  obtain ⟨hdisj, rfl⟩ := mem_hadd_iff.mp hx
  simp only [HyperAdd.set, Set.mem_iUnion]
  refine ⟨fun j => ⟨(p.toFun j).biUnion (fun i => (a i : Finset (Fin n))), ?_⟩, ?_⟩
  · -- the `j`-th block union is a sum of the elements of the `j`-th block
    simp only [HyperAdd.finset, Set.mem_iUnion]
    refine ⟨fun i => a (i : Fin k), ?_⟩
    refine mem_hadd_iff.mpr ⟨?_, ?_⟩
    · -- the elements of a block are pairwise disjoint, since `orderIsoOfFin` is injective
      intro r r' hrr'
      apply hdisj
      intro h
      exact hrr' (((p.toFun j).orderIsoOfFin rfl).injective (Subtype.ext h))
    · -- listing a block through `orderIsoOfFin` does not change its union
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, hx⟩
        refine ⟨((p.toFun j).orderIsoOfFin rfl).symm ⟨i, hi⟩, ?_⟩
        rw [OrderIso.apply_symm_apply]
        exact hx
      · rintro ⟨r, hx⟩
        exact ⟨((p.toFun j).orderIsoOfFin rfl r : Fin k),
          ((p.toFun j).orderIsoOfFin rfl r).2, hx⟩
  · refine mem_hadd_iff.mpr ⟨?_, ?_⟩
    · -- different blocks have disjoint unions, since blocks are disjoint
      intro j j' hjj'
      change Disjoint ((p.toFun j).biUnion _) ((p.toFun j').biUnion _)
      rw [Finset.disjoint_biUnion_left]
      intro i hi
      rw [Finset.disjoint_biUnion_right]
      intro i' hi'
      apply hdisj
      rintro rfl
      obtain ⟨w, -, huniq⟩ := p.isPar i
      exact hjj' ((huniq j hi).trans (huniq j' hi').symm)
    · -- the union of the block unions is the total union, since blocks cover `Fin k`
      change univ.biUnion (fun i => (a i : Finset (Fin n)))
          = univ.biUnion (fun j => (p.toFun j).biUnion (fun i => (a i : Finset (Fin n))))
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hx⟩
        obtain ⟨j, hj, -⟩ := p.isPar i
        exact ⟨j, i, hj, hx⟩
      · rintro ⟨j, i, -, hx⟩
        exact ⟨i, hx⟩

/-- **The model `𝒫(n)`**: subsets of `Fin n`, with disjoint union and zero `∅`. -/
instance instF1module : F1module (Finset (Fin n)) where
  zero := ∅
  zero_mem k := empty_mem_hadd k
  eq_zero_of_mem_hadd_zero x y hy := by
    rw [(mem_hadd_iff.mp hy).2]
    ext i
    exact Eq.to_iff rfl
  hadd_assoc p A := hadd_assoc p A

@[simp] theorem zero_eq_empty : (F1module.zero : Finset (Fin n)) = ∅ := rfl

end Subsets
