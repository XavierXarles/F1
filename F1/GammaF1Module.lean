import F1.GammaHyperAdd
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Sort

/-!
# The points of a Γ-set form an `F1module`

We prove `GammaSet.hadd_assoc`: for every Γ-set `X`, every partition `p` of `Fin n` into
`m` blocks and every family of subsets `A : Fin n → Set X.Points`,

`HyperAdd.set X.Points n A ⊆ HyperAdd.set X.Points m (fun j => HyperAdd.finset … (p.toFun j) …)`,

so `X.Points` is an `F1module` and the functor `GammaSet.toHyperAddCat` in fact lands in
`F1module`s.  No hypothesis on `X` is needed.

## The proof

A partition `p` gives two families of morphisms of `N`:

* `N.block p : n₊ ⟶ m₊`, sending `i.succ` to `(p.idx i).succ`, where `p.idx i` is the index of
  the block containing `i`;
* `N.restr F : n₊ ⟶ (F.card)₊` for a block `F`, sending `i.succ` to `k.succ` when `i` is the
  `k`-th element of `F` (in the order of `F.orderIsoOfFin rfl`, which is the order in which
  `HyperAdd.finset` lists a block) and everything outside `F` to the basepoint.

If `z : X.Level n` lifts the tuple `a` then `u := X.act (N.block p) z` is the required lift at
level `m`, and `X.act (N.restr (p.toFun j)) z` is the required lift of the `j`-th block.  All
three verifications come from identities *in `N`*, transported by functoriality of `X`:

* `N.restr_comp_proj`: `restr F ≫ map_proj k = map_proj (e k)` — the restriction of `z` to a
  block has the right coordinates (`GammaSet.proj_act_restr`);
* `N.block_comp_proj`: `block p ≫ map_proj j = restr (p.toFun j) ≫ map_add (p.toFun j).card`
  — the `j`-th coordinate of `u` *is* the total sum of the `j`-th block
  (`GammaSet.proj_act_block`).  This is the heart of the matter: projecting after regrouping
  is the same as summing after restricting;
* `N.block_comp_add`: `block p ≫ map_add m = map_add n` — regrouping does not change the total
  sum (`GammaSet.add_act_block`).

The `Finset.orderIsoOfFin` bookkeeping is confined to `N.restrFun_succ_eq_succ_iff`.
-/

open CategoryTheory Pointed

/-! ## The block index of a partition -/

namespace partition

variable {n m : ℕ} (p : partition n m)

theorem exists_mem_block (i : Fin n) : ∃ j : Fin m, i ∈ p.toFun j := by
  obtain ⟨j, hj, -⟩ := p.isPar i
  exact ⟨j, hj⟩

/-- The index of the (unique) block of `p` containing `i`. -/
noncomputable def idx (i : Fin n) : Fin m := (p.exists_mem_block i).choose

theorem mem_idx (i : Fin n) : i ∈ p.toFun (p.idx i) := (p.exists_mem_block i).choose_spec

theorem eq_idx {i : Fin n} {j : Fin m} (h : i ∈ p.toFun j) : j = p.idx i := by
  obtain ⟨w, hw, huniq⟩ := p.isPar i
  exact (huniq j h).trans (huniq _ (p.mem_idx i)).symm

theorem idx_eq_iff {i : Fin n} {j : Fin m} : p.idx i = j ↔ i ∈ p.toFun j := by
  constructor
  · intro h
    rw [← h]
    exact p.mem_idx i
  · intro h
    exact (p.eq_idx h).symm

end partition

/-! ## The two families of morphisms of `N` -/

namespace N

/-- Two morphisms of `N` agree as soon as they agree on the non-basepoint elements: on the
basepoint both are forced by `map_point`. -/
theorem hom_ext_of_succ {n m : ℕ} {f g : mk n ⟶ mk m}
    (h : ∀ i : Fin n, Pointed.Hom.toFun f i.succ = Pointed.Hom.toFun g i.succ) : f = g := by
  apply Pointed.hom_ext'
  intro i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · exact (Pointed.Hom.map_point f).trans (Pointed.Hom.map_point g).symm
  · exact h i

/-! ### The block map -/

/-- The function underlying `N.block p`: a non-basepoint `i` is sent to the index of the block
of `p` containing it. -/
noncomputable def blockFun {n m : ℕ} (p : partition n m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cons 0 fun i => (p.idx i).succ

@[simp] theorem blockFun_zero {n m : ℕ} (p : partition n m) : blockFun p 0 = 0 := rfl

@[simp] theorem blockFun_succ {n m : ℕ} (p : partition n m) (i : Fin n) :
    blockFun p i.succ = (p.idx i).succ := rfl

/-- The block map `n₊ ⟶ m₊` attached to a partition of `Fin n` into `m` blocks. -/
noncomputable def block {n m : ℕ} (p : partition n m) : mk n ⟶ mk m :=
  ofFun (blockFun p) rfl

/-! ### The restriction to a block -/

/-- The function underlying `N.restr F`: an element of `F` is sent to its position in `F` (in
the order used by `HyperAdd.finset`), everything else to the basepoint. -/
def restrFun {n : ℕ} (F : Finset (Fin n)) : Fin (n + 1) → Fin (F.card + 1) :=
  Fin.cons 0 fun i =>
    if h : i ∈ F then (((F.orderIsoOfFin rfl).symm ⟨i, h⟩ : Fin F.card)).succ else 0

@[simp] theorem restrFun_zero {n : ℕ} (F : Finset (Fin n)) : restrFun F 0 = 0 := rfl

theorem restrFun_succ_eq_succ_iff {n : ℕ} (F : Finset (Fin n)) (i : Fin n) (k : Fin F.card) :
    restrFun F i.succ = k.succ ↔ i = ((F.orderIsoOfFin rfl) k : Fin n) := by
  simp only [restrFun, Fin.cons_succ]
  by_cases h : i ∈ F
  · rw [dite_eq_left h, Fin.succ_inj]
    constructor
    · intro hc
      have h2 : (⟨i, h⟩ : {x // x ∈ F}) = (F.orderIsoOfFin rfl) k := by
        rw [← hc, OrderIso.apply_symm_apply]
      exact congrArg Subtype.val h2
    · intro hc
      have h2 : (⟨i, h⟩ : {x // x ∈ F}) = (F.orderIsoOfFin rfl) k := Subtype.ext hc
      rw [h2, OrderIso.symm_apply_apply]
  · rw [dite_eq_right h]
    constructor
    · intro hc
      exact absurd hc.symm (Fin.succ_ne_zero k)
    · intro hc
      have hi : i ∈ F := by
        rw [hc]
        exact ((F.orderIsoOfFin rfl) k).2
      exact absurd hi h

theorem restrFun_succ_eq_zero_iff {n : ℕ} (F : Finset (Fin n)) (i : Fin n) :
    restrFun F i.succ = 0 ↔ i ∉ F := by
  simp only [restrFun, Fin.cons_succ]
  by_cases h : i ∈ F
  · rw [dite_eq_left h]
    exact ⟨fun hc => absurd hc (Fin.succ_ne_zero _), fun hc => absurd h hc⟩
  · rw [dite_eq_right h]
    exact ⟨fun _ => h, fun _ => rfl⟩

/-- The restriction-and-reindexing map `n₊ ⟶ (F.card)₊` attached to a block `F`. -/
def restr {n : ℕ} (F : Finset (Fin n)) : mk n ⟶ mk F.card := ofFun (restrFun F) rfl

/-! ### The three identities

Each is an equality of pointed maps `n₊ ⟶ 1₊`, checked on the non-basepoint elements. -/

/-- Projecting to the `k`-th coordinate after restricting to `F` is projecting to the `k`-th
element of `F`. -/
theorem restr_comp_proj {n : ℕ} (F : Finset (Fin n)) (k : Fin F.card) :
    restr F ≫ map_proj k = map_proj ((F.orderIsoOfFin rfl) k : Fin n) := by
  refine hom_ext_of_succ ?_
  intro i
  change (if restrFun F i.succ = k.succ then (1 : Fin 2) else 0)
      = (if i.succ = (((F.orderIsoOfFin rfl) k : Fin n)).succ then (1 : Fin 2) else 0)
  by_cases h : i = ((F.orderIsoOfFin rfl) k : Fin n)
  · rw [ite_eq_left ((restrFun_succ_eq_succ_iff F i k).mpr h), ite_eq_left (congrArg Fin.succ h)]
  · rw [ite_eq_right fun hc => h ((restrFun_succ_eq_succ_iff F i k).mp hc),
      ite_eq_right fun hc => h (Fin.succ_inj.mp hc)]

/-- **The key identity.** Projecting to the `j`-th coordinate after regrouping along `p` is the
same as summing everything in the `j`-th block. -/
theorem block_comp_proj {n m : ℕ} (p : partition n m) (j : Fin m) :
    block p ≫ map_proj j = restr (p.toFun j) ≫ map_add (p.toFun j).card := by
  refine hom_ext_of_succ ?_
  intro i
  change (if (p.idx i).succ = j.succ then (1 : Fin 2) else 0)
      = (if restrFun (p.toFun j) i.succ = 0 then (0 : Fin 2) else 1)
  by_cases h : i ∈ p.toFun j
  · rw [ite_eq_left (congrArg Fin.succ (p.idx_eq_iff.mpr h))]
    rw [@right_eq_ite_iff]
    rw [@restrFun_succ_eq_zero_iff]
    exact fun a ↦ Eq.symm (Fin.eq_one_of_ne_zero 0 fun a_1 ↦ a h)
  · rw [ite_eq_right fun hc => h (p.idx_eq_iff.mp (Fin.succ_inj.mp hc)),
      ite_eq_left ((restrFun_succ_eq_zero_iff (p.toFun j) i).mpr h)]

/-- Regrouping along a partition does not change the total sum. -/
theorem block_comp_add {n m : ℕ} (p : partition n m) : block p ≫ map_add m = map_add n := by
  refine hom_ext_of_succ ?_
  intro i
  change (if (p.idx i).succ = (0 : Fin (m + 1)) then (0 : Fin 2) else 1)
      = (if i.succ = (0 : Fin (n + 1)) then (0 : Fin 2) else 1)
  rw [ite_eq_right (Fin.succ_ne_zero _), ite_eq_right (Fin.succ_ne_zero _)]

end N

/-! ## Transport to a Γ-set -/

namespace GammaSet

section Act

variable (X : GammaSet)

/-- The action of a morphism of `N` on the levels of `X`. -/
def act {n m : ℕ} (f : N.mk n ⟶ N.mk m) (z : X.Level n) : X.Level m :=
  Pointed.Hom.toFun (X.F.map f) z

theorem proj_eq_act {n : ℕ} (j : Fin n) (z : X.Level n) :
    X.proj j z = X.act (N.map_proj j) z := rfl

theorem add_eq_act (n : ℕ) (z : X.Level n) : X.add n z = X.act (N.map_add n) z := rfl

theorem act_comp {n m k : ℕ} (f : N.mk n ⟶ N.mk m) (g : N.mk m ⟶ N.mk k) (z : X.Level n) :
    X.act g (X.act f z) = X.act (f ≫ g) z :=
  (congrArg (fun h : X.F.obj (N.mk n) ⟶ X.F.obj (N.mk k) => Pointed.Hom.toFun h z)
    (X.F.map_comp f g)).symm

theorem act_congr {n m : ℕ} {f g : N.mk n ⟶ N.mk m} (h : f = g) (z : X.Level n) :
    X.act f z = X.act g z :=
  congrArg (fun k : N.mk n ⟶ N.mk m => X.act k z) h

end Act

section Regroup

variable (X : GammaSet) {n m : ℕ}

/-- The `k`-th coordinate of the restriction of `z` to a block `F` is the coordinate of `z` at
the `k`-th element of `F`. -/
theorem proj_act_restr (F : Finset (Fin n)) (k : Fin F.card) (z : X.Level n) :
    X.proj k (X.act (N.restr F) z) = X.proj ((F.orderIsoOfFin rfl) k : Fin n) z := by
  rw [X.proj_eq_act, X.act_comp, X.act_congr (N.restr_comp_proj F k), ← X.proj_eq_act]

/-- The `j`-th coordinate of the regrouping of `z` along `p` is the total sum of the part of `z`
lying over the `j`-th block. -/
theorem proj_act_block (p : partition n m) (j : Fin m) (z : X.Level n) :
    X.proj j (X.act (N.block p) z)
      = X.add (p.toFun j).card (X.act (N.restr (p.toFun j)) z) := by
  rw [X.proj_eq_act, X.act_comp, X.add_eq_act, X.act_comp,
    X.act_congr (N.block_comp_proj p j)]

/-- Regrouping `z` along `p` does not change its total sum. -/
theorem add_act_block (p : partition n m) (z : X.Level n) :
    X.add m (X.act (N.block p) z) = X.add n z := by
  rw [X.add_eq_act, X.act_comp, X.act_congr (N.block_comp_add p), ← X.add_eq_act]

end Regroup

/-! ## The associativity inclusion -/

variable (X : GammaSet)

/-- **Hyper-associativity for the points of a Γ-set.** A sum of a tuple can always be
computed by regrouping it along any partition: the single lift `z` at level `n` produces, in one
stroke, a lift at level `m` and a lift of each block. -/
theorem hadd_assoc {n m : ℕ} (p : partition n m) (A : Fin n → Set X.Points) :
    HyperAdd.set X.Points n A
      ⊆ HyperAdd.set X.Points m
          (fun j => HyperAdd.finset X.Points n (p.toFun j) fun f => A f) := by
  intro x hx
  -- unpack: a choice `a i ∈ A i`, and a lift `z` of it at level `n` summing to `x`
  simp only [HyperAdd.set, Set.mem_iUnion] at hx
  obtain ⟨a, hx⟩ := hx
  replace hx : x ∈ X.hadd n fun i => ((a i : X.Points)) := hx
  obtain ⟨z, hz, hxz⟩ := (X.mem_hadd_iff _ x).mp hx
  -- the level `m` witness is `z` regrouped along `p`
  simp only [HyperAdd.set, Set.mem_iUnion]
  refine ⟨fun j => ⟨X.proj j (X.act (N.block p) z), ?_⟩, ?_⟩
  · -- its `j`-th coordinate is a sum of the elements indexed by the `j`-th block, as witnessed
    -- by the restriction of `z` to that block
    simp only [HyperAdd.finset, Set.mem_iUnion]
    refine ⟨fun i => a (i : Fin n), ?_⟩
    rw [X.proj_act_block p j z]
    exact X.mem_hadd fun k =>
      (hz (((p.toFun j).orderIsoOfFin rfl k : Fin n))).trans
        (X.proj_act_restr (p.toFun j) k z).symm
  · -- and the regrouping still sums to `x`
    rw [← (X.add_act_block p z).trans hxz]
    exact X.mem_hadd fun _ => rfl

/-- The points of a Γ-set form an `F1module`. -/
instance : F1module X.Points where
  toHyperAdd := X.HyperAdd
  hadd_assoc p A := X.hadd_assoc p A

end GammaSet
