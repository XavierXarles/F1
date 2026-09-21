import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.Algebra.BigOperators.Fin
/-! The naturals as category Gamma^op called N -/
universe u

open CategoryTheory

/-- The pointed finite set `n₊ = {0, 1, …, n}`, realized as `Fin (n + 1)` pointed
at `0`, viewed as an object of the category `Pointed` of pointed types. -/
abbrev PointedFin (n : ℕ) : Pointed :=
  Pointed.of (0 : Fin (n + 1))

/-- The category `N` (Segal's category `Γ` / category of pointed finite sets).

Objects are natural numbers `n : ℕ`, standing for the pointed finite set
`n₊ = {0, 1, …, n}` via `PointedFin`. We build the `Category N` instance by
hand: `Hom n m` is *defined to be* `PointedFin n ⟶ PointedFin m` in `Pointed`,
and `id`/`comp` are literally `Pointed`'s `id`/`comp`. -/
def N : Type := ℕ

namespace N

instance : Category N where
  Hom n m := PointedFin n ⟶ PointedFin m
  id n := 𝟙 (PointedFin n)
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- `n₊` as an object of `N`. -/
def mk (n : ℕ) : N := n

@[simp]
def unmk (n : N) : ℕ := by trivial

/-- A morphism `n₊ ⟶ m₊` in `N` is by definition a pointed map
`Fin (n + 1) → Fin (m + 1)`, i.e. a function sending `0` to `0`. -/
example (n m : ℕ) : (mk n ⟶ mk m) = Pointed.Hom (PointedFin n) (PointedFin m) := rfl

/-- A pointed map `Fin (n+1) → Fin (m+1)`, viewed as a morphism `n₊ ⟶ m₊` of `N`. -/
def ofFun {n m : ℕ} (φ : Fin (n + 1) → Fin (m + 1)) (hφ : φ 0 = 0) : mk n  ⟶ mk m  :=
  Pointed.Hom.mk φ hφ

/-- The morphism viewed as pointed map. -/
def toFun {n m : N} (f : n ⟶ m) : PointedFin n ⟶ PointedFin m := by
  trivial

/-- The map that gives the n addition. -/
def map_add n : mk n  ⟶ mk 1  :=
  ofFun (fun i => if i = 0 then 0 else 1) (Fin.eq_of_val_eq rfl)

/-- The projection to the j-th coordinate of n_+, where the coordinates go from 0 to n-1 -/
def map_proj {n : ℕ} (j : Fin n) : mk n  ⟶ mk 1  :=
  ofFun (fun i => if i = j.succ then 1 else 0) (Fin.eq_of_val_eq rfl)

/-- The projection to the j-th coordinate of n_+, where the coordinates go from 0 to n-1 -/
def map_proj' (n j : ℕ) : mk n  ⟶ mk 1  :=
  ofFun (fun i => if i = j.succ then 1 else 0) (Fin.eq_of_val_eq rfl)

/-- The map from n_+ to m_+ given by the identity (it is an inclusion
or the identity or a projection depending if n < m, n = m or n > m). -/
def map_inc (n m : ℕ) : mk n  ⟶ mk m :=
  ofFun (fun i => if h: i < m + 1 then ⟨i, h⟩ else 0) (by grind)

lemma succ_zero_one : (0 : Fin 1).succ = (1 : Fin 2) := by decide

lemma fin1_eq_zero : ∀ k : Fin 1, k = 0 := by decide


/-- The unique pointed map `n₊ ⟶ 0₊`. -/
def toZero (n : ℕ) : mk n ⟶ mk 0 := ofFun (fun _ => 0) rfl

/-- The (basepoint) map `0₊ ⟶ n₊`. -/
def fromZero (n : ℕ) : mk 0 ⟶ mk n := ofFun (fun _ => 0) rfl

/-- The function underlying `N.pt i`: it sends `0 ↦ 0` and `1 ↦ i`. -/
def ptFun {n : ℕ} (i : Fin (n + 1)) : Fin 2 → Fin (n + 1) :=
  fun j => if j = 0 then 0 else i

@[simp] lemma ptFun_zero {n : ℕ} (i : Fin (n + 1)) : ptFun i 0 = 0 := by
  simp [ptFun]

@[simp] lemma ptFun_one {n : ℕ} (i : Fin (n + 1)) : ptFun i 1 = i := by
  have h : ¬ ((1 : Fin 2) = 0) := by decide
  simp [ptFun, h]

lemma ptFun_of_ne {n : ℕ} (i : Fin (n + 1)) {j : Fin 2} (hj : ¬ (j = 0)) : ptFun i j = i := by
  simp [ptFun, hj]

/-- `pt i : 1₊ ⟶ n₊` is the pointed map picking out the element `i` of `n₊`.
The elements of `Hom_N (1₊, n₊)` are exactly the `pt i`, and `pt 0` is the zero map. -/
def pt {n : ℕ} (i : Fin (n + 1)) : mk 1 ⟶ mk n := ofFun (ptFun i) (ptFun_zero i)

end N
