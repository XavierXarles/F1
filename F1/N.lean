import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.Algebra.BigOperators.Fin
/-! The naturals as category Γ^op, called `N`. -/

open CategoryTheory

/-- Objects of `N` (Segal's category `Γ^op`, pointed finite sets).
The object `⟨n⟩` stands for the pointed set `n₊ = {0, 1, …, n} = Fin (n + 1)`,
pointed at `0`. The constructor is `N.mk`, written `n₊`. -/
structure N : Type where
  /-- The `n` of `n₊`. -/
  as : ℕ

namespace N

/-- `n₊` is the object `{0, 1, …, n}` of `N`. -/
scoped postfix:max "₊" => N.mk

/-- The underlying type of `X : N`, namely `Fin (X.as + 1)`. -/
@[coe] abbrev Carrier (X : N) : Type := Fin (X.as + 1)

instance : CoeSort N Type := ⟨Carrier⟩

/-- The basepoint `0` of `X`. -/
def point (X : N) : X := 0

@[simp] lemma point_eq (X : N) : X.point = 0 := rfl

/-- `X` viewed as an object of `Pointed`. -/
abbrev toPointed (X : N) : Pointed := Pointed.of (0 : X)

lemma toPointed_point (X : N) : X.toPointed.point = X.point := rfl

/-- Morphisms `X ⟶ Y` in `N` are the pointed maps `X.toPointed ⟶ Y.toPointed`;
`id`/`comp` are `Pointed`'s. -/
instance : Category N where
  Hom X Y := X.toPointed ⟶ Y.toPointed
  id X := 𝟙 X.toPointed
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- A morphism of `N` is a function between the underlying types. -/
instance {X Y : N} : CoeFun (X ⟶ Y) (fun _ => X → Y) where
  coe f := Pointed.Hom.toFun f

@[simp] lemma apply_zero {X Y : N} (f : X ⟶ Y) : f 0 = 0 :=
  Pointed.Hom.map_point f

@[simp] lemma apply_point {X Y : N} (f : X ⟶ Y) : f X.point = Y.point :=
  Pointed.Hom.map_point f

@[simp] lemma id_apply (X : N) (x : X) : (𝟙 X : X ⟶ X) x = x := rfl

@[simp] lemma comp_apply {X Y Z : N} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := rfl

@[ext]
lemma hom_ext {X Y : N} {f g : X ⟶ Y} (h : ∀ x : X, f x = g x) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  have : f = g := funext h
  subst this
  rfl

/-- A pointed map `X → Y`, viewed as a morphism `X ⟶ Y` of `N`. -/
def ofFun {X Y : N} (φ : X → Y) (hφ : φ 0 = 0) : X ⟶ Y :=
  Pointed.Hom.mk φ hφ

@[simp] lemma ofFun_apply {X Y : N} (φ : X → Y) (hφ : φ 0 = 0) (x : X) :
    ofFun φ hφ x = φ x := rfl

/- The Natural number associated to an element in N. Obsolete-/
def unmk (n : N) : ℕ := n.as

/-! ### Sanity checks for the new interface -/

example (n : ℕ) : (0 : n₊) = (n₊).point := rfl
example (n : ℕ) (i : Fin (n + 1)) : n₊ := i
example (n : ℕ) (i : n₊) : Fin (n + 1) := i
example (n : ℕ) : (n₊ : Type) = Fin (n + 1) := rfl
example (n m : ℕ) : (n₊ ⟶ m₊) = (Pointed.of (0 : Fin (n + 1)) ⟶ Pointed.of (0 : Fin (m + 1))) := rfl

/-! ### Special maps -/

/-- The map that gives the `n`-fold addition. -/
def map_add (n : ℕ) : n₊ ⟶ 1₊ :=
  ofFun (fun i => if i = 0 then 0 else 1) (Fin.eq_of_val_eq rfl)

/-- The projection to the `j`-th coordinate of `n₊`, coordinates going from `0` to `n-1`. -/
def map_proj {n : ℕ} (j : Fin n) : n₊ ⟶ 1₊ :=
  ofFun (fun i => if i = j.succ then 1 else 0) (Fin.eq_of_val_eq rfl)

/-- The projection to the `j`-th coordinate of `n₊`, with `j : ℕ`. -/
def map_proj' (n j : ℕ) : n₊ ⟶ 1₊ :=
  ofFun (fun i => if i = j.succ then 1 else 0) (Fin.eq_of_val_eq rfl)

/-- The map `n₊ ⟶ m₊` given by the identity (an inclusion, the identity or a
projection depending on whether `n < m`, `n = m` or `n > m`). -/
def map_inc (n m : ℕ) : n₊ ⟶ m₊ :=
  ofFun (fun i => if h : (i : ℕ) < m + 1 then ⟨i, h⟩ else 0) (by grind)

lemma succ_zero_one : (0 : Fin 1).succ = (1 : Fin 2) := by decide

lemma fin1_eq_zero : ∀ k : 0₊, k = 0 := by decide

/-- The unique pointed map `n₊ ⟶ 0₊`. -/
def toZero (n : ℕ) : n₊ ⟶ 0₊ := ofFun (fun _ => 0) rfl

/-- The (basepoint) map `0₊ ⟶ n₊`. -/
def fromZero (n : ℕ) : 0₊ ⟶ n₊ := ofFun (fun _ => 0) rfl

/-- The function underlying `N.pt i`: it sends `0 ↦ 0` and `1 ↦ i`. -/
def ptFun {X : N} (i : X) : 1₊ → X :=
  fun j => if j = 0 then 0 else i

@[simp] lemma ptFun_zero {X : N} (i : X) : ptFun i 0 = 0 := by
  simp [ptFun]

@[simp] lemma ptFun_one {X : N} (i : X) : ptFun i 1 = i := by
  have h : ¬ ((1 : 1₊) = 0) := by decide
  simp [ptFun, h]

lemma ptFun_of_ne {X : N} (i : X) {j : 1₊} (hj : ¬ (j = 0)) : ptFun i j = i := by
  simp [ptFun, hj]

/-- `pt i : 1₊ ⟶ X` is the pointed map picking out the element `i` of `X`.
The elements of `1₊ ⟶ X` are exactly the `pt i`, and `pt 0` is the zero map. -/
def pt {X : N} (i : X) : 1₊ ⟶ X := ofFun (ptFun i) (ptFun_zero i)

@[simp] lemma pt_apply_one {X : N} (i : X) : pt i 1 = i := ptFun_one i

end N
