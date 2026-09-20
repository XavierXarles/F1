import F1.N
import F1.Gamma
import Init.Data.Fin.Lemmas
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
/-! HM -/

open CategoryTheory

universe u

namespace HM

variable {M : Type u} [AddCommMonoid M]

/-- The underlying function of `HM M` on a morphism, expressed in terms of the
underlying map `φ : Fin (n+1) → Fin (m+1)` of pointed sets:
`(m₁,…,mₙ) ↦ (∑_{φ(i)=1} mᵢ, …, ∑_{φ(i)=m} mᵢ)`.
Indices `i : Fin n` are the non-basepoint elements `i.succ` of `Fin (n+1)`. -/
def mapFun {n m : ℕ} (φ : Fin (n + 1) → Fin (m + 1)) (a : Fin n → M) (j : Fin m) : M :=
  ∑ i : Fin n, if φ i.succ = j.succ then a i else 0

lemma mapFun_zero {n m : ℕ} (φ : Fin (n + 1) → Fin (m + 1)) :
    mapFun φ (fun _ => (0 : M)) = fun _ => (0 : M) := by
  funext j; simp [mapFun]

lemma mapFun_id {n : ℕ} (φ : Fin (n + 1) → Fin (n + 1)) (hφ : ∀ i, φ i = i)
    (a : Fin n → M) : mapFun φ a = a := by
  funext j; simp [mapFun, hφ]

lemma mapFun_comp {n m k : ℕ}
    (φ : Fin (n + 1) → Fin (m + 1)) (ψ : Fin (m + 1) → Fin (k + 1))
    (χ : Fin (n + 1) → Fin (k + 1)) (hχ : ∀ i, χ i = ψ (φ i)) (hψ : ψ 0 = 0)
    (a : Fin n → M) : mapFun χ a = mapFun ψ (mapFun φ a) := by
  funext l
  simp only [mapFun, hχ]
  calc (∑ i : Fin n, if ψ (φ i.succ) = l.succ then a i else 0)
      = ∑ i : Fin n, ∑ j : Fin m,
          (if φ i.succ = j.succ then (if ψ j.succ = l.succ then a i else 0) else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rcases Fin.eq_zero_or_eq_succ (φ i.succ) with h | ⟨j₀, h⟩
        · -- `i` is sent to the basepoint: it contributes to nothing
          rw [h, hψ, ite_eq_right (Ne.symm (Fin.succ_ne_zero l))]
          exact (Finset.sum_eq_zero fun j _ => ite_eq_right (Ne.symm (Fin.succ_ne_zero j))).symm
        · -- `i` is sent to `j₀`: only the `j₀` summand survives
          rw [h]; simp
    _ = ∑ j : Fin m, ∑ i : Fin n,
          (if φ i.succ = j.succ then (if ψ j.succ = l.succ then a i else 0) else 0) :=
        Finset.sum_comm
    _ = ∑ j : Fin m, if ψ j.succ = l.succ then
          (∑ i : Fin n, if φ i.succ = j.succ then a i else 0) else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : ψ j.succ = l.succ <;> simp [h]

end HM

open HM in
/-- The Eilenberg–Mac Lane `Γ`-set of a commutative monoid `M`:
`HM(n₊) = M^{⊕n}`, pointed at `(0,…,0)`. -/
def HM (M : Type 0) [AddCommMonoid M] : GammaSpace where
  obj := fun n => ⟨(Fin n → M), fun _ => (0 : M)⟩
  map := fun {n m} f => ⟨mapFun f.toFun, mapFun_zero f.toFun⟩
  map_id := fun n => by
    apply Pointed.Hom.ext
    funext a
    exact mapFun_id _ (fun i => rfl) a
  map_comp := fun {n m k} f g => by
    apply Pointed.Hom.ext
    funext a
    exact mapFun_comp f.toFun g.toFun _ (fun i => rfl) g.map_point a



namespace HM

variable {M N : Type 0} [AddCommMonoid M] [AddCommMonoid N]

/-- Applying an additive hom componentwise commutes with `mapFun`. -/
lemma mapFun_hom {n m : ℕ} (φ : Fin (n + 1) → Fin (m + 1)) (h : M →+ N) (a : Fin n → M) :
    mapFun φ (fun i => h (a i)) = fun j => h (mapFun φ a j) := by
  funext j
  simp [mapFun, map_sum, apply_ite h]


/-- An additive hom `M →+ N` induces a map of `Γ`-sets `HM M ⟶ HM N`,
given in each degree by applying `h` componentwise. -/
def hMap (h : M →+ N) : HM M ⟶ HM N where
  app n := ⟨fun a i => h (a i), by funext i; exact h.map_zero⟩
  naturality := fun {n m} f => by
    apply Pointed.Hom.ext
    funext a
    exact (mapFun_hom f.toFun h a).symm

@[simp] lemma hMap_app_toFun (h : M →+ N) (n : ℕ) (a : Fin n → M) :
    ((hMap h).app n).toFun a = fun i => h (a i) := rfl

end HM


open HM in
/-- The Eilenberg–Mac Lane functor `AddCommMonCat ⥤ GammaSpace`,
`M ↦ HM M`, `h ↦ h` applied componentwise. -/
def HMFunctor : AddCommMonCat ⥤ GammaSpace where
  obj M := HM M
  map f := hMap f.hom
  map_id M := by
    apply NatTrans.ext
    funext n
    apply Pointed.Hom.ext
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext n
    apply Pointed.Hom.ext
    rfl

namespace HM

variable {M M' : Type 0} [AddCommMonoid M] [AddCommMonoid M']

/-- Naturality of a morphism of `Γ`-sets, written out in coordinates. -/
lemma app_mapFun (α : HM M ⟶ HM M') {n m : ℕ} (φ : Fin (n + 1) → Fin (m + 1)) (hφ : φ 0 = 0)
    (a : Fin n → M) :
    Pointed.Hom.toFun (NatTrans.app α m) (mapFun φ a)
      = mapFun φ (Pointed.Hom.toFun (NatTrans.app α n) a) := by
  have h := NatTrans.naturality α (N.ofFun φ hφ)
  exact congrFun (congrArg Pointed.Hom.toFun h) a

/-- `p_j : n₊ ⟶ 1₊`, killing every coordinate but the `j`-th. -/
def collapseFun {n : ℕ} (j : Fin n) : Fin (n + 1) → Fin 2 :=
  fun i => if i = j.succ then 1 else 0

lemma collapseFun_zero {n : ℕ} (j : Fin n) : collapseFun j 0 = 0 :=
  ite_eq_right (Ne.symm (Fin.succ_ne_zero j))

/-- `σ : 2₊ ⟶ 1₊`, the map inducing the addition. -/
def addFun : Fin 3 → Fin 2 := fun i => if i = 0 then 0 else 1

lemma addFun_zero : addFun 0 = 0 := ite_eq_left rfl

lemma addFun_succ (i : Fin 2) : addFun i.succ = (0 : Fin 1).succ :=
  (ite_eq_right (Fin.succ_ne_zero i)).trans N.succ_zero_one.symm

/-! ### The two computations of `mapFun` that we need -/

lemma mapFun_collapseFun {n : ℕ} (j : Fin n) (a : Fin n → M) :
    mapFun (collapseFun j) a = fun _ => a j := by
  have key : ∀ i : Fin n, collapseFun j i.succ = (0 : Fin 1).succ ↔ i = j := by
    intro i
    constructor
    · intro hi
      by_contra hij
      have h0 : collapseFun j i.succ = 0 :=
        ite_eq_right fun hs : i.succ = j.succ => hij (Fin.succ_injective n hs)
      exact absurd (h0.symm.trans hi) (by decide)
    · intro hij
      exact (ite_eq_left (congrArg Fin.succ hij)).trans N.succ_zero_one.symm
  funext k
  obtain rfl := N.fin1_eq_zero k
  show mapFun (collapseFun j) a 0 = a j
  calc mapFun (collapseFun j) a 0
      = ∑ i : Fin n, if collapseFun j i.succ = (0 : Fin 1).succ then a i else 0 := rfl
    _ = if collapseFun j j.succ = (0 : Fin 1).succ then a j else 0 :=
        Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
          (fun i _ hij => ite_eq_right fun hc => hij ((key i).mp hc))
    _ = a j := ite_eq_left ((key j).mpr rfl)

lemma mapFun_addFun (a : Fin 2 → M) : mapFun addFun a = fun _ => a 0 + a 1 := by
  funext k
  obtain rfl := N.fin1_eq_zero k
  show mapFun addFun a 0 = a 0 + a 1
  calc mapFun addFun a 0
      = ∑ i : Fin 2, if addFun i.succ = (0 : Fin 1).succ then a i else 0 := rfl
    _ = ∑ i : Fin 2, a i := Finset.sum_congr rfl fun i _ => ite_eq_left (addFun_succ i)
    _ = a 0 + a 1 := Fin.sum_univ_two a

/-! ### The degree one component of a map of `Γ`-sets -/

/-- The map `M → M'` underlying `α : HM M ⟶ HM M'`, read off in degree `1`. -/
def deg1 (α : HM M ⟶ HM M') (x : M) : M' :=
  Pointed.Hom.toFun (NatTrans.app α (1 : ℕ)) (fun _ => x) 0

lemma deg1_zero (α : HM M ⟶ HM M') : deg1 α 0 = 0 :=
  congrFun (Pointed.Hom.map_point (NatTrans.app α (1 : ℕ))) 0

/-- `α` is determined, in every degree, by its degree one component. -/
lemma deg1_spec (α : HM M ⟶ HM M') {n : ℕ} (a : Fin n → M) (j : Fin n) :
    Pointed.Hom.toFun (NatTrans.app α n) a j = deg1 α (a j) := by
  have h := congrFun (app_mapFun α (collapseFun j) (collapseFun_zero j) a) 0
  simp_rw [mapFun_collapseFun] at h
  rw [mapFun_collapseFun j ((α.app n).toFun a)] at h
  exact h.symm

lemma deg1_add' (α : HM M ⟶ HM M') (a : Fin 2 → M) :
    deg1 α (a 0 + a 1) = deg1 α (a 0) + deg1 α (a 1) := by
  have h0 := congrFun (app_mapFun α addFun addFun_zero a) 0
  rw [mapFun_addFun, deg1_spec] at h0
  rw [mapFun_addFun ((α.app (2:ℕ)).toFun a),deg1_spec,deg1_spec] at h0
  exact h0

lemma deg1_add (α : HM M ⟶ HM M') (x y : M) : deg1 α (x + y) = deg1 α x + deg1 α y := by
  have h := deg1_add' α (fun i : Fin 2 => if i = 0 then x else y)
  have e1 : (if (1 : Fin 2) = 0 then x else y) = y := ite_eq_right (by decide)
  simp only [e1] at h
  exact h

/-- The additive hom underlying a map of `Γ`-sets. -/
def toAddMonoidHom (α : HM M ⟶ HM M') : M →+ M' where
  toFun := deg1 α
  map_zero' := deg1_zero α
  map_add' := deg1_add α

/-- Every map of `Γ`-sets between Eilenberg–Mac Lane `Γ`-sets is induced by an additive hom. -/
lemma hMap_toAddMonoidHom (α : HM M ⟶ HM M') : hMap (toAddMonoidHom α) = α := by
  apply NatTrans.ext
  funext n
  apply Pointed.Hom.ext
  funext a
  funext j
  exact (deg1_spec α a j).symm

end HM

lemma HMFunctor.Faithful : HMFunctor.Faithful where
  map_injective := by
    intro M M' f g h
    ext x
    -- `deg1 (hMap f.hom) = f.hom` holds by definition, so `h` is exactly what we need
    have h' : HM.deg1 (HMFunctor.map f) x = HM.deg1 (HMFunctor.map g) x := by rw [h]
    exact h'

lemma HMFunctor.Full : HMFunctor.Full where
  map_surjective := by
    intro M M' α
    exact ⟨AddCommMonCat.ofHom (HM.toAddMonoidHom α), HM.hMap_toAddMonoidHom α⟩
