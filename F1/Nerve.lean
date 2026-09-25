import F1.F1moduleCat
import F1.Subsets
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The nerve of an `F1module`, right adjoint to the points functor

For an `F1module` `M` we define the Γ-set

`Nerve M (n₊) = HyperAdd.Hom (𝒫 n) M`,   pointed at the constant map `S ↦ 0`,

where `𝒫 n = Finset (Fin n)` carries the disjoint-union hyperoperation (`F1.Subsets`).  A map
`φ : n₊ ⟶ m₊` acts by precomposition with the preimage map
`pre φ : 𝒫 m → 𝒫 n`, `T ↦ {i | φ i.succ ∈ T.succ}`.

`𝒫 n` is the value at `1₊` of the representable Γ-set `N(n₊, -)`, so this is the usual nerve
construction.  For a commutative monoid, `a (S) = ∑_{i ∈ S} a {i}` is forced, so
`Nerve M (n₊) ≅ Mⁿ` and `Nerve` generalises `HM`.

* `Nerve.nerveFunctor : F1moduleCat ⥤ GammaSpace`;
* `Nerve.adj : GammaSpace.toF1moduleCat ⊣ Nerve.nerveFunctor`.

## Why `HyperAdd.Hom` and not `F1module.Hom`

The levels of the nerve are *all* weak morphisms `𝒫 n → M`, not only those sending `∅` to
`0`.  Such an `a` still satisfies `a ∅ ∈ hadd 0 ()`, since `∅` is the empty sum in `𝒫 n`, and
the constant map at `0` is one of them precisely because of `F1module.zero_mem`.  With
zero-preserving levels the adjunction would fail for non-reduced Γ-sets.  For instance, for the
constant Γ-set `X` at a pointed type `A`, naturality along zero maps forces every `X ⟶ Nerve M`
to be trivial, while `hom (X 1₊, M)` need not be.  The zero-preserving condition on
*morphisms* of `F1module`s is still what makes `Nerve` a functor into pointed objects.

## The adjunction

Write `χ_S = N.ind S : n₊ ⟶ 1₊` for the indicator of `S`.

* `toNerve f : X ⟶ Nerve M`, for `f : X 1₊ → M`, is `z ↦ (S ↦ f (X χ_S z))`.  That this is a
  weak morphism uses `N.sep S : n₊ ⟶ k₊` for a disjoint family `S`: it sends `S r` to `r` and
  the complement to the basepoint.  It is `N.block` for the partition `(S₀, …, S_{k-1}, rest)`
  followed by the collapse of the last block, which we write down directly.  The identities
  `sep S ≫ proj r = χ_{S r}` and `sep S ≫ add = χ_{⋃ S}` exhibit `X (sep S) z` as a lift of
  `(X χ_{S r} z)_r` with sum `X χ_{⋃ S} z`.
* `fromNerve α : X 1₊ → M` is `x ↦ α₁ x (univ)`.  It is a weak morphism because
  `univ = ⨆ {i}` in `𝒫 k`, and `pre add univ = univ`, `pre (proj i) univ = {i}`.
* The round trips come from `χ_univ = 𝟙 1₊` and `pre χ_S univ = S`.

As in `F1.spherical_adjunction`, level-wise statements use `n m : ℕ` and `N.mk`, `N.unmk` is
used wherever a natural transformation hands us an `n : N`, and elements of `Nerve M` are
evaluated through `Nerve.ev` rather than through a coercion, because instance search does
not unfold `Functor.obj`.
-/

open CategoryTheory Finset

/-! ## Indicator and separation maps in `N` -/

namespace N

/-- The function underlying `N.ind S`: `i.succ ↦ 1` if `i ∈ S`, and `0` otherwise. -/
def indFun {n : ℕ} (S : Finset (Fin n)) : Fin (n + 1) → Fin 2 :=
  Fin.cons 0 fun i => if i ∈ S then 1 else 0

@[simp] theorem indFun_zero {n : ℕ} (S : Finset (Fin n)) : indFun S 0 = 0 := rfl

theorem indFun_succ {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    indFun S i.succ = if i ∈ S then 1 else 0 := rfl

/-- The indicator `χ_S : n₊ ⟶ 1₊` of a subset `S ⊆ {1, …, n}`.  The elements of
`Hom_N (n₊, 1₊)` are exactly the `ind S`. -/
def ind {n : ℕ} (S : Finset (Fin n)) : mk n ⟶ mk 1 := ofFun (indFun S) rfl

/-- `χ_{1} = 𝟙 1₊`. -/
theorem ind_univ_one : ind (univ : Finset (Fin 1)) = 𝟙 (mk 1) := by
  refine hom_ext_of_succ ?_
  intro i
  change (if i ∈ (univ : Finset (Fin 1)) then (1 : Fin 2) else 0) = i.succ
  rw [ite_eq_left (Finset.mem_univ i), fin1_eq_zero i, succ_zero_one]

/-- The function underlying `N.sep S`: an element of some `S r` is sent to `r`, everything
else to the basepoint.  For a disjoint family `r` is unique. -/
noncomputable def sepFun {n k : ℕ} (S : Fin k → Finset (Fin n)) : Fin (n + 1) → Fin (k + 1) :=
  Fin.cons 0 fun i => if h : ∃ r, i ∈ S r then h.choose.succ else 0

@[simp] theorem sepFun_zero {n k : ℕ} (S : Fin k → Finset (Fin n)) : sepFun S 0 = 0 := rfl

theorem sepFun_succ_eq_succ_iff {n k : ℕ} {S : Fin k → Finset (Fin n)}
    (hS : Pairwise fun r r' => Disjoint (S r) (S r')) (i : Fin n) (r : Fin k) :
    sepFun S i.succ = r.succ ↔ i ∈ S r := by
  change (if h : ∃ r, i ∈ S r then h.choose.succ else 0) = r.succ ↔ i ∈ S r
  by_cases h : ∃ r, i ∈ S r
  · rw [dite_eq_left h, Fin.succ_inj]
    constructor
    · rintro rfl
      exact h.choose_spec
    · intro hr
      by_contra hne
      exact Finset.disjoint_left.mp (hS hne) h.choose_spec hr
  · rw [dite_eq_right h]
    exact ⟨fun hc => absurd hc.symm (Fin.succ_ne_zero r), fun hr => absurd ⟨r, hr⟩ h⟩

theorem sepFun_succ_eq_zero_iff {n k : ℕ} (S : Fin k → Finset (Fin n)) (i : Fin n) :
    sepFun S i.succ = 0 ↔ ¬ ∃ r, i ∈ S r := by
  change (if h : ∃ r, i ∈ S r then h.choose.succ else 0) = 0 ↔ ¬ ∃ r, i ∈ S r
  by_cases h : ∃ r, i ∈ S r
  · rw [dite_eq_left h]
    exact ⟨fun hc => absurd hc (Fin.succ_ne_zero _), fun hc => absurd h hc⟩
  · rw [dite_eq_right h]
    exact ⟨fun _ => h, fun _ => rfl⟩

/-- The separation map `n₊ ⟶ k₊` of a family of subsets: `S r ↦ r`, the rest to `0`. -/
noncomputable def sep {n k : ℕ} (S : Fin k → Finset (Fin n)) : mk n ⟶ mk k :=
  ofFun (sepFun S) rfl

/-- For a disjoint family, projecting to `r` after separating is the indicator of `S r`. -/
theorem sep_comp_proj {n k : ℕ} {S : Fin k → Finset (Fin n)}
    (hS : Pairwise fun r r' => Disjoint (S r) (S r')) (r : Fin k) :
    sep S ≫ map_proj r = ind (S r) := by
  refine hom_ext_of_succ ?_
  intro i
  change (if sepFun S i.succ = r.succ then (1 : Fin 2) else 0)
      = (if i ∈ S r then (1 : Fin 2) else 0)
  by_cases h : i ∈ S r
  · rw [ite_eq_left ((sepFun_succ_eq_succ_iff hS i r).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h ((sepFun_succ_eq_succ_iff hS i r).mp hc)), ite_eq_right h]

/-- Summing after separating is the indicator of the union. -/
theorem sep_comp_add {n k : ℕ} (S : Fin k → Finset (Fin n)) :
    sep S ≫ map_add k = ind (univ.biUnion S) := by
  refine hom_ext_of_succ ?_
  intro i
  change (if sepFun S i.succ = 0 then (0 : Fin 2) else 1)
      = (if i ∈ univ.biUnion S then (1 : Fin 2) else 0)
  have hmem : i ∈ univ.biUnion S ↔ ∃ r, i ∈ S r := by simp
  by_cases h : ∃ r, i ∈ S r
  · rw [ite_eq_right (fun hc => (sepFun_succ_eq_zero_iff S i).mp hc h), ite_eq_left (hmem.mpr h)]
  · rw [ite_eq_left ((sepFun_succ_eq_zero_iff S i).mpr h), ite_eq_right (fun hc => h (hmem.mp hc))]

end N

/-! ## Preimages -/

namespace Nerve

/-- The preimage of `T ⊆ {1, …, m}` under a pointed map `φ : n₊ → m₊`, as a subset of
`{1, …, n}`. -/
def pre {n m : ℕ} (φ : Fin (n + 1) → Fin (m + 1)) (T : Finset (Fin m)) : Finset (Fin n) :=
  univ.filter fun i => ∃ j ∈ T, φ i.succ = j.succ

theorem mem_pre {n m : ℕ} {φ : Fin (n + 1) → Fin (m + 1)} {T : Finset (Fin m)} {i : Fin n} :
    i ∈ pre φ T ↔ ∃ j ∈ T, φ i.succ = j.succ := by
  simp only [pre, Finset.mem_filter, Finset.mem_univ, true_and]

theorem disjoint_pre {n m : ℕ} (φ : Fin (n + 1) → Fin (m + 1)) {T T' : Finset (Fin m)}
    (h : Disjoint T T') : Disjoint (pre φ T) (pre φ T') := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  obtain ⟨j, hj, hφ⟩ := mem_pre.mp hi
  obtain ⟨j', hj', hφ'⟩ := mem_pre.mp hi'
  obtain rfl : j = j' := Fin.succ_injective _ (hφ.symm.trans hφ')
  exact Finset.disjoint_left.mp h hj hj'

theorem pre_biUnion {n m k : ℕ} (φ : Fin (n + 1) → Fin (m + 1)) (S : Fin k → Finset (Fin m)) :
    pre φ (univ.biUnion S) = univ.biUnion fun r => pre φ (S r) := by
  ext i
  simp only [mem_pre, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, ⟨r, hj⟩, h⟩
    exact ⟨r, j, hj, h⟩
  · rintro ⟨r, j, hj, h⟩
    exact ⟨j, ⟨r, hj⟩, h⟩

theorem pre_id {n : ℕ} (φ : Fin (n + 1) → Fin (n + 1)) (hφ : ∀ i, φ i = i)
    (T : Finset (Fin n)) : pre φ T = T := by
  ext i
  rw [mem_pre]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [hφ] at h
    rw [Fin.succ_injective _ h]
    exact hj
  · intro hi
    exact ⟨i, hi, hφ _⟩

theorem pre_comp {n m k : ℕ} (φ : Fin (n + 1) → Fin (m + 1)) (ψ : Fin (m + 1) → Fin (k + 1))
    (χ : Fin (n + 1) → Fin (k + 1)) (hχ : ∀ i, χ i = ψ (φ i)) (hψ : ψ 0 = 0)
    (T : Finset (Fin k)) : pre χ T = pre φ (pre ψ T) := by
  ext i
  simp only [mem_pre, hχ]
  constructor
  · rintro ⟨l, hl, h⟩
    rcases Fin.eq_zero_or_eq_succ (φ i.succ) with h0 | ⟨j, hj⟩
    · -- `i` goes to the basepoint, so it is in no preimage
      rw [h0, hψ] at h
      exact absurd h.symm (Fin.succ_ne_zero l)
    · rw [hj] at h
      exact ⟨j, ⟨l, hl, h⟩, hj⟩
  · rintro ⟨j, ⟨l, hl, h⟩, hj⟩
    exact ⟨l, hl, by rw [hj]; exact h⟩

/-- Preimages along a pointed map form a morphism `𝒫 m → 𝒫 n`: they preserve disjointness
and unions. -/
def preHom {n m : ℕ} (φ : Fin (n + 1) → Fin (m + 1)) :
    HyperAdd.Hom (Finset (Fin m)) (Finset (Fin n)) where
  toFun := pre φ
  map_hadd k S := by
    rintro _ ⟨T, hT, rfl⟩
    obtain ⟨hdisj, rfl⟩ := Subsets.mem_hadd_iff.mp hT
    exact Subsets.mem_hadd_iff.mpr
      ⟨fun r r' hrr' => disjoint_pre φ (hdisj hrr'), pre_biUnion φ S⟩

/-- `Fin k` is the disjoint union of its singletons in `𝒫 k`. -/
theorem univ_mem_hadd_singleton (k : ℕ) :
    (univ : Finset (Fin k)) ∈ hadd k (fun i => ({i} : Finset (Fin k))) :=
  Subsets.mem_hadd_iff.mpr ⟨fun _ _ hij => Finset.disjoint_singleton.mpr hij, by ext x; simp⟩
/-! ### Preimages of the maps `n₊ ⟶ 1₊` -/

/-- For `φ : n₊ ⟶ 1₊`, the preimage of `{1}` is the set where `φ` takes the value `1`. -/
theorem mem_pre_univ_one {n : ℕ} {φ : Fin (n + 1) → Fin 2} {i : Fin n} :
    i ∈ pre φ (univ : Finset (Fin 1)) ↔ φ i.succ = 1 := by
  rw [mem_pre]
  constructor
  · rintro ⟨j, -, h⟩
    rw [N.fin1_eq_zero j, N.succ_zero_one] at h
    exact h
  · intro h
    exact ⟨0, Finset.mem_univ _, h.trans N.succ_zero_one.symm⟩

theorem pre_ind_univ {n : ℕ} (S : Finset (Fin n)) : pre (N.indFun S) univ = S := by
  ext i
  rw [mem_pre_univ_one, N.indFun_succ]
  by_cases h : i ∈ S
  · rw [ite_eq_left h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [ite_eq_right h]
    exact ⟨fun hc => absurd hc (by decide), fun hc => absurd hc h⟩

theorem pre_map_add_univ (n : ℕ) :
    pre (Pointed.Hom.toFun (N.map_add n)) (univ : Finset (Fin 1)) = univ := by
  ext i
  rw [mem_pre_univ_one]
  change (if i.succ = 0 then (0 : Fin 2) else 1) = 1 ↔ i ∈ univ
  rw [ite_eq_right (Fin.succ_ne_zero i)]
  exact ⟨fun _ => Finset.mem_univ i, fun _ => rfl⟩

theorem pre_map_proj_univ {n : ℕ} (r : Fin n) :
    pre (Pointed.Hom.toFun (N.map_proj r)) (univ : Finset (Fin 1)) = {r} := by
  ext i
  rw [mem_pre_univ_one, Finset.mem_singleton]
  change (if i.succ = r.succ then (1 : Fin 2) else 0) = 1 ↔ i = r
  by_cases h : i = r
  · rw [ite_eq_left (congrArg Fin.succ h)]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [ite_eq_right (fun hc => h (Fin.succ_injective _ hc))]
    exact ⟨fun hc => absurd hc (by decide), fun hc => absurd hc h⟩

/-- Precomposing an indicator: `g ≫ χ_T = χ_{g⁻¹ T}`. -/
theorem comp_ind {n m : ℕ} (g : N.mk n ⟶ N.mk m) (T : Finset (Fin m)) :
    g ≫ N.ind T = N.ind (pre (Pointed.Hom.toFun g) T) := by
  refine N.hom_ext_of_succ ?_
  intro i
  change N.indFun T (Pointed.Hom.toFun g i.succ)
      = (if i ∈ pre (Pointed.Hom.toFun g) T then (1 : Fin 2) else 0)
  rcases Fin.eq_zero_or_eq_succ (Pointed.Hom.toFun g i.succ) with h0 | ⟨j, hj⟩
  · have hi : i ∉ pre (Pointed.Hom.toFun g) T := fun hi => by
      obtain ⟨j, -, hj⟩ := mem_pre.mp hi
      exact Fin.succ_ne_zero j (hj.symm.trans h0)
    rw [h0]
    exact (ite_eq_right hi).symm
  · have hiff : i ∈ pre (Pointed.Hom.toFun g) T ↔ j ∈ T := by
      rw [mem_pre]
      constructor
      · rintro ⟨j', hj', h⟩
        rw [hj] at h
        rw [Fin.succ_injective _ h]
        exact hj'
      · intro hjT
        exact ⟨j, hjT, hj⟩
    rw [hj, N.indFun_succ]
    by_cases hjT : j ∈ T
    · rw [ite_eq_left hjT, ite_eq_left (hiff.mpr hjT)]
    · rw [ite_eq_right hjT, ite_eq_right (fun hc => hjT (hiff.mp hc))]

/-! ## The levels of the nerve -/

variable {M : Type} [F1module M]

/-- The constant map at `0`.  It is a weak morphism exactly because of `F1module.zero_mem`. -/
def zeroHom (P : Type) [HyperAdd P] (M : Type) [F1module M] : HyperAdd.Hom P M where
  toFun _ := F1module.zero
  map_hadd k S := by
    rintro _ ⟨T, -, rfl⟩
    exact F1module.zero_mem k

/-- The action of `φ : n₊ ⟶ m₊` on the levels of the nerve: precomposition with `pre φ`. -/
def mapFun {n m : ℕ} (φ : Fin (n + 1) → Fin (m + 1)) (a : HyperAdd.Hom (Finset (Fin n)) M) :
    HyperAdd.Hom (Finset (Fin m)) M :=
  a.comp (preHom φ)

theorem mapFun_apply {n m : ℕ} (φ : Fin (n + 1) → Fin (m + 1))
    (a : HyperAdd.Hom (Finset (Fin n)) M) (T : Finset (Fin m)) :
    mapFun φ a T = a (pre φ T) := rfl

theorem mapFun_zero {n m : ℕ} (φ : Fin (n + 1) → Fin (m + 1)) :
    mapFun φ (zeroHom (Finset (Fin n)) M) = zeroHom (Finset (Fin m)) M :=
  HyperAdd.Hom.ext fun _ => rfl

theorem mapFun_id {n : ℕ} (φ : Fin (n + 1) → Fin (n + 1)) (hφ : ∀ i, φ i = i)
    (a : HyperAdd.Hom (Finset (Fin n)) M) : mapFun φ a = a :=
  HyperAdd.Hom.ext fun T => congrArg (⇑a) (pre_id φ hφ T)

theorem mapFun_comp {n m k : ℕ}
    (φ : Fin (n + 1) → Fin (m + 1)) (ψ : Fin (m + 1) → Fin (k + 1))
    (χ : Fin (n + 1) → Fin (k + 1)) (hχ : ∀ i, χ i = ψ (φ i)) (hψ : ψ 0 = 0)
    (a : HyperAdd.Hom (Finset (Fin n)) M) : mapFun χ a = mapFun ψ (mapFun φ a) :=
  HyperAdd.Hom.ext fun T => congrArg (⇑a) (pre_comp φ ψ χ hχ hψ T)

end Nerve

open Nerve in
/-- **The nerve of an `F1module`**: `n₊ ↦ HyperAdd.Hom (𝒫 n) M`, pointed at the constant map
at `0`, with `φ` acting by precomposition with preimages. -/
def Nerve (M : Type) [F1module M] : GammaSet where
  F := {
  obj n := ⟨HyperAdd.Hom (Finset (Fin (N.unmk n))) M, zeroHom _ M⟩
  map := fun {n m} f => ⟨mapFun (Pointed.Hom.toFun f), mapFun_zero (Pointed.Hom.toFun f)⟩
  map_id := fun n => by
    apply Pointed.hom_ext'
    intro a
    exact mapFun_id _ (fun i => rfl) a
  map_comp := fun {n m k} f g => by
    apply Pointed.hom_ext'
    intro a
    exact mapFun_comp (Pointed.Hom.toFun f) (Pointed.Hom.toFun g) _ (fun i => rfl)
      g.map_point a}
  reduced := sorry

namespace Nerve

variable {M M' : Type} [F1module M] [F1module M']

/-! ## Evaluating elements of the nerve -/

/-- Evaluation of an element of `Nerve M` at level `n` on a subset.  Use this instead of a
coercion: instance search does not see through `(Nerve M).obj`. -/
def ev {n : ℕ} (a : ((Nerve M).F.obj (N.mk n)).X) (T : Finset (Fin n)) : M :=
  HyperAdd.Hom.toFun (X := Finset (Fin n)) (Y := M) a T

/-- Elements of the nerve are determined by their values. -/
theorem ext {n : ℕ} {a b : ((Nerve M).F.obj (N.mk n)).X}
    (h : ∀ T : Finset (Fin n), ev a T = ev b T) : a = b :=
  HyperAdd.Hom.ext (X := Finset (Fin n)) (Y := M) h

@[simp] theorem ev_point {n : ℕ} (T : Finset (Fin n)) :
    ev ((Nerve M).F.obj (N.mk n)).point T = (F1module.zero : M) := rfl

@[simp] theorem ev_map {n m : ℕ} (g : N.mk n ⟶ N.mk m)
    (a : ((Nerve M).F.obj (N.mk n)).X)
    (T : Finset (Fin m)) :
    ev (Pointed.Hom.toFun ((Nerve M).F.map g) a) T = ev a (pre (Pointed.Hom.toFun g) T) := rfl

/-- The value on `univ` is a sum of the values on the singletons. -/
theorem ev_univ_mem {k : ℕ} (a : ((Nerve M).F.obj (N.mk k)).X) :
    ev a univ ∈ hadd k (fun i => ev a {i}) :=
  HyperAdd.Hom.mem_hadd_of_mem_hadd (X := Finset (Fin k)) (Y := M) a k
    (fun i => ({i} : Finset (Fin k))) (univ_mem_hadd_singleton k)

theorem ev_mem_of {k : ℕ} (a : ((Nerve M).F.obj (N.mk k)).X) (x : M) (v : Fin k → M)
    (hx : x = ev a univ) (hv : ∀ i, v i = ev a {i}) : x ∈ hadd k v := by
  have hv' : v = fun i => ev a {i} := funext hv
  subst hv'
  subst hx
  exact ev_univ_mem a

/-! ## Functoriality in `M` -/

/-- Postcomposition with a morphism of `F1module`s, at level `n`. -/
def hMapApp (h : F1module.Hom M M') (n : ℕ) :
    (Nerve M).F.obj (N.mk n) ⟶ (Nerve M').F.obj (N.mk n) where
  toFun a := HyperAdd.Hom.comp (X := Finset (Fin n)) h.toHom a
  map_point := Nerve.ext fun _ => h.map_zero

/-- A morphism of `F1module`s induces a morphism of nerves, by postcomposition.  Pointedness
is where zero-preservation of `h` is used. -/
def hMap (h : F1module.Hom M M') : Nerve M ⟶ Nerve M' where
  app n := hMapApp h (N.unmk n)
  naturality := by
    intro n m f
    apply Pointed.hom_ext'
    intro a
    rfl

/-- **The nerve functor** `F1moduleCat ⥤ GammaSpace`. -/
def nerveFunctor : F1moduleCat.{0} ⥤ GammaSet where
  obj M := Nerve M
  map h := hMap h.hom
  map_id M := by
    apply preGammaSet.hom_ext
    intro n
    apply Pointed.hom_ext'
    intro a
    rfl
  map_comp f g := by
    apply preGammaSet.hom_ext
    intro n
    apply Pointed.hom_ext'
    intro a
    rfl

@[simp] theorem nerveFunctor_obj (M : F1moduleCat.{0}) : nerveFunctor.obj M = Nerve M := rfl

/-! ## From `X 1₊ → M` to `X ⟶ Nerve M` -/

variable {X : GammaSet}

/-- The element of `Nerve M (n₊)` attached to `z : X n₊`: `S ↦ f (X χ_S z)`.

It is a weak morphism: if `T = ⨆ S r`, then `X (sep S) z` is a lift of `(X χ_{S r} z)_r` with
sum `X χ_T z`, so `X χ_T z ∈ hadd (X χ_{S r} z)_r`, and `f` preserves this. -/
def toNerveFun (f : F1module.Hom X.Points M) (n : ℕ) (z : X.Level n) :
    HyperAdd.Hom (Finset (Fin n)) M where
  toFun S := f (X.act (N.ind S) z)
  map_hadd k S := by
    rintro _ ⟨T, hT, rfl⟩
    obtain ⟨hdisj, rfl⟩ := Subsets.mem_hadd_iff.mp hT
    have hw : X.act (N.ind (univ.biUnion S)) z
        ∈ X.hadd k (fun r => X.act (N.ind (S r)) z) := by
      rw [← X.act_congr (N.sep_comp_add S) z, ← X.act_comp, ← X.add_eq_act]
      exact X.mem_hadd fun r =>
        (X.act_congr (N.sep_comp_proj hdisj r) z).symm.trans (X.act_comp _ _ z).symm
    exact f.mem_hadd_of_mem_hadd k _ hw

/-- The level `n` component of `toNerve f`. -/
def toNerveApp (f : F1module.Hom X.Points M) (n : ℕ) :
    X.F.obj (N.mk n) ⟶ (Nerve M).F.obj (N.mk n) where
  toFun z := toNerveFun f n z
  map_point := Nerve.ext fun S =>
    (congrArg (⇑f) (Pointed.Hom.map_point (X.F.map (N.ind S)))).trans f.map_zero

theorem toNerveApp_naturality (f : F1module.Hom X.Points M) (n m : ℕ)
    (g : N.mk n ⟶ N.mk m) :
    X.F.map g ≫ toNerveApp f m = toNerveApp f n ≫ (Nerve M).F.map g := by
  apply Pointed.hom_ext'
  intro z
  refine Nerve.ext fun T => ?_
  exact congrArg (⇑f) ((X.act_comp g (N.ind T) z).trans (X.act_congr (comp_ind g T) z))

/-- The morphism of Γ-sets `X ⟶ Nerve M` attached to `f : X 1₊ → M`. -/
def toNerve (f : F1module.Hom X.Points M) : X ⟶ Nerve M where
  app n := toNerveApp f (N.unmk n)
  naturality := by
    intro n m g
    exact toNerveApp_naturality f (N.unmk n) (N.unmk m) g

/-! ## From `X ⟶ Nerve M` to `X 1₊ → M` -/

/-- Naturality of `α : X ⟶ Nerve M`, evaluated. -/
theorem ev_app_act (α : X ⟶ Nerve M) {n m : ℕ} (g : N.mk n ⟶ N.mk m) (z : X.Level n)
    (T : Finset (Fin m)) :
    ev (Pointed.Hom.toFun (NatTrans.app α (N.mk m)) (X.act g z)) T
      = ev (Pointed.Hom.toFun (NatTrans.app α (N.mk n)) z) (pre (Pointed.Hom.toFun g) T) :=
  congrArg (fun b : ((Nerve M).F.obj (N.mk m)).X => ev b T) (GammaSet.app_act α g z)

theorem fromNerve_add (α : X ⟶ Nerve M) (k : ℕ) (z : X.Level k) :
    ev (Pointed.Hom.toFun (NatTrans.app α (N.mk 1)) (X.add k z)) univ
      = ev (Pointed.Hom.toFun (NatTrans.app α (N.mk k)) z) univ :=
  (ev_app_act α (N.map_add k) z univ).trans
    (congrArg (ev (Pointed.Hom.toFun (NatTrans.app α (N.mk k)) z)) (pre_map_add_univ k))

theorem fromNerve_proj (α : X ⟶ Nerve M) {k : ℕ} (i : Fin k) (z : X.Level k) :
    ev (Pointed.Hom.toFun (NatTrans.app α (N.mk 1)) (X.proj i z)) univ
      = ev (Pointed.Hom.toFun (NatTrans.app α (N.mk k)) z) {i} :=
  (ev_app_act α (N.map_proj i) z univ).trans
    (congrArg (ev (Pointed.Hom.toFun (NatTrans.app α (N.mk k)) z)) (pre_map_proj_univ i))

/-- The map `X 1₊ → M` attached to `α : X ⟶ Nerve M`: `x ↦ α₁ x ({1})`.

It is a weak morphism: if `x = add z` with `v i = proj i z`, then with `a = α_k z` one has
`α₁ x {1} = a univ` and `α₁ (v i) {1} = a {i}`, and `a univ ∈ hadd (a {i})_i` because
`univ = ⨆ {i}` in `𝒫 k`. -/
def fromNerve (α : X ⟶ Nerve M) : F1module.Hom X.Points M where
  toFun x := ev (Pointed.Hom.toFun (NatTrans.app α (N.mk 1)) x) univ
  map_hadd k v := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (X.mem_hadd_iff v x).mp hx
    exact ev_mem_of (Pointed.Hom.toFun (NatTrans.app α (N.mk k)) z) _ _
      (fromNerve_add α k z)
      (fun i => (congrArg (fun y => ev (Pointed.Hom.toFun (NatTrans.app α (N.mk 1)) y) univ)
        (hz i)).trans (fromNerve_proj α i z))
  map_zero' := congrArg (fun b : ((Nerve M).F.obj (N.mk 1)).X => ev b univ)
    (Pointed.Hom.map_point (NatTrans.app α (N.mk 1)))

/-! ## The two round trips -/

/-- `fromNerve (toNerve f) = f`, since `χ_{1} = 𝟙 1₊`. -/
theorem fromNerve_toNerve (f : F1module.Hom X.Points M) : fromNerve (toNerve f) = f := by
  apply F1module.Hom.ext
  intro x
  exact (congrArg (⇑f) (X.act_congr N.ind_univ_one x)).trans
    (congrArg (⇑f) (congrArg (fun h => Pointed.Hom.toFun h x) (X.F.map_id (N.mk 1))))

/-- `toNerve (fromNerve α) = α` at level `n`: this is naturality of `α` along `χ_S`, together
with `pre χ_S {1} = S`. -/
theorem toNerve_fromNerve_app (α : X ⟶ Nerve M) (n : ℕ) :
    NatTrans.app (toNerve (fromNerve α)) (N.mk n) = NatTrans.app α (N.mk n) := by
  apply Pointed.hom_ext'
  intro z
  refine Nerve.ext fun S => ?_
  exact (ev_app_act α (N.ind S) z univ).trans
    (congrArg (ev (Pointed.Hom.toFun (NatTrans.app α (N.mk n)) z)) (pre_ind_univ S))

theorem toNerve_fromNerve (α : X ⟶ Nerve M) : toNerve (fromNerve α) = α :=
  preGammaSet.hom_ext fun n => toNerve_fromNerve_app α (N.unmk n)

/-! ## The adjunction -/

/-- **The hom-set bijection**: morphisms of `F1module`s `X 1₊ → M` correspond to morphisms of
Γ-sets `X ⟶ Nerve M`. -/
def homEquiv (X : GammaSet) (M : F1moduleCat.{0}) :
    (GammaSet.toF1moduleCat.obj X ⟶ M) ≃ (X ⟶ nerveFunctor.obj M) where
  toFun F := toNerve F.hom
  invFun α := F1moduleCat.ofHom (fromNerve α)
  left_inv F := F1moduleCat.hom_ext fun x => DFunLike.congr_fun (fromNerve_toNerve F.hom) x
  right_inv α := toNerve_fromNerve α

/-- **The adjunction**: the points functor `GammaSpace ⥤ F1moduleCat` is left adjoint to the
nerve.

The unit `X ⟶ Nerve (X 1₊)` is `z ↦ (S ↦ X χ_S z)`, recording all partial sums of `z`; it is
an isomorphism for `HM M`.  The counit `Nerve M 1₊ → M` is `a ↦ a {1}`. -/
def adj : GammaSet.toF1moduleCat ⊣ nerveFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      -- both sides send `x` to `β₁ (α₁ x) {1}`
      homEquiv_naturality_left_symm := by
        intro X' X M α β
        apply F1moduleCat.hom_ext
        intro x
        rfl
      -- both sides send `z` to `S ↦ h (F (X χ_S z))`
      homEquiv_naturality_right := by
        intro X M M' F h
        apply preGammaSet.hom_ext
        intro n
        apply Pointed.hom_ext'
        intro z
        rfl }

/-! ## Sanity checks -/

example (M : Type) [F1module M] (n : ℕ) :
    ((Nerve M).F.obj (N.mk n)).X = HyperAdd.Hom (Finset (Fin n)) M := rfl

example (X : GammaSet) (M : F1moduleCat.{0}) (F : GammaSet.toF1moduleCat.obj X ⟶ M)
    (n : ℕ) (z : X.Level n) (S : Finset (Fin n)) :
    ev (Pointed.Hom.toFun (NatTrans.app ((homEquiv X M) F) (N.mk n)) z) S
      = F.hom (X.act (N.ind S) z) := rfl

end Nerve
