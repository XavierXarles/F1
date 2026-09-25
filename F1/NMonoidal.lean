import F1.N
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The smash product on N

  The object `m₊ ∧ n₊` of `N` is realised as `(m * n)₊`, via the encoding
  `N.enc : Fin (m+1) → Fin (n+1) → Fin (m*n+1)` (`0` on the wedge, `finProdFinEquiv` off it).
  The associativity, unit and symmetry isomorphisms of `N` are `N.assocN`, `N.lamN`, …

-/

open CategoryTheory MonoidalCategory

namespace N

/-! ## The smash product on `N` -/

section Enc

variable {m n : ℕ}

/-- The encoding `m₊ × n₊ → (m n)₊` of the smash product: the wedge goes to `0`,
and `(i+1, j+1) ↦ finProdFinEquiv (i, j) + 1`. -/
def enc (i : Fin (m + 1)) (j : Fin (n + 1)) : Fin (m * n + 1) :=
  Fin.cases 0 (fun i' => Fin.cases 0 (fun j' => (finProdFinEquiv (i', j')).succ) j) i

@[simp] lemma enc_zero_left (j : Fin (n + 1)) : enc (0 : Fin (m + 1)) j = 0 := by
  simp [enc]

@[simp] lemma enc_zero_right (i : Fin (m + 1)) : enc i (0 : Fin (n + 1)) = 0 := by
  cases i using Fin.cases <;> simp [enc]

@[simp] lemma enc_succ_succ (i : Fin m) (j : Fin n) :
    enc i.succ j.succ = (finProdFinEquiv (i, j)).succ := by
  simp [enc]

/-- The decoding `(m n)₊ → m₊ × n₊`, a section of `enc`. -/
def dec (c : Fin (m * n + 1)) : Fin (m + 1) × Fin (n + 1) :=
  Fin.cases (0, 0)
    (fun c' => ((finProdFinEquiv.symm c').1.succ, (finProdFinEquiv.symm c').2.succ)) c

@[simp] lemma dec_zero : dec (m := m) (n := n) 0 = (0, 0) := by
  simp [dec]

@[simp] lemma dec_succ (c : Fin (m * n)) :
    dec c.succ = ((finProdFinEquiv.symm c).1.succ, (finProdFinEquiv.symm c).2.succ) := by
  simp [dec]

lemma enc_dec (c : Fin (m * n + 1)) : enc (dec c).1 (dec c).2 = c := by
  cases c using Fin.cases with
  | zero => simp
  | succ c =>
      rw [enc, dec]
      simp only [finProdFinEquiv_symm_apply, Fin.cases_succ, Fin.succ_inj]
      exact (Equiv.eq_symm_apply finProdFinEquiv).mp rfl

lemma enc_surj (c : Fin (m * n + 1)) : ∃ i j, enc (m := m) (n := n) i j = c :=
  ⟨_, _, enc_dec c⟩

/-- A function on `m₊ × n₊` which is constant on the wedge can be evaluated through `dec ∘ enc`. -/
lemma dec_eval {X : Sort*} (ψ : Fin (m + 1) → Fin (n + 1) → X)
    (hl : ∀ j, ψ 0 j = ψ 0 0) (hr : ∀ i, ψ i 0 = ψ 0 0) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ψ (dec (enc i j)).1 (dec (enc i j)).2 = ψ i j := by
  cases i using Fin.cases with
  | zero =>
    simp only [enc_zero_left, dec_zero]
    exact (hl j).symm
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      simp only [enc_zero_right, dec_zero]
      exact (hr _).symm
    | succ j =>
      simp only [enc_succ_succ, dec_succ, Equiv.symm_apply_apply]

end Enc

/-! ### Maps of `N` -/

@[simp] lemma comp_toFun {a b c : ℕ} (f : a₊ ⟶ b₊) (g : b₊ ⟶ c₊) (x : Fin (a + 1)) :
    Pointed.Hom.toFun (f ≫ g) x = Pointed.Hom.toFun g (Pointed.Hom.toFun f x) := rfl

@[simp] lemma id_toFun {a : ℕ} (x : Fin (a + 1)) : Pointed.Hom.toFun (𝟙 a₊) x = x := rfl

@[simp] lemma ofFun_toFun {a b : ℕ} (φ : Fin (a + 1) → Fin (b + 1)) (h : φ 0 = 0)
    (x : Fin (a + 1)) : Pointed.Hom.toFun (ofFun φ h) x = φ x := rfl

@[simp] lemma hom_zero {a b : ℕ} (f : a₊ ⟶ b₊) :
    Pointed.Hom.toFun f 0 = 0 :=
  Pointed.Hom.map_point f

lemma hom_ext_of_fun {a b : ℕ} {f g : a₊ ⟶ b₊}
    (h : ∀ c, Pointed.Hom.toFun f c = Pointed.Hom.toFun g c) : f = g :=
  N.hom_ext h

/-- Maps out of `m₊ ∧ n₊` are determined on encoded pairs. -/
lemma hom_ext_enc {m n b : ℕ} {f g : (m * n)₊ ⟶ b₊}
    (h : ∀ i j, Pointed.Hom.toFun f (enc i j) = Pointed.Hom.toFun g (enc i j)) : f = g :=
  hom_ext_of_fun fun c => by
    obtain ⟨i, j, rfl⟩ := enc_surj c
    exact h i j

/-- The universal property of `m₊ ∧ n₊`: a function on pairs killing the wedge. -/
def smashLift {m n k : ℕ} (φ : Fin (m + 1) → Fin (n + 1) → Fin (k + 1))
    (hl : ∀ j, φ 0 j = 0) : (m * n)₊ ⟶ k₊ :=
  ofFun (fun c => φ (dec c).1 (dec c).2) (by simp [hl])

@[simp] lemma smashLift_enc {m n k : ℕ} (φ : Fin (m + 1) → Fin (n + 1) → Fin (k + 1))
    (hl : ∀ j, φ 0 j = 0) (hr : ∀ i, φ i 0 = 0) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Pointed.Hom.toFun (smashLift φ hl) (enc i j) = φ i j :=
  dec_eval φ (fun j => by rw [hl, hl]) (fun i => by rw [hr, hl]) i j

/-- The smash product `f ∧ g : m₊ ∧ n₊ ⟶ m'₊ ∧ n'₊` of two maps of `N`. -/
def smashMap {m m' n n' : ℕ} (f : m₊ ⟶ m'₊) (g : n₊ ⟶ n'₊) :
    (m * n)₊ ⟶ (m' * n')₊ :=
  smashLift (fun i j => enc (Pointed.Hom.toFun f i) (Pointed.Hom.toFun g j))
    (fun j => by
      change enc (f.toFun 0) (g.toFun j) = 0
      rw [hom_zero f]
      exact enc_zero_left (g.toFun j))

@[simp] lemma smashMap_enc {m m' n n' : ℕ} (f : m₊ ⟶ m'₊) (g : n₊ ⟶ n'₊)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Pointed.Hom.toFun (smashMap f g) (enc i j) =
      enc (Pointed.Hom.toFun f i) (Pointed.Hom.toFun g j) :=
  smashLift_enc _ _ (by simp only [apply_zero, enc_zero_right, implies_true]) i j

lemma smashMap_id (m n : ℕ) : smashMap (𝟙 m₊) (𝟙 n₊) = 𝟙 (m * n)₊ :=
  hom_ext_enc fun i j => by aesop

lemma smashMap_comp {m m' m'' n n' n'' : ℕ} (f : m₊ ⟶ m'₊) (f' : m'₊ ⟶ m''₊)
    (g : n₊ ⟶ n'₊) (g' : n'₊ ⟶ n''₊) :
    smashMap (f ≫ f') (g ≫ g') = smashMap f g ≫ smashMap f' g' :=
  hom_ext_enc fun i j => by simp only [comp_toFun, smashMap_enc]

/-- The associator `(m₊ ∧ n₊) ∧ q₊ ⟶ m₊ ∧ (n₊ ∧ q₊)` of `N`. -/
def assocN (m n q : ℕ) : (m * n * q)₊ ⟶ (m * (n * q))₊ :=
  smashLift (fun c k => enc (dec c).1 (enc (dec c).2 k)) (fun k => by simp)

@[simp] lemma assocN_enc {m n q : ℕ} (i : Fin (m + 1)) (j : Fin (n + 1)) (k : Fin (q + 1)) :
    Pointed.Hom.toFun (assocN m n q) (enc (enc i j) k) = enc i (enc j k) := by
  rw [assocN, smashLift_enc]
  · exact dec_eval (fun i j => enc i (enc j k)) (fun j => by simp) (fun i => by simp) i j
  · simp only [enc_zero_right, implies_true]

/-- The inverse associator `m₊ ∧ (n₊ ∧ q₊) ⟶ (m₊ ∧ n₊) ∧ q₊` of `N`. -/
def assocInvN (m n q : ℕ) : (m * (n * q))₊ ⟶ (m * n * q)₊ :=
  smashLift (fun i c => enc (enc i (dec c).1) (dec c).2) (fun c => by simp)

@[simp] lemma assocInvN_enc {m n q : ℕ} (i : Fin (m + 1)) (j : Fin (n + 1)) (k : Fin (q + 1)) :
    Pointed.Hom.toFun (assocInvN m n q) (enc i (enc j k)) = enc (enc i j) k := by
  rw [assocInvN, smashLift_enc]
  · exact dec_eval (fun j k => enc (enc i j) k) (fun k => by simp) (fun j => by simp) j k
  · simp only [dec_zero, enc_zero_right, implies_true]

/-- The left unitor `1₊ ∧ n₊ ⟶ n₊` of `N`. -/
def lamN (n : ℕ) : (1 * n)₊ ⟶ n₊ :=
  smashLift (fun i j => if i = 0 then 0 else j) (fun j => by simp)

@[simp] lemma lamN_enc {n : ℕ} (i : Fin 2) (j : Fin (n + 1)) :
    Pointed.Hom.toFun (lamN n) (enc i j) = if i = 0 then 0 else j :=
  smashLift_enc _ _ (by simp) i j

/-- The right unitor `n₊ ∧ 1₊ ⟶ n₊` of `N`. -/
def rhoN (n : ℕ) : (n * 1)₊ ⟶ n₊ :=
  smashLift (fun i j => if j = 0 then 0 else i) (fun j => by simp)

@[simp] lemma rhoN_enc {n : ℕ} (i : Fin (n + 1)) (j : Fin 2) :
    Pointed.Hom.toFun (rhoN n) (enc i j) = if j = 0 then 0 else i :=
  smashLift_enc _ _ (by simp) i j

/-- The symmetry `m₊ ∧ n₊ ⟶ n₊ ∧ m₊` of `N`. -/
def swapN (m n : ℕ) : (m * n)₊ ⟶ (n * m)₊ :=
  smashLift (fun i j => enc j i) (fun j => by simp)

@[simp] lemma swapN_enc {m n : ℕ} (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Pointed.Hom.toFun (swapN m n) (enc i j) = enc j i :=
  smashLift_enc _ _ (by simp) i j

/-- `j ↦ (i, j)`, i.e. `pt i ∧ n₊` composed with the unitor. -/
def incL {m n : ℕ} (i : Fin (m + 1)) : n₊ ⟶ (m * n)₊ := ofFun (fun j => enc i j) (by simp)

/-- `i ↦ (i, j)`. -/
def incR {m n : ℕ} (j : Fin (n + 1)) : m₊ ⟶ (m * n)₊ := ofFun (fun i => enc i j) (by simp)

@[simp] lemma incL_toFun {m n : ℕ} (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Pointed.Hom.toFun (incL (n := n) i) j = enc i j := rfl

@[simp] lemma incR_toFun {m n : ℕ} (j : Fin (n + 1)) (i : Fin (m + 1)) :
    Pointed.Hom.toFun (incR (m := m) j) i = enc i j := rfl

@[simp] lemma pt_toFun {n : ℕ} (i : Fin (n + 1)) (c : Fin 2) :
    Pointed.Hom.toFun (pt i) c = if c = 0 then 0 else i := rfl

@[simp] lemma toZero_toFun (n : ℕ) (c : Fin (n + 1)) :
    Pointed.Hom.toFun (toZero n) c = 0 := rfl

@[simp] lemma fromZero_toFun (n : ℕ) (c : Fin 1) :
    Pointed.Hom.toFun (fromZero n) c = 0 := rfl

/-- A map of `N` all of whose values are `0` factors through `0₊`. -/
lemma eq_of_zero {a b : ℕ} (f : a₊ ⟶ b₊) (hf : ∀ c, Pointed.Hom.toFun f c = 0) :
    f = toZero a ≫ fromZero b :=
  hom_ext_of_fun hf

end N

/-- Tactic proving equalities of maps of `N` out of (iterated) smash products:
test on encoded elements, decode nested encodings, then compute. -/
macro "enc_ext" : tactic => `(tactic| (
  apply N.hom_ext_enc
  intro i j
  try (obtain ⟨i, i', rfl⟩ := N.enc_surj i)
  try (obtain ⟨i, i'', rfl⟩ := N.enc_surj i)
  try (obtain ⟨j, j', rfl⟩ := N.enc_surj j)
  try (obtain ⟨j', j'', rfl⟩ := N.enc_surj j')
  try (obtain ⟨j, j''', rfl⟩ := N.enc_surj j)
  simp only [N.comp_toFun, N.id_toFun, N.smashMap_enc, N.assocN_enc, N.assocInvN_enc,
    N.lamN_enc, N.rhoN_enc, N.swapN_enc, N.incL_toFun, N.incR_toFun, N.pt_toFun,
    N.ofFun_toFun, N.hom_zero, N.enc_zero_left, N.enc_zero_right]
  try (split_ifs <;> simp_all)))
