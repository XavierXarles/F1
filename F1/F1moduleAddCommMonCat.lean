import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.Data.Multiset.Basic
import F1.F1moduleCat

/-! The functor to F1Module to AddCommMonCat. -/

universe u

open CategoryTheory

namespace F1module

variable (M : Type u) [F1module M]

/-- `{c} ~ {x 0} + ⋯ + {x (n-1)}` whenever `c ∈ hadd n x`, for every `n`. -/
inductive envRel : Multiset M → Multiset M → Prop
  | of_mem {n : ℕ} (x : Fin n → M) {c : M} (h : c ∈ hadd n x) :
      envRel {c} (∑ i, ({x i} : Multiset M))

def envCon : AddCon (Multiset M) := addConGen (envRel M)

/-- The enveloping commutative monoid of an `F1module`. -/
abbrev Env : Type u := (envCon M).Quotient

def ι (m : M) : Env M := (envCon M).mk' {m}

theorem ι_of_mem {n : ℕ} (x : Fin n → M) {c : M} (h : c ∈ hadd n x) :
    ι M c = ∑ i, ι M (x i) := by
  simp only [ι, ← map_sum]
  refine (AddCon.eq _).2 ?_
  tauto

/-- The unit `M → F (Env M)`. -/
def unit : F1module.Hom M (Env M) where
  toFun := ι M
  map_hadd n x := by
    rintro _ ⟨c, hc, rfl⟩
    rw [AddMonoid.hadd_eq_sum]; exact ι_of_mem M x hc
  map_zero' := by
    have := ι_of_mem (M:=M) (fun x ↦ zero) (F1module.zero_mem 0)
    exact ((fun a ↦ this) ∘ fun a ↦ M) M

@[simp]
theorem unit_apply (m : M) : unit M m = ι M m := rfl



variable {M} {A : Type u} [AddCommMonoid A]

/-- Universal property: a morphism `M → F A` factors uniquely through `Env M`. -/
def lift (φ : F1module.Hom M A) : Env M →+ A :=
  (envCon M).lift (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom φ)) <|
    by
      rw [envCon,AddCon.addConGen_le]
      intro A B h
      obtain ⟨x, hc⟩ := h
      have := φ.mem_hadd_of_mem_hadd _ x hc
      rw [AddMonoid.hadd_eq_sum] at this
      simpa [map_sum] using this

@[simp] theorem lift_ι (φ : F1module.Hom M A) (m : M) : lift φ (ι M m) = φ m := by
  simp [lift, ι]

theorem hom_ext {f g : Env M →+ A} (h : ∀ m, f (ι M m) = g (ι M m)) : f = g :=
  AddCon.hom_ext <| Multiset.addHom_ext h   -- singletons generate `Multiset M`

end F1module

namespace F1moduleCat

/-- **The enveloping monoid functor**, defined by hand: `M ↦ Env M`, and a morphism
`g : M ⟶ N` goes to the unique additive map `Env M → Env N` with `ι m ↦ ι (g m)`. -/
def env : F1moduleCat.{u} ⥤ AddCommMonCat.{u} where
  obj M := AddCommMonCat.of (F1module.Env M)
  map {_ N} g := AddCommMonCat.ofHom (F1module.lift ((F1module.unit N).comp g.hom))
  map_id M := by
    apply AddCommMonCat.hom_ext
    apply F1module.hom_ext
    intro m
    trivial
  map_comp {M N P} f g := by
    apply AddCommMonCat.hom_ext
    apply F1module.hom_ext
    intro m
    trivial

@[simp] theorem env_obj (M : F1moduleCat.{u}) :
    env.obj M = AddCommMonCat.of (F1module.Env M) := rfl

@[simp] theorem env_map_ι {M N : F1moduleCat.{u}} (g : M ⟶ N) (m : M) :
    (env.map g).hom (F1module.ι M m) = F1module.ι N (g.hom m) := by
  trivial

/-- `env ⊣ AddCommMonCat.toF1moduleCat`: maps `Env M → A` of monoids are the same as
morphisms `M → A` of `F1module`s. -/
def envAdj : env.{u} ⊣ AddCommMonCat.toF1moduleCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M A =>
        { toFun := fun f => F1moduleCat.ofHom (f.hom.toF1moduleHom.comp (F1module.unit M))
          invFun := fun φ => AddCommMonCat.ofHom (F1module.lift φ.hom)
          left_inv := fun f => by
            apply AddCommMonCat.hom_ext
            apply F1module.hom_ext
            intro m
            -- goal: lift (f ∘ ι) (ι m) = f (ι m)
            exact F1module.lift_ι _ m
          right_inv := fun φ => by
            ext m
            -- goal: (lift φ) (ι m) = φ m
            exact F1module.lift_ι φ.hom m (A:=A)}
      homEquiv_naturality_left_symm := fun f g => by
        apply AddCommMonCat.hom_ext
        apply F1module.hom_ext
        intro m
        trivial
      homEquiv_naturality_right := fun f g => by
        ext m
        rfl }

end F1moduleCat
