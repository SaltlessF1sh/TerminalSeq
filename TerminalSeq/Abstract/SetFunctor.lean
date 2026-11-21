import Mathlib.SetTheory.Cardinal.Regular

/-!
# Set Endofunctors and Accessibility

Defines endofunctors `SetFunctor` on `Type 1`, basic categorical facts (preservation of
bijections and split monomorphisms/epimorphisms), and `κ`- / `ω`-accessibility.
-/

noncomputable section

open Classical Cardinal

namespace TerminalSeq.Abstract

/-- An endofunctor on `Type 1` (sets in a fixed universe). -/
structure SetFunctor : Type 2 where
  obj : Type 1 → Type 1
  map : {X Y : Type 1} → (X → Y) → obj X → obj Y
  map_id : ∀ {X : Type 1} (x : obj X), map id x = x
  map_comp : ∀ {X Y Z : Type 1} (g : Y → Z) (h : X → Y) (x : obj X),
    map (g ∘ h) x = map g (map h x)

namespace SetFunctor

variable (F : SetFunctor)

@[simp]
theorem map_id_apply {X : Type 1} (x : F.obj X) : F.map id x = x :=
  F.map_id x

theorem map_id_eq {X : Type 1} : F.map (id : X → X) = id :=
  funext F.map_id

theorem map_comp_apply {X Y Z : Type 1} (g : Y → Z) (h : X → Y) (x : F.obj X) :
    F.map (g ∘ h) x = F.map g (F.map h x) :=
  F.map_comp g h x

theorem map_comp_eq {X Y Z : Type 1} (g : Y → Z) (h : X → Y) :
    F.map (g ∘ h) = F.map g ∘ F.map h :=
  funext (F.map_comp g h)

/-- An equivalence `X ≃ Y` lifts to `F.obj X ≃ F.obj Y`. -/
def mapEquiv {X Y : Type 1} (e : X ≃ Y) : F.obj X ≃ F.obj Y where
  toFun := F.map e
  invFun := F.map e.symm
  left_inv x := by
    rw [← F.map_comp_apply e.symm e x]
    simp
  right_inv y := by
    rw [← F.map_comp_apply e e.symm y]
    simp

theorem map_bijective {X Y : Type 1} {g : X → Y} (hg : Function.Bijective g) :
    Function.Bijective (F.map g) :=
  (F.mapEquiv (Equiv.ofBijective g hg)).bijective

theorem map_injective_of_leftInverse {X Y : Type 1} {g : X → Y} {r : Y → X}
    (hr : r ∘ g = id) : Function.Injective (F.map g) := by
  intro x₁ x₂ hx
  have h1 := congrArg (F.map r) hx
  rw [← F.map_comp_apply, ← F.map_comp_apply, hr, F.map_id, F.map_id] at h1
  exact h1

theorem map_surjective_of_rightInverse {X Y : Type 1} {g : X → Y} {s : Y → X}
    (hs : g ∘ s = id) : Function.Surjective (F.map g) := by
  intro y
  refine ⟨F.map s y, ?_⟩
  rw [← F.map_comp_apply, hs, F.map_id]

/-- Any injective map out of a nonempty set splits, hence `F.map` preserves it. -/
theorem map_injective_of_nonempty {X Y : Type 1} [Nonempty X] {g : X → Y}
    (hg : Function.Injective g) : Function.Injective (F.map g) := by
  let r : Y → X := Function.invFun g
  have hr : r ∘ g = id := funext (Function.leftInverse_invFun hg)
  exact F.map_injective_of_leftInverse hr

/-- Inclusion map `S ↪ X` for a subset `S : Set X`. -/
abbrev inc {X : Type 1} (S : Set X) : S → X := Subtype.val

/-- `κ`-accessibility of a set functor `F`. -/
def IsAccessible (κ : Cardinal.{0}) (F : SetFunctor) : Prop :=
  ∀ {X : Type 1} (u : F.obj X),
    ∃ S : Set X, Cardinal.mk S < Cardinal.lift.{1, 0} κ ∧
      u ∈ Set.range (F.map (inc S))

/-- `ω`-accessibility (finitarity) of a set functor `F`. -/
def IsOmegaAccessible (F : SetFunctor) : Prop :=
  ∀ {X : Type 1} (u : F.obj X),
    ∃ S : Set X, S.Finite ∧ u ∈ Set.range (F.map (inc S))

theorem isAccessible_aleph0_iff :
    IsAccessible Cardinal.aleph0 F ↔ IsOmegaAccessible F := by
  constructor
  · intro h X u
    rcases h u with ⟨S, hS, v, hv⟩
    have hfin : S.Finite := by
      rw [← Cardinal.lt_aleph0_iff_set_finite]
      simpa using hS
    exact ⟨S, hfin, v, hv⟩
  · intro h X u
    rcases h u with ⟨S, hfin, v, hv⟩
    have hS : Cardinal.mk S < Cardinal.lift.{1, 0} Cardinal.aleph0 := by
      simpa using (Cardinal.lt_aleph0_iff_set_finite.2 hfin)
    exact ⟨S, hS, v, hv⟩

end SetFunctor

end TerminalSeq.Abstract
