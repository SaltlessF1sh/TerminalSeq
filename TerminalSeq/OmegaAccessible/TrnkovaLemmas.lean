import TerminalSeq.Abstract.Stabilization

/-!
# Trnková's Pullback Lemmas and Constant-Retract Criterion

Formalizes Lemmas 1.1, 1.2, and 1.3 from the manuscript for arbitrary endofunctors
`F : SetFunctor` (`Set → Set`):

1. `trnkova_inter` (Lemma 1.1): For nonempty intersection `A ∩ B`,
   `range (F.map (inc A)) ∩ range (F.map (inc B)) = range (F.map (inc (A ∩ B)))`.
2. `singleton_of_disjoint_range` (Lemma 1.2): Any element of `F.obj X` supported on
   two disjoint subsets `A, B ⊆ X` factors through every singleton `{z₀} ⊆ X`.
3. `stabilizesAt_one_of_section_and_terminal` (Lemma 1.3): If `A F 1` is a retract of `X`
   and `F` preserves the terminal map `X → 1`, then `F` stabilizes at `1`.
-/

namespace TerminalSeq.OmegaAccessible

open TerminalSeq.Abstract

section TrnkovaLemmas

/-- **Lemma 1.1 (Trnková)**: If `A ∩ B` is nonempty in `X`, then the intersection of the
images of `F(i_A)` and `F(i_B)` inside `F(X)` equals the image of `F(i_{A ∩ B})`. -/
theorem trnkova_inter {F : SetFunctor} {X : Type 1} {A B : Set X}
    (hne : (A ∩ B).Nonempty) :
    Set.range (F.map (SetFunctor.inc A)) ∩ Set.range (F.map (SetFunctor.inc B)) =
      Set.range (F.map (SetFunctor.inc (A ∩ B))) := by
  classical
  ext t
  constructor
  · rintro ⟨⟨uA, rfl⟩, ⟨uB, huB⟩⟩
    obtain ⟨c, hcA, hcB⟩ := hne
    let eA : X → X := fun x => if x ∈ A then x else c
    let eB : X → X := fun x => if x ∈ B then x else c
    let q : X → ↥(A ∩ B) := fun x =>
      if h : x ∈ A ∩ B then ⟨x, h⟩ else ⟨c, hcA, hcB⟩
    have heA_inc : eA ∘ SetFunctor.inc A = SetFunctor.inc A := by
      funext a
      simp [eA, SetFunctor.inc, a.2]
    have heB_inc : eB ∘ SetFunctor.inc B = SetFunctor.inc B := by
      funext b
      simp [eB, SetFunctor.inc, b.2]
    have heAB : eA ∘ eB = SetFunctor.inc (A ∩ B) ∘ q := by
      funext x
      by_cases hxB : x ∈ B
      · by_cases hxA : x ∈ A
        · simp [eA, eB, q, SetFunctor.inc, hxA, hxB]
        · simp [eA, eB, q, SetFunctor.inc, hxA, hxB]
      · simp [eA, eB, q, SetFunctor.inc, hcA, hxB]
    have hFA : F.map eA (F.map (SetFunctor.inc A) uA) = F.map (SetFunctor.inc A) uA := by
      rw [← F.map_comp_apply, heA_inc]
    have hFB : F.map eB (F.map (SetFunctor.inc A) uA) = F.map (SetFunctor.inc A) uA := by
      rw [← huB, ← F.map_comp_apply, heB_inc]
    refine ⟨F.map q (F.map (SetFunctor.inc A) uA), ?_⟩
    calc
      F.map (SetFunctor.inc (A ∩ B)) (F.map q (F.map (SetFunctor.inc A) uA))
          = F.map (SetFunctor.inc (A ∩ B) ∘ q) (F.map (SetFunctor.inc A) uA) := by
            rw [← F.map_comp_apply]
      _ = F.map (eA ∘ eB) (F.map (SetFunctor.inc A) uA) := by rw [heAB]
      _ = F.map eA (F.map eB (F.map (SetFunctor.inc A) uA)) := by rw [F.map_comp_apply]
      _ = F.map (SetFunctor.inc A) uA := by rw [hFB, hFA]
  · rintro ⟨u, rfl⟩
    constructor
    · refine ⟨F.map (Set.inclusion Set.inter_subset_left) u, ?_⟩
      rw [← F.map_comp_apply]
      rfl
    · refine ⟨F.map (Set.inclusion Set.inter_subset_right) u, ?_⟩
      rw [← F.map_comp_apply]
      rfl

/-- Finite iterated version of Lemma 1.1: if `E : Finset X` has nonempty complement `(E : Set X)ᶜ`
and `F.map (inc {b}ᶜ)` is surjective for every `b ∈ E`, then `F.map (inc (E : Set X)ᶜ)` is surjective. -/
theorem surjective_compl_finset_of_compl_singleton {F : SetFunctor} {X : Type 1}
    (hsingle : ∀ b : X, Function.Surjective (F.map (SetFunctor.inc ({b}ᶜ : Set X)))) :
    ∀ (E : Finset X), ((E : Set X)ᶜ).Nonempty →
      Function.Surjective (F.map (SetFunctor.inc ((E : Set X)ᶜ))) := by
  classical
  intro E
  induction E using Finset.induction with
  | empty =>
    intro _ x
    let e : X → ↥(((∅ : Finset X) : Set X)ᶜ) := fun y => ⟨y, by simp⟩
    have he : SetFunctor.inc (((∅ : Finset X) : Set X)ᶜ) ∘ e = id := by
      funext y; rfl
    refine ⟨F.map e x, ?_⟩
    rw [← F.map_comp_apply, he, F.map_id_apply]
  | @insert a E ha IH =>
    intro hne x
    have hE_ne : ((E : Set X)ᶜ).Nonempty :=
      hne.mono (by simp)
    have hinter_eq : ({a}ᶜ : Set X) ∩ (E : Set X)ᶜ = ((insert a E : Finset X) : Set X)ᶜ := by
      ext y
      simp [not_or]
    have hinter_ne : (({a}ᶜ : Set X) ∩ (E : Set X)ᶜ).Nonempty := by
      simpa [hinter_eq] using hne
    have hmem : x ∈ Set.range (F.map (SetFunctor.inc ({a}ᶜ : Set X))) ∩
        Set.range (F.map (SetFunctor.inc (E : Set X)ᶜ)) := by
      exact ⟨hsingle a x, IH hE_ne x⟩
    rw [trnkova_inter hinter_ne] at hmem
    obtain ⟨u, rfl⟩ := hmem
    let castSub : ↥(({a}ᶜ : Set X) ∩ (E : Set X)ᶜ) → ↥(((insert a E : Finset X) : Set X)ᶜ) :=
      Set.inclusion (le_of_eq hinter_eq)
    refine ⟨F.map castSub u, ?_⟩
    rw [← F.map_comp_apply]
    rfl

/-- **Lemma 1.2**: If `A` and `B` are disjoint subsets of `X` and `x : F.obj X` lies in both
`range (F.map (inc A))` and `range (F.map (inc B))`, then for every `z₀ : X`, `x` lies in
`range (F.map (fun _ : PUnit.{2} => z₀))`. -/
theorem singleton_of_disjoint_range {F : SetFunctor} {X : Type 1} {A B : Set X}
    (hdisj : Disjoint A B) {x : F.obj X}
    (hxA : x ∈ Set.range (F.map (SetFunctor.inc A)))
    (hxB : x ∈ Set.range (F.map (SetFunctor.inc B))) (z₀ : X) :
    x ∈ Set.range (F.map (fun _ : PUnit.{2} => z₀)) := by
  classical
  obtain ⟨uA, huA⟩ := hxA
  obtain ⟨uB, huB⟩ := hxB
  let f : X → X := fun y => if y ∈ A then z₀ else y
  have hfA : f ∘ SetFunctor.inc A = (fun _ : PUnit.{2} => z₀) ∘ (fun _ : ↥A => PUnit.unit) := by
    funext a
    simp [f, SetFunctor.inc, a.2]
  have hfB : f ∘ SetFunctor.inc B = SetFunctor.inc B := by
    funext b
    simp [f, SetFunctor.inc, Set.disjoint_right.1 hdisj b.2]
  have hFx : F.map f x = x := by
    calc
      F.map f x = F.map f (F.map (SetFunctor.inc B) uB) := by rw [huB]
      _ = F.map (f ∘ SetFunctor.inc B) uB := by rw [← F.map_comp_apply]
      _ = F.map (SetFunctor.inc B) uB := by rw [hfB]
      _ = x := huB
  refine ⟨F.map (fun _ : ↥A => PUnit.unit) uA, ?_⟩
  calc
    F.map (fun _ : PUnit.{2} => z₀) (F.map (fun _ : ↥A => PUnit.unit) uA)
        = F.map ((fun _ : PUnit.{2} => z₀) ∘ (fun _ : ↥A => PUnit.unit)) uA := by
          rw [← F.map_comp_apply]
    _ = F.map (f ∘ SetFunctor.inc A) uA := by rw [hfA]
    _ = F.map f (F.map (SetFunctor.inc A) uA) := by rw [F.map_comp_apply]
    _ = F.map f x := by rw [huA]
    _ = x := hFx

private theorem bijective_of_terminal_one {F : SetFunctor}
    (hbij : Function.Bijective (F.map (fun _ : A F 1 => PUnit.unit))) :
    StabilizesAt F 1 := by
  have h01 : (0 : Ordinal.{0}) ≤ 1 := bot_le
  have hfact : (fun _ : A F 1 => PUnit.unit) = zeroEquiv F ∘ f (F := F) h01 := by
    funext _
    simp
  have hF01 : Function.Bijective (F.map (f (F := F) h01)) := by
    have hcomp_fun : F.map (fun _ : A F 1 => PUnit.unit) =
        F.map (zeroEquiv F : A F 0 → PUnit.{2}) ∘ F.map (f (F := F) h01) := by
      funext x
      rw [hfact]
      exact F.map_comp_apply _ _ x
    rw [hcomp_fun] at hbij
    have hzero : Function.Bijective (F.map (zeroEquiv F : A F 0 → PUnit.{2})) :=
      F.map_bijective (zeroEquiv F).bijective
    exact ⟨fun a b hab => hbij.1 (by simp [Function.comp, hab]),
      fun y => by
        obtain ⟨x, hx⟩ := hbij.2 (F.map (zeroEquiv F) y)
        exact ⟨x, hzero.1 hx⟩⟩
  have hsucc0 : Order.succ (0 : Ordinal.{0}) = 1 := by simp
  let e0 : A F (Order.succ 0) ≃ A F 1 := Equiv.cast (congrArg (A F) hsucc0)
  have hcast : ∀ {α β : Ordinal.{0}} (hab : α = β) (h1 : α ≤ Order.succ 1)
      (h2 : β ≤ Order.succ 1) (x : A F (Order.succ 1)),
      Equiv.cast (congrArg (A F) hab) (f (F := F) h1 x) = f (F := F) h2 x := by
    rintro α β rfl h1 h2 x
    rfl
  have hcomm : (succEquiv F 0 ∘ e0.symm) ∘ f (F := F) (Order.le_succ 1) =
      F.map (f (F := F) h01) ∘ succEquiv F 1 := by
    funext x
    dsimp [Function.comp]
    have hsymm : e0.symm (f (F := F) (Order.le_succ 1) x) =
        f (F := F) (Order.succ_le_succ h01) x :=
      hcast hsucc0.symm (Order.le_succ 1) (Order.succ_le_succ h01) x
    rw [hsymm, succEquiv_f_succ h01 x]
  have hcomp_bij : Function.Bijective
      ((succEquiv F 0 ∘ e0.symm) ∘ f (F := F) (Order.le_succ 1)) := by
    rw [hcomm]
    exact hF01.comp (succEquiv F 1).bijective
  have hleft_bij : Function.Bijective (succEquiv F 0 ∘ e0.symm) :=
    (succEquiv F 0).bijective.comp e0.symm.bijective
  unfold StabilizesAt
  constructor
  · intro a b hab
    exact hcomp_bij.1 (by simp [Function.comp, hab])
  · intro y
    obtain ⟨x, hx⟩ := hcomp_bij.2 ((succEquiv F 0 ∘ e0.symm) y)
    exact ⟨x, hleft_bij.1 hx⟩

/-- **Lemma 1.3**: Suppose `A F 1` is a retract of `X` (`q ∘ s = id`) and `F` maps the
terminal projection `X → PUnit` to a bijection `F(X) → F(PUnit)`. Then `F` stabilizes at `1`. -/
theorem stabilizesAt_one_of_section_and_terminal {F : SetFunctor} {X : Type 1}
    (q : X → A F 1) (s : A F 1 → X) (hqs : q ∘ s = id)
    (hbij : Function.Bijective (F.map (fun _ : X => PUnit.unit))) :
    StabilizesAt F 1 := by
  let tX : X → PUnit.{2} := fun _ => PUnit.unit
  let t1 : A F 1 → PUnit.{2} := fun _ => PUnit.unit
  have htq : t1 ∘ q = tX := rfl
  have hts : tX ∘ s = t1 := rfl
  have hFs_inj : Function.Injective (F.map s) :=
    F.map_injective_of_leftInverse hqs
  have hFt1_inj : Function.Injective (F.map t1) := by
    have hcomp : F.map t1 = F.map tX ∘ F.map s := by
      funext x
      rw [← hts]
      exact F.map_comp_apply tX s x
    rw [hcomp]
    exact hbij.1.comp hFs_inj
  have hFt1_surj : Function.Surjective (F.map t1) := by
    intro y
    obtain ⟨x, hx⟩ := hbij.2 y
    refine ⟨F.map q x, ?_⟩
    rw [← F.map_comp_apply, htq]
    exact hx
  exact bijective_of_terminal_one ⟨hFt1_inj, hFt1_surj⟩

end TrnkovaLemmas

end TerminalSeq.OmegaAccessible
