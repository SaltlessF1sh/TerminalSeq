import TerminalSeq.FinalSequence

/-!
# Accessibility and Tail Injectivity for `G_{κ,θ}`

Proves from scratch in Lean 4 that `GFunctor κ θ` is `κ`-accessible (`G_isAccessible`)
whenever `θ ≤ κ`, and derives tail monicity (`f_kappa_succ_injective`, `tail_monic`)
directly from the general theorem `TerminalSeq.Abstract.tail_monic_of_accessible`.
-/

noncomputable section

open Classical Ordinal Cardinal

namespace TerminalSeq

/-! ### 1. Preservation of Injections -/

theorem G.map_injective {κ θ : Cardinal.{0}} {X Y : Type 1} {g : X → Y}
    (hg : Function.Injective g) : Function.Injective (G.map (κ := κ) (θ := θ) g) := by
  intro x y hxy
  cases x with
  | inl S₁ =>
      cases y with
      | inl S₂ =>
          rcases S₁ with ⟨S₁, h₁⟩
          rcases S₂ with ⟨S₂, h₂⟩
          have him : g '' S₁ = g '' S₂ := congrArg Subtype.val (Sum.inl.inj hxy)
          have hS : S₁ = S₂ := (Set.image_injective.mpr hg) him
          congr 1
          exact Subtype.ext hS
      | inr _ => cases hxy
  | inr p₁ =>
      cases y with
      | inl _ => cases hxy
      | inr p₂ =>
          rcases p₁ with ⟨μ₁, q₁⟩
          rcases p₂ with ⟨μ₂, q₂⟩
          induction q₁, q₂ using Quotient.inductionOn₂ with
          | h a b =>
              have hsig := Sum.inr.inj hxy
              have hμ : μ₁ = μ₂ := congrArg Sigma.fst hsig
              subst hμ
              have hq : Quotient.mk (ltDiffSetoid Y μ₁) (g ∘ a) =
                  Quotient.mk (ltDiffSetoid Y μ₁) (g ∘ b) := by
                have hsnd := (Sigma.mk.inj_iff.1 hsig).2
                rwa [heq_eq_eq] at hsnd
              have hdiff : ltDiff μ₁.1 (g ∘ a) (g ∘ b) := Quotient.exact hq
              have hcard_eq : Cardinal.mk { i : μ₁.1.ord.ToType // a i ≠ b i } =
                  Cardinal.mk { i : μ₁.1.ord.ToType // g (a i) ≠ g (b i) } :=
                Cardinal.mk_congr
                  { toFun := fun i => ⟨i.1, fun h => i.2 (hg h)⟩
                    invFun := fun i => ⟨i.1, fun h => i.2 (congrArg g h)⟩
                    left_inv := fun _ => rfl
                    right_inv := fun _ => rfl }
              have hdiff' : ltDiff μ₁.1 a b := by
                unfold ltDiff at hdiff ⊢
                rwa [hcard_eq]
              exact congrArg (fun q => (Sum.inr ⟨μ₁, q⟩ : G κ θ X)) (Quotient.sound hdiff')

/-! ### 2. `κ`-Accessibility of `G_{κ,θ}` -/

theorem G_isAccessible {κ θ : Cardinal.{0}} (hθ : θ ≤ κ) :
    (GFunctor κ θ).IsAccessible κ := by
  intro X u
  cases u with
  | inl S =>
      rcases S with ⟨S, hS⟩
      have hcard : Cardinal.mk (Set.univ : Set ↥S) < Cardinal.lift.{1, 0} κ := by
        simpa using hS
      refine ⟨S, hS, .inl ⟨Set.univ, hcard⟩, ?_⟩
      change (Sum.inl ⟨Subtype.val '' (Set.univ : Set ↥S), _⟩ : G κ θ X) = Sum.inl ⟨S, hS⟩
      congr 1
      apply Subtype.ext
      ext x
      simp
  | inr p =>
      rcases p with ⟨μ, q⟩
      induction q using Quotient.ind with
      | _ a =>
          let S : Set X := Set.range a
          have hμ_card : Cardinal.mk μ.1.ord.ToType = μ.1 := by simp
          have hrange : Cardinal.mk S ≤ Cardinal.lift.{1, 0} μ.1 := by
            simpa [S, hμ_card] using Cardinal.mk_range_le_lift (f := a)
          have hμκ : μ.1 < κ := lt_of_lt_of_le μ.2.2 hθ
          have hS : Cardinal.mk S < Cardinal.lift.{1, 0} κ :=
            lt_of_le_of_lt hrange (Cardinal.lift_lt.2 hμκ)
          let a' : μ.1.ord.ToType → ↥S := fun i => ⟨a i, Set.mem_range_self i⟩
          refine ⟨S, hS, .inr ⟨μ, Quotient.mk (ltDiffSetoid (↥S) μ) a'⟩, ?_⟩
          rfl

/-! ### 3. Tail Injectivity via `Abstract.tail_monic_of_accessible` -/

theorem tail_monic {κ θ : Cardinal.{0}} (hκ : κ.IsRegular) (hθ : θ ≤ κ)
    {α β : Ordinal.{0}} (hκα : κ.ord ≤ α) (hαβ : α ≤ β) :
    Function.Injective (f (κ := κ) (θ := θ) hαβ) := by
  have : Nonempty (A κ θ 1) := nonempty_A hκ.pos 1
  exact Abstract.tail_monic_of_accessible hκ (G_isAccessible hθ) hκα hαβ

theorem f_kappa_succ_injective {κ θ : Cardinal.{0}} (hκ : κ.IsRegular) (hθ : θ ≤ κ) :
    Function.Injective (f (κ := κ) (θ := θ) (Order.le_succ κ.ord)) :=
  tail_monic hκ hθ le_rfl (Order.le_succ κ.ord)

end TerminalSeq
