import TerminalSeq.Step2_GeneralStab

/-!
# Specialization to `κ = θ = ℵ₁`

Specializing `stab_general_kappa_theta` to `κ = θ = ℵ₁`:
1. The only infinite regular cardinal strictly below `ℵ₁` is `ℵ₀`, so the second summand
   of `G (ℵ₁) (ℵ₁) X` collapses to `X^ω / ≡_{<ω}`, i.e. countable sequences modulo finite
   differences (`=_{fin}`), recovering `G(X) = P_{<ω₁}(X) ⊔ (X^ω / =_{fin})`.
2. Step 1 yields non-surjectivity of `f_{ω₁}^{ω₁+1}`, proving `Stab(G) ≥ ω₁`.
3. `G` is `ℵ₁`-accessible and `f_{ω₁}^{ω₁+1}` (and hence every tail projection) is injective.
4. Step 2 proves exact stabilization `Stab(G) = ω₁ + ω₁ = ω₁ * 2`.
-/

namespace TerminalSeq

open Cardinal Ordinal

/-- `ord (ℵ₁) = ω₁` in `Ordinal.{0}` and `Cardinal.{0}`. -/
theorem ord_aleph_one : (ℵ₁ : Cardinal.{0}).ord = ω₁ := by
  simp

/-- Every infinite regular cardinal strictly below `ℵ₁` equals `ℵ₀`. -/
theorem regBelow_aleph_one_eq_aleph0 (μ : RegBelow (ℵ₁ : Cardinal.{0})) : μ.1 = ℵ₀ :=
  le_antisymm (Cardinal.lt_aleph_one_iff.1 μ.2.2) μ.2.1.aleph0_le

/-- `ℵ₁`-accessibility of the set functor `GFunctor ℵ₁ ℵ₁`. -/
theorem omega1_accessible :
    (GFunctor (ℵ₁ : Cardinal.{0}) (ℵ₁ : Cardinal.{0})).IsAccessible (ℵ₁ : Cardinal.{0}) :=
  G_isAccessible (κ := (ℵ₁ : Cardinal.{0})) (θ := (ℵ₁ : Cardinal.{0})) le_rfl

/-- Step 1 at `ω₁`: `f_{ω₁}^{ω₁+1}` is not surjective. -/
theorem omega1_step1 :
    ∃ b : A (ℵ₁ : Cardinal.{0}) (ℵ₁ : Cardinal.{0}) ω₁,
      ∀ x : A (ℵ₁ : Cardinal.{0}) (ℵ₁ : Cardinal.{0}) (Order.succ ω₁),
        f (κ := (ℵ₁ : Cardinal.{0})) (θ := (ℵ₁ : Cardinal.{0})) (Order.le_succ ω₁) x ≠ b := by
  have h := step1_not_surjective_kappa (ℵ₁ : Cardinal.{0}) (ℵ₁ : Cardinal.{0})
    Cardinal.isRegular_aleph_one
  rwa [ord_aleph_one] at h

/-- Tail monicity at `ω₁`: `f_{ω₁}^{ω₁+1}` is injective. -/
theorem omega1_monic :
    Function.Injective
      (f (κ := (ℵ₁ : Cardinal.{0})) (θ := (ℵ₁ : Cardinal.{0})) (Order.le_succ ω₁)) := by
  have h := f_kappa_succ_injective (κ := (ℵ₁ : Cardinal.{0})) (θ := (ℵ₁ : Cardinal.{0}))
    Cardinal.isRegular_aleph_one le_rfl
  rwa [ord_aleph_one] at h

/-- Exact stabilization of `G (ℵ₁) (ℵ₁)` at `ω₁ + ω₁`. -/
theorem omega1_stab :
    Stabilizes (ℵ₁ : Cardinal.{0}) (ℵ₁ : Cardinal.{0}) (ω₁ + ω₁) := by
  have h := stab_general_kappa_theta (κ := (ℵ₁ : Cardinal.{0})) (θ := (ℵ₁ : Cardinal.{0}))
    Cardinal.isRegular_aleph_one Cardinal.isRegular_aleph_one le_rfl
  rwa [ord_aleph_one] at h

/-- Exact stabilization stated with right multiplication `ω₁ * 2 = ω₁ + ω₁`. -/
theorem omega1_stab_mul_two :
    Stabilizes (ℵ₁ : Cardinal.{0}) (ℵ₁ : Cardinal.{0}) (ω₁ * 2) := by
  rw [Ordinal.mul_two]
  exact omega1_stab

end TerminalSeq
