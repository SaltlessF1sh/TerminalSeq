import TerminalSeq.FinalSequence
import TerminalSeq.AccessibleAndMonic
import TerminalSeq.Step1_BoundedPowerset
import TerminalSeq.Step2_GeneralStab
import TerminalSeq.Seminar_Omega1
import TerminalSeq.Abstract.SetFunctor
import TerminalSeq.Abstract.FinalSequence
import TerminalSeq.Abstract.Stabilization
import TerminalSeq.OmegaAccessible.TrnkovaLemmas
import TerminalSeq.OmegaAccessible.Classification

/-!
# Terminal Sequence Stabilization of Set Functors

Top-level umbrella module exporting the entire formalization:

## Part I: Explicit Family `G_{κ,θ}` with Exact Stabilization `κ + θ`
- `TerminalSeq.FinalSequence`: Functor `GFunctor κ θ : SetFunctor` instantiating `TerminalSeq.Abstract`
- `TerminalSeq.AccessibleAndMonic`: `κ`-accessibility (`G_isAccessible`) and tail monicity via `Abstract.tail_monic_of_accessible`
- `TerminalSeq.Step1_BoundedPowerset`: `f_κ^{κ+1}` non-surjectivity for arbitrary regular `κ`
- `TerminalSeq.Step2_GeneralStab`: Exact stabilization theorem `Stab(G_{κ,θ}) = κ + θ`
- `TerminalSeq.Seminar_Omega1`: Specialization `κ = θ = ℵ₁` giving `Stab(G) = ω₁ + ω₁ = ω₁ * 2`

## Part II: Abstract Final-Sequence Infrastructure & 4-Point Classification for `ω`-Accessible Functors
- `TerminalSeq.Abstract.SetFunctor`: `SetFunctor` (`Type 1 → Type 1`) and `κ`- / `ω`-accessibility
- `TerminalSeq.Abstract.FinalSequence`: Terminal sequence `A F α` for arbitrary `SetFunctor`
- `TerminalSeq.Abstract.Stabilization`: `StabilizesAt`, `Stabilizes`, Lemma 1.4 (`coneMap`), and `tail_monic_of_accessible`
- `TerminalSeq.OmegaAccessible.TrnkovaLemmas`: Lemmas 1.1–1.3 (Trnková pullback, disjoint support, constant retract)
- `TerminalSeq.OmegaAccessible.Classification`: Proposition 2.1, Theorem 2.2 (`∀ α ≥ 1, Stab(F) ≠ α + 1`),
  Worrell's upper bound `Stab(F) ≤ ω + ω`, and the 4-point theorem `Stab(F) ∈ {0, 1, ω, ω + ω}`
-/

#print axioms TerminalSeq.G_isAccessible
#print axioms TerminalSeq.tail_monic
#print axioms TerminalSeq.step1_not_surjective_kappa
#print axioms TerminalSeq.stab_general_kappa_theta
#print axioms TerminalSeq.omega1_stab

#print axioms TerminalSeq.Abstract.tail_monic_of_accessible
#print axioms TerminalSeq.OmegaAccessible.trnkova_inter
#print axioms TerminalSeq.OmegaAccessible.singleton_of_disjoint_range
#print axioms TerminalSeq.OmegaAccessible.stabilizesAt_one_of_section_and_terminal
#print axioms TerminalSeq.OmegaAccessible.terminal_bijective_of_proper_subset_surjective
#print axioms TerminalSeq.OmegaAccessible.not_stabilizes_succ_of_ge_one
#print axioms TerminalSeq.OmegaAccessible.stabilizesAt_omega_add_omega
#print axioms TerminalSeq.OmegaAccessible.stab_mem_four_points
#print axioms TerminalSeq.OmegaAccessible.omega_accessible_stab_four_points
