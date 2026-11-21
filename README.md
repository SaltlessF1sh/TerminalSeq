# Terminal Sequence Stabilization of Set Functors (Lean 4 Formalization)

Self-contained **Lean 4 + Mathlib** (`v4.36.0`) formalization and bilingual mathematical proofs (LaTeX + PDF) covering two results on the terminal sequence of set endofunctors, with zero `sorry`s and relying only on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`):

1. **Part I (`Stab(G_{κ,θ}) = κ + θ`)**: For any infinite regular cardinals $\omega \le \theta \le \kappa$, the terminal sequence of

```math
G_{\kappa,\theta}(X) = \mathcal{P}_{<\kappa}(X) \;\sqcup\; \bigsqcup_{\substack{\mu < \theta \\ \mu\text{ infinite regular}}} \bigl(X^\mu / {\equiv_{<\mu}}\bigr)
```

stabilizes at exact ordinal $\kappa + \theta$ (specializing $\kappa = \theta = \aleph_1$ to $\omega_1 + \omega_1 = \omega_1 \cdot 2$).

2. **Part II ($\omega$-Accessible 4-Point Classification)**: For any $\omega$-accessible (finitary) set endofunctor $F : \mathbf{Set} \to \mathbf{Set}$, every ordinal $\alpha \ge 1$ satisfies $\mathrm{Stab}(F) \neq \alpha + 1$ and $\mathrm{Stab}(F) \le \omega + \omega$, yielding the complete classification

```math
\mathrm{Stab}(F) \in \{0,\; 1,\; \omega,\; \omega + \omega\}.
```

---

## Repository Structure

### General Infrastructure (`TerminalSeq/Abstract/`)
| File | Description |
| --- | --- |
| [`TerminalSeq/Abstract/SetFunctor.lean`](TerminalSeq/Abstract/SetFunctor.lean) | Abstract set endofunctors `SetFunctor` (`Type 1 → Type 1`), preservation of bijections/retractions, $\kappa$-accessibility and $\omega$-accessibility (`IsAccessible`, `IsOmegaAccessible`) |
| [`TerminalSeq/Abstract/FinalSequence.lean`](TerminalSeq/Abstract/FinalSequence.lean) | Terminal sequence `(A F α, f h)` for arbitrary `SetFunctor` with `zeroEquiv`, `succEquiv`, `limitEquiv`, and naturality lemmas |
| [`TerminalSeq/Abstract/Stabilization.lean`](TerminalSeq/Abstract/Stabilization.lean) | `StabilizesAt`, `Stabilizes`, uniqueness & upward closure, Lemma 1.4 constant-coalgebra cone sections (`coneMap`), and general tail monicity (`tail_monic_of_accessible`) |

### Part I: Explicit Family `G_{κ,θ}` with Exact Stabilization `κ + θ`
| File | Description |
| --- | --- |
| [`TerminalSeq/FinalSequence.lean`](TerminalSeq/FinalSequence.lean) | Functor `GFunctor κ θ : SetFunctor` and terminal sequence API instantiating `TerminalSeq.Abstract` |
| [`TerminalSeq/AccessibleAndMonic.lean`](TerminalSeq/AccessibleAndMonic.lean) | $\kappa$-accessibility (`G_isAccessible`) and tail monicity (`tail_monic`, `f_kappa_succ_injective`) via `Abstract.tail_monic_of_accessible` |
| [`TerminalSeq/Step1_BoundedPowerset.lean`](TerminalSeq/Step1_BoundedPowerset.lean) | Step 1: non-surjectivity of $f_\kappa^{\kappa+1}$ via the bounded powerset diagonal family (`step1_not_surjective_kappa`) |
| [`TerminalSeq/Step2_GeneralStab.lean`](TerminalSeq/Step2_GeneralStab.lean) | Step 2: rank filtration $B_\beta$, delay operators $\sigma, \tau_\mu$, rank realization (`exists_witness_rank`), regularity closure (`B_theta_closed`), and main theorem (`stab_general_kappa_theta`) |
| [`TerminalSeq/Seminar_Omega1.lean`](TerminalSeq/Seminar_Omega1.lean) | Specialization to $\kappa = \theta = \aleph_1$ (`omega1_stab`, `omega1_stab_mul_two`) |

### Part II: Convergence-Point Classification for $\omega$-Accessible Functors (`TerminalSeq/OmegaAccessible/`)
| File | Description |
| --- | --- |
| [`TerminalSeq/OmegaAccessible/TrnkovaLemmas.lean`](TerminalSeq/OmegaAccessible/TrnkovaLemmas.lean) | Lemma 1.1 (Trnková intersection `trnkova_inter`), Lemma 1.2 (disjoint support collapse `singleton_of_disjoint_range`), and Lemma 1.3 (`stabilizesAt_one_of_section_and_terminal`) |
| [`TerminalSeq/OmegaAccessible/Classification.lean`](TerminalSeq/OmegaAccessible/Classification.lean) | Proposition 2.1 (`terminal_bijective_of_proper_subset_surjective`), Theorem 2.2 (`not_stabilizes_succ_of_ge_one`), Worrell upper bound (`stabilizesAt_omega_add_omega`), and 4-point theorem (`omega_accessible_stab_four_points`, `stab_mem_four_points`) |

### Top-Level Entry & Mathematical Proofs (`docs/`)
| File | Description |
| --- | --- |
| [`TerminalSeq.lean`](TerminalSeq.lean) | Umbrella module re-exporting all developments and running `#print axioms` checks |
| [`docs/proof_zh.pdf`](docs/proof_zh.pdf) ([`.tex`](docs/proof_zh.tex)) | Part I 完整中文数学证明 — 精确稳定阶 $\kappa + \theta$ |
| [`docs/proof_en.pdf`](docs/proof_en.pdf) ([`.tex`](docs/proof_en.tex)) | Part I Complete English proof — exact stabilization $\kappa + \theta$ |
| [`docs/omega_accessible_zh.pdf`](docs/omega_accessible_zh.pdf) ([`.tex`](docs/omega_accessible_zh.tex)) | Part II 完整中文数学证明 — $\omega$-可达函子四点收敛分类 |
| [`docs/omega_accessible_en.pdf`](docs/omega_accessible_en.pdf) ([`.tex`](docs/omega_accessible_en.tex)) | Part II Complete English proof — 4-point classification for $\omega$-accessible functors |

---

## Main Formalized Theorems

### Part I (`G_{κ,θ}`)
- `TerminalSeq.G_isAccessible` — $G_{\kappa,\theta}$ is $\kappa$-accessible whenever $\theta \le \kappa$.
- `TerminalSeq.tail_monic` — $f_\alpha^\beta$ is injective for all $\kappa \le \alpha \le \beta$ (when $\kappa$ is regular and $\theta \le \kappa$).
- `TerminalSeq.step1_not_surjective_kappa` — $f_\kappa^{\kappa+1}$ is not surjective for any regular cardinal $\kappa$ (independent of $\theta$).
- `TerminalSeq.stab_general_kappa_theta` — For regular $\kappa, \theta$ with $\theta \le \kappa$, `Stabilizes κ θ (κ.ord + θ.ord)`.
- `TerminalSeq.omega1_stab` & `TerminalSeq.omega1_stab_mul_two` — Specialization to $\aleph_1$: `Stabilizes ℵ₁ ℵ₁ (ω₁ + ω₁)` and `Stabilizes ℵ₁ ℵ₁ (ω₁ * 2)`.

### Part II ($\omega$-Accessible 4-Point Classification)
- `TerminalSeq.Abstract.tail_monic_of_accessible` — For regular $\kappa$ and $\kappa$-accessible $F$ with stage-1 object $A_1$ nonempty, every tail transition map is injective for $\kappa \le \alpha \le \beta$.
- `TerminalSeq.OmegaAccessible.trnkova_inter` / `singleton_of_disjoint_range` / `stabilizesAt_one_of_section_and_terminal` — Lemmas 1.1, 1.2, and 1.3.
- `TerminalSeq.OmegaAccessible.terminal_bijective_of_proper_subset_surjective` — Proposition 2.1.
- `TerminalSeq.OmegaAccessible.not_stabilizes_succ_of_ge_one` — Theorem 2.2: $\forall \alpha \ge 1,\; \mathrm{Stab}(F) \neq \alpha + 1$.
- `TerminalSeq.OmegaAccessible.stabilizesAt_omega_add_omega` — Worrell upper bound: every $\omega$-accessible $F$ stabilizes by $\omega + \omega$.
- `TerminalSeq.OmegaAccessible.omega_accessible_stab_four_points` & `stab_mem_four_points` — Exact stabilization ordinal $\mathrm{Stab}(F) \in \{0, 1, \omega, \omega + \omega\}$.

---

## Building Locally

Requires **Lean 4 / Mathlib `v4.36.0`** (managed via `elan` and `lakefile.toml`).

```bash
lake exe cache get   # optional: fetch precompiled Mathlib cache
lake build
```
