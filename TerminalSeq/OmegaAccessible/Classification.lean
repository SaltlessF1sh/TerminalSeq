import TerminalSeq.OmegaAccessible.TrnkovaLemmas

/-!
# Classification of Stabilization Ordinals for ω-Accessible Set Functors

Formalizes Proposition 2.1, Theorem 2.2, Worrell's upper bound `Stab(F) ≤ ω + ω`, and
the complete 4-point convergence classification for `ω`-accessible endofunctors `F : SetFunctor`:

* `terminal_bijective_of_proper_subset_surjective` (**Proposition 2.1**)
* `not_stabilizes_succ_of_ge_one` (**Theorem 2.2**): `∀ α ≥ 1, ¬ Stabilizes F (Order.succ α)`
* `stabilizesAt_omega_add_omega`: `StabilizesAt F (ω + ω)` for any `ω`-accessible `F`
* `omega_accessible_stab_four_points`: `∃ γ, Stabilizes F γ ∧ (γ = 0 ∨ γ = 1 ∨ γ = ω ∨ γ = ω + ω)`
-/

noncomputable section

open Classical

namespace TerminalSeq.OmegaAccessible

open TerminalSeq.Abstract Ordinal

section Prop21

/-- **Proposition 2.1**: Let `F` be `ω`-accessible and `X` a set with `|X| ≥ 2`.
If `T ⊂ X` is a proper subset such that `F.map (inc T) : F(T) → F(X)` is surjective,
then both `F(const z) : F(1) → F(X)` (for every `z : X`) and `F(!_X) : F(X) → F(1)`
are bijective. -/
theorem terminal_bijective_of_proper_subset_surjective {F : SetFunctor}
    (hacc : F.IsOmegaAccessible) {X : Type 1}
    (hcard : 2 ≤ Cardinal.mk X) {T : Set X} (hT : T ≠ Set.univ)
    (hsurj : Function.Surjective (F.map (SetFunctor.inc T))) :
    (∀ z : X, Function.Bijective (F.map (fun _ : PUnit.{2} => z))) ∧
      Function.Bijective (F.map (fun _ : X => PUnit.unit)) := by
  have hnt : Nontrivial X := by
    rw [← Cardinal.one_lt_iff_nontrivial]
    have h12 : (1 : Cardinal.{1}) < 2 := by simp
    exact lt_of_lt_of_le h12 hcard
  have hcompl_T : Tᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    exact hT
  obtain ⟨g, hgT⟩ := hcompl_T
  have hcompl_g_surj : Function.Surjective (F.map (SetFunctor.inc ({g}ᶜ : Set X))) := by
    have hsub : T ⊆ ({g}ᶜ : Set X) := fun x hx hxg => by
      have hxeq : x = g := Set.mem_singleton_iff.1 hxg
      exact hgT (hxeq ▸ hx)
    have hfact : SetFunctor.inc T = SetFunctor.inc ({g}ᶜ : Set X) ∘ Set.inclusion hsub := rfl
    intro x
    obtain ⟨u, rfl⟩ := hsurj x
    refine ⟨F.map (Set.inclusion hsub) u, ?_⟩
    rw [← F.map_comp_apply]
    rfl
  have hsingle : ∀ b : X, Function.Surjective (F.map (SetFunctor.inc ({b}ᶜ : Set X))) := by
    intro b
    let σ : Equiv.Perm X := Equiv.swap g b
    let σSub : ↥({g}ᶜ : Set X) → ↥({b}ᶜ : Set X) := fun x =>
      ⟨σ x.1, by
        intro hx
        apply x.2
        have h1 : σ x.1 = σ g := by simpa [σ] using hx
        exact σ.injective h1⟩
    have hcomm : SetFunctor.inc ({b}ᶜ : Set X) ∘ σSub = σ ∘ SetFunctor.inc ({g}ᶜ : Set X) := by
      funext x; rfl
    have hFσ : Function.Bijective (F.map (σ : X → X)) := F.map_bijective σ.bijective
    intro y
    obtain ⟨y', hy'⟩ := hFσ.2 y
    obtain ⟨u, hu⟩ := hcompl_g_surj y'
    refine ⟨F.map σSub u, ?_⟩
    rw [← F.map_comp_apply, hcomm, F.map_comp_apply, hu, hy']
  have hconst_surj : ∀ z : X, Function.Surjective (F.map (fun _ : PUnit.{2} => z)) := by
    intro z x
    rcases finite_or_infinite X with hfin | hinf
    · have : Finite X := hfin
      let E : Finset X := (@Finset.univ X (Fintype.ofFinite X)).erase z
      have hE_eq : ((E : Set X)ᶜ) = ({z} : Set X) := by
        ext y
        simp [E]
      have hE_ne : ((E : Set X)ᶜ).Nonempty := by
        rw [hE_eq]
        exact ⟨z, rfl⟩
      obtain ⟨u, hu⟩ := surjective_compl_finset_of_compl_singleton hsingle E hE_ne x
      let c : ↥((E : Set X)ᶜ) → PUnit.{2} := fun _ => PUnit.unit
      have hinc_fact : SetFunctor.inc ((E : Set X)ᶜ) =
          (fun _ : PUnit.{2} => z) ∘ c := by
        funext a
        have ha : a.1 ∈ ({z} : Set X) := by rw [← hE_eq]; exact a.2
        exact Set.mem_singleton_iff.1 ha
      refine ⟨F.map c u, ?_⟩
      rw [← F.map_comp_apply, ← hinc_fact, hu]
    · have : Infinite X := hinf
      obtain ⟨S, hS_fin, u, hu⟩ := hacc x
      let B₀ : Finset X := hS_fin.toFinset
      have hB₀_eq : (B₀ : Set X) = S := hS_fin.coe_toFinset
      have hcompl_ne : ((B₀ : Set X)ᶜ).Nonempty := by
        rw [Set.nonempty_compl]
        intro huniv
        have hfin_univ : (Set.univ : Set X).Finite := huniv ▸ B₀.finite_toSet
        exact hinf.not_finite (Set.finite_univ_iff.1 hfin_univ)
      by_cases hB₀ : B₀ = ∅
      · have hS_empty : S = ∅ := by simpa [hB₀] using hB₀_eq.symm
        let c : ↥S → PUnit.{2} := fun _ => PUnit.unit
        have hinc_fact : SetFunctor.inc S = (fun _ : PUnit.{2} => z) ∘ c := by
          funext a
          exfalso
          have ha : a.1 ∈ (∅ : Set X) := hS_empty ▸ a.2
          exact Set.notMem_empty a.1 ha
        refine ⟨F.map c u, ?_⟩
        rw [← F.map_comp_apply, ← hinc_fact, hu]
      · have hxB : x ∈ Set.range (F.map (SetFunctor.inc (B₀ : Set X))) := by
          refine ⟨F.map (Set.inclusion (le_of_eq hB₀_eq.symm)) u, ?_⟩
          rw [← F.map_comp_apply]
          exact hu
        have hxBc : x ∈ Set.range (F.map (SetFunctor.inc ((B₀ : Set X)ᶜ))) :=
          surjective_compl_finset_of_compl_singleton hsingle B₀ hcompl_ne x
        exact singleton_of_disjoint_range disjoint_compl_right hxB hxBc z
  have hconst_bij : ∀ z : X, Function.Bijective (F.map (fun _ : PUnit.{2} => z)) := by
    intro z
    have hcomp : (fun _ : X => PUnit.unit) ∘ (fun _ : PUnit.{2} => z) = id := by
      funext ⟨⟩; rfl
    have hinj : Function.Injective (F.map (fun _ : PUnit.{2} => z)) :=
      F.map_injective_of_leftInverse hcomp
    exact ⟨hinj, hconst_surj z⟩
  refine ⟨hconst_bij, ?_⟩
  let z₀ : X := hnt.to_nonempty.some
  let tX : X → PUnit.{2} := fun _ => PUnit.unit
  let cz : PUnit.{2} → X := fun _ => z₀
  have hcomp : tX ∘ cz = id := by funext ⟨⟩; rfl
  have hFcomp : F.map tX ∘ F.map cz = id := by
    funext w
    rw [Function.comp_apply, ← F.map_comp_apply, hcomp, F.map_id_apply]
    rfl
  have hcz_bij := hconst_bij z₀
  constructor
  · intro x₁ x₂ hx
    obtain ⟨w₁, rfl⟩ := hcz_bij.2 x₁
    obtain ⟨w₂, rfl⟩ := hcz_bij.2 x₂
    have hw₁ : F.map tX (F.map cz w₁) = w₁ := congrFun hFcomp w₁
    have hw₂ : F.map tX (F.map cz w₂) = w₂ := congrFun hFcomp w₂
    rw [← hw₁, ← hw₂, hx]
  · intro w
    exact ⟨F.map cz w, congrFun hFcomp w⟩

end Prop21

section Thm22

private theorem nontrivial_stage_one_of_stabilizes_gt_one {F : SetFunctor} {γ : Ordinal.{0}}
    (h1γ : 1 < γ) (hstab : Stabilizes F γ) :
    2 ≤ Cardinal.mk (A F 1) := by
  have hne : Nonempty (A F 1) := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have : IsEmpty (A F 1) := hempty
    exact absurd (stabilizes_unique hstab (stabilizes_one_of_isEmpty (F := F))) (ne_of_gt h1γ)
  have hnot_sub : ¬ Subsingleton (A F 1) := by
    intro hsub
    have h0 : StabilizesAt F 0 := stabilizesAt_zero_of_subsingleton (F := F)
    exact hstab.2 0 (lt_trans zero_lt_one h1γ) h0
  have hnt : Nontrivial (A F 1) := not_subsingleton_iff_nontrivial.1 hnot_sub
  have hlt1 : 1 < Cardinal.mk (A F 1) := Cardinal.one_lt_iff_nontrivial.2 hnt
  obtain ⟨a, b, hab⟩ := exists_pair_ne (A F 1)
  have hcard2 : (2 : Cardinal.{1}) ≤ Cardinal.mk (A F 1) := by
    have hmk : Cardinal.mk (ULift.{1, 0} Bool) = 2 := by simp
    rw [← hmk]
    apply Cardinal.mk_le_of_injective (f := fun c : ULift.{1, 0} Bool => if c.down then a else b)
    intro c₁ c₂ heq
    cases c₁ with | up b₁ => cases c₂ with | up b₂ =>
      cases b₁ <;> cases b₂ <;> simp_all [hab.symm]
  exact hcard2

/-- **Theorem 2.2**: For any `ω`-accessible endofunctor `F : SetFunctor` and any ordinal `α ≥ 1`,
`F` cannot stabilize at the successor ordinal `α + 1` (`Order.succ α`). -/
theorem not_stabilizes_succ_of_ge_one {F : SetFunctor} (hacc : F.IsOmegaAccessible) :
    ∀ α : Ordinal.{0}, 1 ≤ α → ¬ Stabilizes F (Order.succ α) := by
  intro α h1α hstab
  have h1_lt : 1 < Order.succ α := Order.lt_succ_of_le h1α
  have hcard1 : 2 ≤ Cardinal.mk (A F 1) :=
    nontrivial_stage_one_of_stabilizes_gt_one h1_lt hstab
  have hstab_succ : StabilizesAt F (Order.succ α) := hstab.1
  have hnot_stab_α : ¬ StabilizesAt F α := hstab.2 α (Order.lt_succ α)
  let p : A F (Order.succ α) → A F α := f (F := F) (Order.le_succ α)
  have hFp_bij : Function.Bijective (F.map p) := by
    have hcomm : succEquiv F α ∘ f (F := F) (Order.succ_le_succ (Order.le_succ α)) =
        F.map p ∘ succEquiv F (Order.succ α) := by
      funext x
      exact succEquiv_f_succ (F := F) (Order.le_succ α) x
    have hbij_L : Function.Bijective
        (succEquiv F α ∘ f (F := F) (Order.succ_le_succ (Order.le_succ α))) := by
      have h_eq : (Order.succ_le_succ (Order.le_succ α) :
          Order.succ α ≤ Order.succ (Order.succ α)) = Order.le_succ (Order.succ α) := rfl
      rw [h_eq]
      exact (succEquiv F α).bijective.comp hstab_succ
    rw [hcomm] at hbij_L
    have hsr := (succEquiv F (Order.succ α)).bijective
    exact ⟨fun a b hab => by
      obtain ⟨a', rfl⟩ := hsr.2 a
      obtain ⟨b', rfl⟩ := hsr.2 b
      exact congrArg (succEquiv F (Order.succ α)) (hbij_L.1 hab),
      fun y => by
        obtain ⟨x, hx⟩ := hbij_L.2 y
        exact ⟨succEquiv F (Order.succ α) x, hx⟩⟩
  by_cases hp_surj : Function.Surjective p
  · -- Case 2: `p` is surjective, hence not injective.
    have hp_not_inj : ¬ Function.Injective p :=
      fun hinj => hnot_stab_α ⟨hinj, hp_surj⟩
    have hex : ∃ x₁ x₂ : A F (Order.succ α), p x₁ = p x₂ ∧ x₁ ≠ x₂ := by
      by_contra h
      push Not at h
      exact hp_not_inj fun a b hab => h a b hab
    obtain ⟨x₁, x₂, hpeq, hxne⟩ := hex
    let y₀ : A F α := p x₁
    let σ₀ : A F α → A F (Order.succ α) := fun y => Classical.choose (hp_surj y)
    have hσ₀ : ∀ y, p (σ₀ y) = y := fun y => Classical.choose_spec (hp_surj y)
    let σ₁ : A F α → A F (Order.succ α) := fun y => if y = y₀ then x₁ else σ₀ y
    let σ₂ : A F α → A F (Order.succ α) := fun y => if y = y₀ then x₂ else σ₀ y
    have hpσ₁ : p ∘ σ₁ = id := by
      funext y
      dsimp [σ₁]
      split_ifs with h
      · exact h ▸ rfl
      · exact hσ₀ y
    have hpσ₂ : p ∘ σ₂ = id := by
      funext y
      dsimp [σ₂]
      split_ifs with h
      · exact h ▸ hpeq.symm
      · exact hσ₀ y
    have surj_of_rightInv : ∀ {σ : A F α → A F (Order.succ α)},
        p ∘ σ = id → Function.Surjective (F.map σ) := by
      intro σ hcomp u
      have hFcomp : F.map p ∘ F.map σ = id := by
        funext v
        rw [Function.comp_apply, ← F.map_comp_apply, hcomp, F.map_id_apply]
        rfl
      refine ⟨F.map p u, hFp_bij.1 (congrFun hFcomp (F.map p u))⟩
    have hFσ₁_surj : Function.Surjective (F.map σ₁) := surj_of_rightInv hpσ₁
    have hFσ₂_surj : Function.Surjective (F.map σ₂) := surj_of_rightInv hpσ₂
    let S₁ : Set (A F (Order.succ α)) := Set.range σ₁
    let S₂ : Set (A F (Order.succ α)) := Set.range σ₂
    let T₀ : Set (A F (Order.succ α)) := σ₁ '' ({y₀}ᶜ : Set (A F α))
    have hinter_eq : S₁ ∩ S₂ = T₀ := by
      ext t
      constructor
      · rintro ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩
        have ha12 : a₁ = a₂ := by
          have hp1 : p (σ₁ a₁) = a₁ := congrFun hpσ₁ a₁
          have hp2 : p (σ₂ a₂) = a₂ := congrFun hpσ₂ a₂
          rw [← hp1, ha₁, ← ha₂, hp2]
        subst ha12
        have hne_y₀ : a₁ ≠ y₀ := by
          intro heq
          subst heq
          have h12 : x₁ = x₂ := by
            calc
              x₁ = σ₁ y₀ := by simp [σ₁]
              _ = t := ha₁
              _ = σ₂ y₀ := ha₂.symm
              _ = x₂ := by simp [σ₂]
          exact hxne h12
        exact ⟨a₁, hne_y₀, ha₁⟩
      · rintro ⟨a, ha, rfl⟩
        refine ⟨⟨a, rfl⟩, ⟨a, ?_⟩⟩
        have hne : a ≠ y₀ := ha
        simp [σ₁, σ₂, hne]
    have hcard_α : 2 ≤ Cardinal.mk (A F α) :=
      le_trans hcard1 (card_one_le_of_one_le h1α)
    have hnt_α : Nontrivial (A F α) := by
      rw [← Cardinal.one_lt_iff_nontrivial]
      have h12 : (1 : Cardinal.{1}) < 2 := by simp
      exact lt_of_lt_of_le h12 hcard_α
    have hT₀_ne_empty : T₀.Nonempty := by
      obtain ⟨y₁, hy₁⟩ := exists_ne y₀
      exact ⟨σ₁ y₁, y₁, hy₁, rfl⟩
    have hinter_ne : (S₁ ∩ S₂).Nonempty := by
      simpa [hinter_eq] using hT₀_ne_empty
    have hT₀_ne_univ : T₀ ≠ Set.univ := by
      intro huniv
      have hx₁ : x₁ ∈ T₀ := huniv ▸ Set.mem_univ x₁
      obtain ⟨y, hy, hyx⟩ := hx₁
      have hp_eq : y = y₀ := by
        calc
          y = p (σ₁ y) := (congrFun hpσ₁ y).symm
          _ = p x₁ := by rw [hyx]
          _ = y₀ := rfl
      exact hy hp_eq
    have surj_range_inc : ∀ {σ : A F α → A F (Order.succ α)},
        Function.Surjective (F.map σ) →
          Function.Surjective (F.map (SetFunctor.inc (Set.range σ))) := by
      intro σ hσ u
      let r : A F α → ↥(Set.range σ) := Set.rangeFactorization σ
      obtain ⟨v, hv⟩ := hσ u
      refine ⟨F.map r v, ?_⟩
      rw [← F.map_comp_apply]
      exact hv
    have hFT₀_surj : Function.Surjective (F.map (SetFunctor.inc T₀)) := by
      intro u
      have hu : u ∈ Set.range (F.map (SetFunctor.inc S₁)) ∩
          Set.range (F.map (SetFunctor.inc S₂)) :=
        ⟨surj_range_inc hFσ₁_surj u, surj_range_inc hFσ₂_surj u⟩
      rw [trnkova_inter hinter_ne] at hu
      obtain ⟨w, hw⟩ := hu
      refine ⟨F.map (Set.inclusion (le_of_eq hinter_eq)) w, ?_⟩
      rw [← F.map_comp_apply]
      exact hw
    have hcard_succ : 2 ≤ Cardinal.mk (A F (Order.succ α)) :=
      le_trans hcard1 (card_one_le_of_one_le h1_lt.le)
    have hFterm : Function.Bijective (F.map (fun _ : A F (Order.succ α) => PUnit.unit)) :=
      (terminal_bijective_of_proper_subset_surjective hacc hcard_succ hT₀_ne_univ hFT₀_surj).2
    have hstab1 : StabilizesAt F 1 :=
      stabilizesAt_one_of_section_and_terminal
        (f (F := F) h1_lt.le) (coneMap F (Order.succ α))
        (coneMap_rightInverse h1_lt.le) hFterm
    exact hstab.2 1 h1_lt hstab1
  · -- Case 1: `p` is not surjective.
    let T : Set (A F α) := Set.range p
    have hT_ne : T ≠ Set.univ := by
      intro huniv
      apply hp_surj
      intro y
      have hy : y ∈ T := huniv ▸ Set.mem_univ y
      exact hy
    have hFT_surj : Function.Surjective (F.map (SetFunctor.inc T)) := by
      let pr : A F (Order.succ α) → ↥T := Set.rangeFactorization p
      have hfact : p = SetFunctor.inc T ∘ pr := rfl
      intro z
      obtain ⟨w, hw⟩ := hFp_bij.2 z
      refine ⟨F.map pr w, ?_⟩
      rw [← F.map_comp_apply, ← hfact, hw]
    have hcard_α : 2 ≤ Cardinal.mk (A F α) :=
      le_trans hcard1 (card_one_le_of_one_le h1α)
    have hFterm : Function.Bijective (F.map (fun _ : A F α => PUnit.unit)) :=
      (terminal_bijective_of_proper_subset_surjective hacc hcard_α hT_ne hFT_surj).2
    have hstab1 : StabilizesAt F 1 :=
      stabilizesAt_one_of_section_and_terminal (f (F := F) h1α) (coneMap F α)
        (coneMap_rightInverse h1α) hFterm
    exact hstab.2 1 h1_lt hstab1

end Thm22

section UpperBoundAndClassification

private theorem lt_omega_add_omega_le_add_nat {i : Ordinal.{0}}
    (hi : i < omega0 + omega0) :
    ∃ k : ℕ, i ≤ omega0 + (k : Ordinal.{0}) := by
  by_cases hiω : i ≤ omega0
  · exact ⟨0, by simpa using hiω⟩
  · have hlt : omega0 < i := lt_of_not_ge hiω
    have hd_lt : i - omega0 < omega0 := by
      rw [← add_lt_add_iff_left omega0, Ordinal.add_sub_cancel_of_le hlt.le]
      exact hi
    obtain ⟨k, hk⟩ := Ordinal.lt_omega0.1 hd_lt
    refine ⟨k, le_of_eq ?_⟩
    rw [← hk, Ordinal.add_sub_cancel_of_le hlt.le]

/-- **Worrell's Upper Bound**: Every `ω`-accessible set endofunctor stabilizes by `ω + ω`. -/
theorem stabilizesAt_omega_add_omega {F : SetFunctor} (hacc : F.IsOmegaAccessible) :
    StabilizesAt F (omega0 + omega0) := by
  by_cases hempty : IsEmpty (A F 1)
  · have : IsEmpty (A F 1) := hempty
    have h1 : StabilizesAt F 1 := (stabilizes_one_of_isEmpty (F := F)).1
    have h1ω : (1 : Ordinal.{0}) ≤ omega0 + omega0 :=
      le_trans (by simpa using (Ordinal.lt_omega0.2 ⟨1, rfl⟩).le) le_self_add
    exact (stabilizesAt_upward h1 h1ω).2
  · rw [not_isEmpty_iff] at hempty
    have : Nonempty (A F 1) := hempty
    have hlim_ω : Order.IsSuccLimit omega0 := by
      simp
    have hacc_card : F.IsAccessible Cardinal.aleph0 :=
      (SetFunctor.isAccessible_aleph0_iff F).2 hacc
    have htail : ∀ {α β : Ordinal.{0}}, omega0 ≤ α → ∀ (hαβ : α ≤ β),
        Function.Injective (f (F := F) hαβ) := by
      intro α β hα hαβ
      exact tail_monic_of_accessible Cardinal.isRegular_aleph0 hacc_card
        (by simpa [Cardinal.ord_aleph0] using hα) hαβ
    have hωω : omega0 ≤ omega0 + omega0 := le_self_add
    have hinj_step : Function.Injective (f (F := F) (Order.le_succ (omega0 + omega0))) :=
      htail hωω (Order.le_succ (omega0 + omega0))
    refine ⟨hinj_step, fun y => ?_⟩
    let C : ℕ → Set (A F omega0) := fun k =>
      Set.range (f (F := F) (le_self_add : omega0 ≤ omega0 + (k : Ordinal.{0})))
    let Cω : Set (A F omega0) := Set.range (f (F := F) hωω)
    have hC_mono : ∀ {k m : ℕ}, k ≤ m → C m ⊆ C k := by
      intro k m hkm z ⟨a, ha⟩
      have hωkm : omega0 + (k : Ordinal.{0}) ≤ omega0 + (m : Ordinal.{0}) :=
        add_le_add_right (Nat.cast_le.2 hkm) omega0
      refine ⟨f (F := F) hωkm a, ?_⟩
      rw [← ha]
      exact (f_comp (le_self_add : omega0 ≤ omega0 + (k : Ordinal.{0})) hωkm a).symm
    have hCω_eq : ∀ z, (∀ k : ℕ, z ∈ C k) → z ∈ Cω := by
      intro z hz
      let zk : ∀ k : ℕ, A F (omega0 + (k : Ordinal.{0})) := fun k => Classical.choose (hz k)
      have hzk_spec : ∀ k : ℕ,
          f (F := F) (le_self_add : omega0 ≤ omega0 + (k : Ordinal.{0})) (zk k) = z :=
        fun k => Classical.choose_spec (hz k)
      have hzk_compat : ∀ {k m : ℕ} (hkm : k ≤ m),
          f (F := F) (add_le_add_right (Nat.cast_le.2 hkm) omega0) (zk m) = zk k := by
        intro k m hkm
        apply htail le_rfl (le_self_add : omega0 ≤ omega0 + (k : Ordinal.{0}))
        rw [← f_comp (le_self_add : omega0 ≤ omega0 + (k : Ordinal.{0}))
            (add_le_add_right (Nat.cast_le.2 hkm) omega0) (zk m)]
        rw [hzk_spec m, hzk_spec k]
      let kOf (i : Ordinal.{0}) (hi : i < omega0 + omega0) : ℕ :=
        Classical.choose (lt_omega_add_omega_le_add_nat hi)
      have hkOf_spec : ∀ {i : Ordinal.{0}} (hi : i < omega0 + omega0),
          i ≤ omega0 + (kOf i hi : Ordinal.{0}) :=
        fun hi => Classical.choose_spec (lt_omega_add_omega_le_add_nat hi)
      let t : (i : (omega0 + omega0).ToType) → A F i.toOrd.1 :=
        fun i => f (F := F) (hkOf_spec i.toOrd.2) (zk (kOf i.toOrd.1 i.toOrd.2))
      have hcompat : ∀ (i j : (omega0 + omega0).ToType) (hij : i.toOrd.1 ≤ j.toOrd.1),
          f (F := F) hij (t j) = t i := by
        intro i j hij
        let k₁ := kOf i.toOrd.1 i.toOrd.2
        let k₂ := kOf j.toOrd.1 j.toOrd.2
        let m := max k₁ k₂
        have hm₁ : k₁ ≤ m := le_max_left k₁ k₂
        have hm₂ : k₂ ≤ m := le_max_right k₁ k₂
        have hkm₁ : omega0 + (k₁ : Ordinal.{0}) ≤ omega0 + (m : Ordinal.{0}) :=
          add_le_add_right (Nat.cast_le.2 hm₁) omega0
        have hkm₂ : omega0 + (k₂ : Ordinal.{0}) ≤ omega0 + (m : Ordinal.{0}) :=
          add_le_add_right (Nat.cast_le.2 hm₂) omega0
        dsimp only [t]
        rw [← hzk_compat hm₁, ← hzk_compat hm₂]
        rw [← f_comp (hkOf_spec i.toOrd.2) hkm₁ (zk m)]
        rw [← f_comp (hkOf_spec j.toOrd.2) hkm₂ (zk m)]
        exact (f_comp hij ((hkOf_spec j.toOrd.2).trans hkm₂) (zk m)).symm
      have hlim_ωω : Order.IsSuccLimit (omega0 + omega0) :=
        Ordinal.isSuccLimit_add omega0 hlim_ω
      let z_lim : A F (omega0 + omega0) := (limitEquiv F hlim_ωω).symm ⟨t, hcompat⟩
      refine ⟨z_lim, ?_⟩
      have hω_lt : omega0 < omega0 + omega0 := by
        simp
      let iω : (omega0 + omega0).ToType := Ordinal.ToType.mk ⟨omega0, hω_lt⟩
      have hiω : iω.toOrd.1 = omega0 := by simp [iω]
      have hp := congrArg (fun q : { q : (j : (omega0 + omega0).ToType) → A F j.toOrd.1 // _ } => q.1 iω)
        ((limitEquiv F hlim_ωω).apply_symm_apply ⟨t, hcompat⟩)
      rw [limitEquiv_proj] at hp
      have hrew : ∀ (o : Ordinal.{0}) (ho : o ≤ omega0 + omega0) (heq : o = omega0) (a : A F o),
          f (F := F) ho z_lim = a → f (F := F) hωω z_lim = cast (congrArg (A F) heq) a := by
        rintro o _ rfl a rfl; rfl
      have hfω : f (F := F) hωω z_lim = cast (congrArg (A F) hiω) (t iω) :=
        hrew iω.toOrd.1 iω.toOrd.2.le hiω (t iω) hp
      rw [hfω]
      have hfin : ∀ (o : Ordinal.{0}) (ho : o < omega0 + omega0) (heq : o = omega0),
          cast (congrArg (A F) heq)
            (f (F := F) (hkOf_spec ho) (zk (kOf o ho))) = z := by
        rintro o ho rfl
        exact hzk_spec _
      exact hfin iω.toOrd.1 iω.toOrd.2 hiω
    -- Now examine `y : A F (omega0 + omega0)` at stage `omega0 + 1`.
    have hω1_le : Order.succ omega0 ≤ omega0 + omega0 := by
      rw [Order.succ_le_iff]
      simp
    let y₁ : A F (Order.succ omega0) := f (F := F) hω1_le y
    let u₀ : F.obj (A F omega0) := succEquiv F omega0 y₁
    have hu₀_in_Ck : ∀ k : ℕ, u₀ ∈ Set.range (F.map (SetFunctor.inc (C k))) := by
      intro k
      have hk : omega0 ≤ omega0 + (k : Ordinal.{0}) := le_self_add
      have hsucc_k : Order.succ (omega0 + (k : Ordinal.{0})) ≤ omega0 + omega0 := by
        rw [Order.succ_le_iff]
        exact (add_lt_add_iff_left omega0).2 (Ordinal.lt_omega0.2 ⟨k, rfl⟩)
      let yk1 : A F (Order.succ (omega0 + (k : Ordinal.{0}))) := f (F := F) hsucc_k y
      have hproj : f (F := F) (Order.succ_le_succ hk) yk1 = y₁ := by
        dsimp only [y₁, yk1]
        exact (f_comp (Order.succ_le_succ hk) hsucc_k y).symm
      have hu_eq : u₀ = F.map (f (F := F) hk) (succEquiv F (omega0 + (k : Ordinal.{0})) yk1) := by
        dsimp only [u₀]
        rw [← hproj, succEquiv_f_succ hk yk1]
      let rk : A F (omega0 + (k : Ordinal.{0})) → ↥(C k) :=
        Set.rangeFactorization (f (F := F) hk)
      refine ⟨F.map rk (succEquiv F (omega0 + (k : Ordinal.{0})) yk1), ?_⟩
      rw [← F.map_comp_apply]
      exact hu_eq.symm
    obtain ⟨S_set, hS_fin, u_S, hu_S⟩ := hacc u₀
    let S : Finset (A F omega0) := hS_fin.toFinset
    have hS_eq : (S : Set (A F omega0)) = S_set := hS_fin.coe_toFinset
    have hu₀_in_S : u₀ ∈ Set.range (F.map (SetFunctor.inc (S : Set (A F omega0)))) := by
      refine ⟨F.map (Set.inclusion (le_of_eq hS_eq.symm)) u_S, ?_⟩
      rw [← F.map_comp_apply]
      exact hu_S
    let exitIdx : A F omega0 → ℕ := fun s =>
      if h : ∃ k : ℕ, s ∉ C k then Nat.find h else 0
    let N : ℕ := S.sup exitIdx
    have hCN_sub : (S : Set (A F omega0)) ∩ C N ⊆ Cω := by
      rintro s ⟨hsS, hsCN⟩
      apply hCω_eq
      intro k
      by_contra hnot
      have hex : ∃ m : ℕ, s ∉ C m := ⟨k, hnot⟩
      have hfind_le : Nat.find hex ≤ N := by
        have hle : exitIdx s ≤ N := Finset.le_sup (f := exitIdx) (by simpa [S, hS_eq] using hsS)
        simpa [exitIdx, hex] using hle
      exact Nat.find_spec hex (hC_mono hfind_le hsCN)
    have hu₀_in_Cω : u₀ ∈ Set.range (F.map (SetFunctor.inc Cω)) := by
      by_cases hinter : ((S : Set (A F omega0)) ∩ C N).Nonempty
      · have hmem : u₀ ∈ Set.range (F.map (SetFunctor.inc (S : Set (A F omega0)))) ∩
            Set.range (F.map (SetFunctor.inc (C N))) :=
          ⟨hu₀_in_S, hu₀_in_Ck N⟩
        rw [trnkova_inter hinter] at hmem
        obtain ⟨w, hw⟩ := hmem
        refine ⟨F.map (Set.inclusion hCN_sub) w, ?_⟩
        rw [← F.map_comp_apply]
        exact hw
      · rw [Set.not_nonempty_iff_eq_empty] at hinter
        have hdisj : Disjoint (S : Set (A F omega0)) (C N) :=
          Set.disjoint_iff_inter_eq_empty.2 hinter
        let y₀ : A F omega0 := f (F := F) hωω y
        obtain ⟨w, hw⟩ := singleton_of_disjoint_range hdisj hu₀_in_S (hu₀_in_Ck N) y₀
        let pick : PUnit.{2} → ↥Cω := fun _ => ⟨y₀, ⟨y, rfl⟩⟩
        refine ⟨F.map pick w, ?_⟩
        rw [← F.map_comp_apply]
        exact hw
    obtain ⟨v, hv⟩ := hu₀_in_Cω
    have hinj_ωω : Function.Injective (f (F := F) hωω) := htail le_rfl hωω
    let g : A F (omega0 + omega0) → ↥Cω := Set.rangeFactorization (f (F := F) hωω)
    have hg_bij : Function.Bijective g :=
      ⟨fun a b hab => hinj_ωω (congrArg Subtype.val hab),
        fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩⟩
    let ge : A F (omega0 + omega0) ≃ ↥Cω := Equiv.ofBijective g hg_bij
    let w : F.obj (A F (omega0 + omega0)) := F.map ge.symm v
    have hFw : F.map (f (F := F) hωω) w = u₀ := by
      have hfact : f (F := F) hωω ∘ ge.symm = SetFunctor.inc Cω := by
        funext z
        exact congrArg Subtype.val (ge.apply_symm_apply z)
      dsimp only [w]
      rw [← F.map_comp_apply, hfact, hv]
    let x : A F (Order.succ (omega0 + omega0)) := (succEquiv F (omega0 + omega0)).symm w
    refine ⟨x, ?_⟩
    have hx_at_ω1 : f (F := F) (hω1_le.trans (Order.le_succ (omega0 + omega0))) x = y₁ := by
      apply (succEquiv F omega0).injective
      have h_eq : (hω1_le.trans (Order.le_succ (omega0 + omega0)) :
          Order.succ omega0 ≤ Order.succ (omega0 + omega0)) = Order.succ_le_succ hωω := rfl
      rw [h_eq, succEquiv_f_succ hωω x]
      dsimp only [x]
      rw [Equiv.apply_symm_apply, hFw]
    have hlim_ωω : Order.IsSuccLimit (omega0 + omega0) :=
      Ordinal.isSuccLimit_add omega0 hlim_ω
    apply (limitEquiv F hlim_ωω).injective
    apply Subtype.ext
    funext i
    rw [limitEquiv_proj, limitEquiv_proj]
    obtain ⟨k, hik⟩ := lt_omega_add_omega_le_add_nat i.toOrd.2
    have hik1 : i.toOrd.1 ≤ omega0 + ((k + 1 : ℕ) : Ordinal.{0}) :=
      hik.trans (add_le_add_right (Nat.cast_le.2 (Nat.le_succ k)) omega0)
    have hk1_lt : omega0 + ((k + 1 : ℕ) : Ordinal.{0}) < omega0 + omega0 :=
      (add_lt_add_iff_left omega0).2 (Ordinal.lt_omega0.2 ⟨k + 1, rfl⟩)
    have hω1_le_k1 : Order.succ omega0 ≤ omega0 + ((k + 1 : ℕ) : Ordinal.{0}) := by
      rw [Order.succ_eq_add_one]
      exact add_le_add_right (by norm_cast; omega) omega0
    have h_eq_k1 : f (F := F) (hk1_lt.le.trans (Order.le_succ (omega0 + omega0))) x =
        f (F := F) hk1_lt.le y := by
      apply htail (Order.le_succ omega0) hω1_le_k1
      rw [← f_comp hω1_le_k1 (hk1_lt.le.trans (Order.le_succ (omega0 + omega0))) x]
      rw [← f_comp hω1_le_k1 hk1_lt.le y]
      exact hx_at_ω1
    rw [← f_comp i.toOrd.2.le (Order.le_succ (omega0 + omega0)) x]
    rw [f_comp hik1 (hk1_lt.le.trans (Order.le_succ (omega0 + omega0))) x]
    rw [h_eq_k1, ← f_comp hik1 hk1_lt.le y]

/-- Corollary: Every exact stabilization ordinal of an `ω`-accessible set functor must belong to
`{0, 1, ω, ω + ω}`. -/
theorem stab_mem_four_points {F : SetFunctor} (hacc : F.IsOmegaAccessible) {γ : Ordinal.{0}}
    (hstab : Stabilizes F γ) :
    γ = 0 ∨ γ = 1 ∨ γ = omega0 ∨ γ = omega0 + omega0 := by
  have hωω : StabilizesAt F (omega0 + omega0) := stabilizesAt_omega_add_omega hacc
  have hle : γ ≤ omega0 + omega0 := by
    by_contra hgt
    exact hstab.2 (omega0 + omega0) (lt_of_not_ge hgt) hωω |>.elim
  rcases lt_trichotomy γ omega0 with hlt | rfl | hgt
  · obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.1 hlt
    rcases m with _ | _ | k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (by simp))
    · exfalso
      have hsucc : ((k + 2 : ℕ) : Ordinal.{0}) = Order.succ ((k + 1 : ℕ) : Ordinal.{0}) := by
        rw [Order.succ_eq_add_one]
        norm_cast
      rw [hsucc] at hstab
      exact not_stabilizes_succ_of_ge_one hacc ((k + 1 : ℕ) : Ordinal.{0})
        (by exact_mod_cast (by omega : 1 ≤ k + 1)) hstab
  · exact Or.inr (Or.inr (Or.inl rfl))
  · rcases eq_or_lt_of_le hle with rfl | hlt_ωω
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exfalso
      have hd_lt : γ - omega0 < omega0 := by
        rw [← add_lt_add_iff_left omega0, Ordinal.add_sub_cancel_of_le hgt.le]
        exact hlt_ωω
      obtain ⟨m, hm⟩ := Ordinal.lt_omega0.1 hd_lt
      have hm_pos : 0 < m := by
        by_contra hm0
        have hm0' : m = 0 := by omega
        subst hm0'
        have hEq : γ = omega0 := by
          calc
            γ = omega0 + (γ - omega0) := (Ordinal.add_sub_cancel_of_le hgt.le).symm
            _ = omega0 + (0 : ℕ) := by rw [← hm]
            _ = omega0 := by simp
        exact hgt.ne' hEq
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hm_pos)
      have hsucc : γ = Order.succ (omega0 + (n : Ordinal.{0})) := by
        calc
          γ = omega0 + (γ - omega0) := (Ordinal.add_sub_cancel_of_le hgt.le).symm
          _ = omega0 + ((n + 1 : ℕ) : Ordinal.{0}) := by rw [← hm]
          _ = omega0 + ((n : Ordinal.{0}) + 1) := by norm_cast
          _ = (omega0 + (n : Ordinal.{0})) + 1 := (add_assoc _ _ _).symm
          _ = Order.succ (omega0 + (n : Ordinal.{0})) := (Order.succ_eq_add_one _).symm
      rw [hsucc] at hstab
      have h1ω : (1 : Ordinal.{0}) ≤ omega0 + (n : Ordinal.{0}) :=
        le_trans (by simpa using (Ordinal.lt_omega0.2 ⟨1, rfl⟩).le) le_self_add
      exact not_stabilizes_succ_of_ge_one hacc (omega0 + (n : Ordinal.{0})) h1ω hstab

/-- **Main 4-Point Classification Theorem**: Every `ω`-accessible endofunctor `F : SetFunctor`
has a unique exact stabilization ordinal `γ`, and `γ ∈ {0, 1, ω, ω + ω}`. -/
theorem omega_accessible_stab_four_points {F : SetFunctor} (hacc : F.IsOmegaAccessible) :
    ∃ γ : Ordinal.{0}, Stabilizes F γ ∧
      (γ = 0 ∨ γ = 1 ∨ γ = omega0 ∨ γ = omega0 + omega0) := by
  obtain ⟨γ, _, hstab⟩ := exists_stabilizes_of_stabilizesAt (stabilizesAt_omega_add_omega hacc)
  exact ⟨γ, hstab, stab_mem_four_points hacc hstab⟩

end UpperBoundAndClassification

end TerminalSeq.OmegaAccessible

