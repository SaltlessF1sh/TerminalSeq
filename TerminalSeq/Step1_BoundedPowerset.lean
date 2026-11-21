import TerminalSeq.FinalSequence

/-!
# Step 1: Bounded Powerset Non-Surjectivity for Arbitrary Regular `κ`

Follows the non-circular construction from Step 1 of the seminar manuscript:
1. Constructs `qFun α β : A κ θ α` for `α ≤ κ.ord` and arbitrary `β` by well-founded
   recursion, without presupposing Lemma 1 or Lemma 2 in the recursion step.
2. Proves Lemma 1 (`qFun_eq_iff`: `q_α(β) = q_α(γ) ↔ min α β = min α γ`) and
   Lemma 2 (`f_qFun`: projection compatibility `f_δ^α (q_α(β)) = q_δ(β)`).
3. Sets `b_κ := q_κ(κ) ∈ A_κ` and proves `b_κ ∉ Set.range (f_κ^{κ+1})`.

Notice this entire module holds for **any** regular cardinal `κ` and **any** `θ : Cardinal.{0}`.
-/

noncomputable section

open Classical Ordinal Cardinal

namespace TerminalSeq

section Step1Construction

private noncomputable def qFun (κ θ : Cardinal.{0}) (hκ : κ.IsRegular) :
    (α : Ordinal.{0}) → Ordinal.{0} → A κ θ α :=
  WellFoundedLT.fix fun α rec =>
    if hα0 : α = 0 then
      fun _ => cast (congrArg (A κ θ) hα0.symm) ((zeroEquiv κ θ).symm PUnit.unit)
    else if hs : ∃ α', α = Order.succ α' then
      let α' := Classical.choose hs
      have hα' : α = Order.succ α' := Classical.choose_spec hs
      have hlt : α' < α := hα' ▸ Order.lt_succ α'
      if hακ : α' < κ.ord then
        fun β =>
          let hlim_κ : Order.IsSuccLimit κ.ord := Cardinal.isSuccLimit_ord hκ.aleph0_le
          have hsucc_lt : Order.succ α' < κ.ord := hlim_κ.succ_lt hακ
          let m := min β (Order.succ α')
          let S : Set (A κ θ α') := Set.range fun i : m.ToType => rec α' hlt i.toOrd.1
          have hm_le : m ≤ Order.succ α' := min_le_right β (Order.succ α')
          have hm_lt : m < κ.ord := lt_of_le_of_lt hm_le hsucc_lt
          have hm_card : Cardinal.mk m.ToType = m.card := by simp
          have hS : Cardinal.mk S < Cardinal.lift.{1, 0} κ := by
            have h1 := Cardinal.mk_range_le_lift (f := fun i : m.ToType => rec α' hlt i.toOrd.1)
            rw [Cardinal.lift_uzero, hm_card] at h1
            have h2 : m.card < κ := Cardinal.lt_ord.1 hm_lt
            exact lt_of_le_of_lt h1 (Cardinal.lift_lt.2 h2)
          let u : A κ θ (Order.succ α') := (succEquiv κ θ α').symm (.inl ⟨S, hS⟩)
          cast (congrArg (A κ θ) hα'.symm) u
      else
        fun _ => Classical.choice (nonempty_A hκ.pos α)
    else
      have hlim : Order.IsSuccLimit α := by
        rcases Ordinal.zero_or_succ_or_isSuccLimit α with h0 | ⟨α', hα'⟩ | hl
        · exact absurd h0 hα0
        · exact absurd ⟨α', hα'.symm⟩ hs
        · exact hl
      fun β =>
        if hcompat : ∀ (i j : α.ToType) (hij : i.toOrd.1 ≤ j.toOrd.1),
            f (κ := κ) (θ := θ) hij (rec j.toOrd.1 j.toOrd.2 β) = rec i.toOrd.1 i.toOrd.2 β then
          (limitEquiv κ θ hlim).symm ⟨fun i => rec i.toOrd.1 i.toOrd.2 β, hcompat⟩
        else
          Classical.choice (nonempty_A hκ.pos α)

private theorem qFun_zero (κ θ : Cardinal.{0}) (hκ : κ.IsRegular) (β : Ordinal.{0}) :
    qFun κ θ hκ 0 β = (zeroEquiv κ θ).symm PUnit.unit := by
  rw [qFun, WellFoundedLT.fix_eq, dite_eq_left_of_eq_true (eq_true rfl)]
  rfl

private theorem succ_ord_ne_zero (α' : Ordinal.{0}) : Order.succ α' ≠ 0 :=
  ne_of_gt (Order.bot_lt_succ α')

private theorem qFun_succ_set_lt {κ θ : Cardinal.{0}} (hκ : κ.IsRegular)
    {α' : Ordinal.{0}} (hακ : α' < κ.ord) (β : Ordinal.{0})
    (g : Ordinal.{0} → A κ θ α') :
    Cardinal.mk (Set.range fun i : (min β (Order.succ α')).ToType => g i.toOrd.1) <
      Cardinal.lift.{1, 0} κ := by
  have hlim_κ : Order.IsSuccLimit κ.ord := Cardinal.isSuccLimit_ord hκ.aleph0_le
  have hsucc_lt : Order.succ α' < κ.ord := hlim_κ.succ_lt hακ
  have hm_lt : min β (Order.succ α') < κ.ord :=
    lt_of_le_of_lt (min_le_right β (Order.succ α')) hsucc_lt
  have hm_card : Cardinal.mk (min β (Order.succ α')).ToType = (min β (Order.succ α')).card := by
    simp
  have h1 := Cardinal.mk_range_le_lift
    (f := fun i : (min β (Order.succ α')).ToType => g i.toOrd.1)
  rw [Cardinal.lift_uzero, hm_card] at h1
  exact lt_of_le_of_lt h1 (Cardinal.lift_lt.2 (Cardinal.lt_ord.1 hm_lt))

private theorem qFun_succ {κ θ : Cardinal.{0}} (hκ : κ.IsRegular)
    {α' : Ordinal.{0}} (hακ : α' < κ.ord) (β : Ordinal.{0}) :
    ∃ hS : Cardinal.mk (Set.range fun i : (min β (Order.succ α')).ToType =>
        qFun κ θ hκ α' i.toOrd.1) < Cardinal.lift.{1, 0} κ,
      succEquiv κ θ α' (qFun κ θ hκ (Order.succ α') β) =
        .inl ⟨Set.range fun i : (min β (Order.succ α')).ToType =>
          qFun κ θ hκ α' i.toOrd.1, hS⟩ := by
  have hS := qFun_succ_set_lt hκ hακ β (qFun κ θ hκ α')
  refine ⟨hS, ?_⟩
  rw [← Equiv.eq_symm_apply]
  have h0 : Order.succ α' ≠ 0 := succ_ord_ne_zero α'
  have hs : ∃ ξ, Order.succ α' = Order.succ ξ := ⟨α', rfl⟩
  have hch : Classical.choose hs = α' := Order.succ_injective (Classical.choose_spec hs).symm
  unfold qFun
  rw [WellFoundedLT.fix_eq, dite_eq_right_of_eq_false (eq_false h0),
      dite_eq_left_of_eq_true (eq_true hs)]
  have hrew : ∀ (ξ : Ordinal.{0}) (hξ : Order.succ α' = Order.succ ξ) (hξκ : ξ < κ.ord),
      ξ = α' →
      cast (congrArg (A κ θ) hξ.symm)
        ((succEquiv κ θ ξ).symm (.inl ⟨Set.range fun i : (min β (Order.succ ξ)).ToType =>
          qFun κ θ hκ ξ i.toOrd.1, qFun_succ_set_lt hκ hξκ β (qFun κ θ hκ ξ)⟩)) =
      (succEquiv κ θ α').symm (.inl ⟨Set.range fun i : (min β (Order.succ α')).ToType =>
        qFun κ θ hκ α' i.toOrd.1, hS⟩) := by
    rintro ξ hξ hξκ rfl
    rfl
  dsimp only
  rw [dite_eq_left_of_eq_true (eq_true (hch.symm ▸ hακ))]
  exact hrew (Classical.choose hs) (Classical.choose_spec hs) (hch.symm ▸ hακ) hch

private theorem qFun_limit {κ θ : Cardinal.{0}} (hκ : κ.IsRegular)
    {l : Ordinal.{0}} (hl : Order.IsSuccLimit l) (β : Ordinal.{0})
    (hcompat : ∀ (i j : l.ToType) (hij : i.toOrd.1 ≤ j.toOrd.1),
      f (κ := κ) (θ := θ) hij (qFun κ θ hκ j.toOrd.1 β) = qFun κ θ hκ i.toOrd.1 β) :
    qFun κ θ hκ l β =
      (limitEquiv κ θ hl).symm ⟨fun i => qFun κ θ hκ i.toOrd.1 β, hcompat⟩ := by
  have h0 : l ≠ 0 := hl.ne_bot
  have hns : ¬ ∃ α', l = Order.succ α' := by
    rintro ⟨α', rfl⟩
    exact Order.not_isSuccLimit_succ α' hl
  unfold qFun
  rw [WellFoundedLT.fix_eq, dite_eq_right_of_eq_false (eq_false h0),
      dite_eq_right_of_eq_false (eq_false hns)]
  dsimp only
  exact dite_eq_left_of_eq_true (eq_true hcompat)

private structure QProps (κ θ : Cardinal.{0}) (hκ : κ.IsRegular) (α : Ordinal.{0}) : Prop where
  eq_iff : ∀ β γ : Ordinal.{0}, qFun κ θ hκ α β = qFun κ θ hκ α γ ↔ min α β = min α γ
  proj : ∀ ⦃δ : Ordinal.{0}⦄ (hδ : δ ≤ α) (β : Ordinal.{0}),
    f (κ := κ) (θ := θ) hδ (qFun κ θ hκ α β) = qFun κ θ hκ δ β

private theorem set_image_Iio_min_eq {X : Type*} {α' : Ordinal.{0}} {g : Ordinal.{0} → X}
    (hg_trunc : ∀ γ : Ordinal.{0}, g γ = g (min α' γ)) (β : Ordinal.{0}) :
    (Set.range fun i : (min β (Order.succ α')).ToType => g i.toOrd.1) =
      { x | ∃ γ < β, g γ = x } := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.toOrd.1, lt_of_lt_of_le i.toOrd.2 (min_le_left β (Order.succ α')), rfl⟩
  · rintro ⟨γ, hγβ, rfl⟩
    by_cases hγ_lt : γ < Order.succ α'
    · have hmin : γ < min β (Order.succ α') := lt_min hγβ hγ_lt
      refine ⟨Ordinal.ToType.mk ⟨γ, hmin⟩, ?_⟩
      simp
    · have hle : Order.succ α' ≤ γ := le_of_not_gt hγ_lt
      have hα'_lt : α' < min β (Order.succ α') :=
        lt_min ((Order.lt_succ α').trans_le hle |>.trans hγβ) (Order.lt_succ α')
      refine ⟨Ordinal.ToType.mk ⟨α', hα'_lt⟩, ?_⟩
      have h1 : g α' = g (min α' α') := hg_trunc α'
      have h2 : g γ = g (min α' γ) := hg_trunc γ
      have hmin2 : min α' γ = α' := min_eq_left ((Order.le_succ α').trans hle)
      simp [h1, h2, hmin2]

private theorem min_succ_eq_min_succ_iff (α' β γ : Ordinal.{0}) :
    (∀ δ < β, ∃ ε < γ, min α' δ = min α' ε) ∧
      (∀ ε < γ, ∃ δ < β, min α' δ = min α' ε) ↔
    min (Order.succ α') β = min (Order.succ α') γ := by
  have hchar : ∀ ξ : Ordinal.{0},
      { n : Ordinal.{0} | ∃ δ < ξ, min α' δ = n } = Set.Iio (min (Order.succ α') ξ) := by
    intro ξ
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_Iio, lt_min_iff]
    constructor
    · rintro ⟨δ, hδξ, rfl⟩
      rcases le_or_gt δ α' with hδα' | hα'δ
      · exact ⟨lt_of_le_of_lt (min_le_right α' δ) (Order.lt_succ_iff.mpr hδα'),
          lt_of_le_of_lt (min_le_right α' δ) hδξ⟩
      · exact ⟨lt_of_le_of_lt (min_le_left α' δ) (Order.lt_succ α'),
          (min_le_left α' δ).trans_lt (hα'δ.trans hδξ)⟩
    · rintro ⟨hn_lt_s, hn_lt_ξ⟩
      refine ⟨n, hn_lt_ξ, ?_⟩
      exact min_eq_right (Order.lt_succ_iff.1 hn_lt_s)
  constructor
  · rintro ⟨h1, h2⟩
    have hset : { n : Ordinal.{0} | ∃ δ < β, min α' δ = n } =
        { n : Ordinal.{0} | ∃ ε < γ, min α' ε = n } := by
      ext n
      constructor
      · rintro ⟨δ, hδ, rfl⟩; obtain ⟨ε, hε, he⟩ := h1 δ hδ; exact ⟨ε, hε, he.symm⟩
      · rintro ⟨ε, hε, rfl⟩; obtain ⟨δ, hδ, he⟩ := h2 ε hε; exact ⟨δ, hδ, he⟩
    rw [hchar β, hchar γ] at hset
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : min (Order.succ α') β ∈ Set.Iio (min (Order.succ α') γ) := hlt
      rw [← hset] at this
      exact lt_irrefl _ (Set.mem_Iio.1 this)
    · have : min (Order.succ α') γ ∈ Set.Iio (min (Order.succ α') β) := hgt
      rw [hset] at this
      exact lt_irrefl _ (Set.mem_Iio.1 this)
  · intro heq
    have hset : { n : Ordinal.{0} | ∃ δ < β, min α' δ = n } =
        { n : Ordinal.{0} | ∃ ε < γ, min α' ε = n } := by
      rw [hchar β, hchar γ, heq]
    constructor
    · intro δ hδ
      have hm : min α' δ ∈ { n | ∃ δ < β, min α' δ = n } := ⟨δ, hδ, rfl⟩
      rw [hset] at hm
      rcases hm with ⟨ε, hε, he⟩
      exact ⟨ε, hε, he.symm⟩
    · intro ε hε
      have hm : min α' ε ∈ { n | ∃ ε < γ, min α' ε = n } := ⟨ε, hε, rfl⟩
      rw [← hset] at hm
      rcases hm with ⟨δ, hδ, he⟩
      exact ⟨δ, hδ, he⟩

private theorem qProps_all {κ θ : Cardinal.{0}} (hκ : κ.IsRegular) :
    ∀ ⦃α : Ordinal.{0}⦄, α ≤ κ.ord → QProps κ θ hκ α := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
    intro hακ
    rcases Ordinal.zero_or_succ_or_isSuccLimit α with rfl | ⟨α', rfl⟩ | hlim
    · refine ⟨?_, ?_⟩
      · intro β γ
        rw [qFun_zero, qFun_zero]
        simp
      · intro δ hδ β
        have h0 : δ = 0 := le_antisymm hδ bot_le
        subst h0
        simp
    · have hα'κ : α' < κ.ord := Order.succ_le_iff.1 hακ
      have ihα' := IH α' (Order.lt_succ α') hα'κ.le
      have htrunc : ∀ γ : Ordinal.{0}, qFun κ θ hκ α' γ = qFun κ θ hκ α' (min α' γ) := by
        intro γ
        rw [ihα'.eq_iff]
        simp
      have hsucc_set : ∀ β : Ordinal.{0},
          ∃ hS : Cardinal.mk ({ x | ∃ γ < β, qFun κ θ hκ α' γ = x }) < Cardinal.lift.{1, 0} κ,
            succEquiv κ θ α' (qFun κ θ hκ (Order.succ α') β) =
              .inl ⟨{ x | ∃ γ < β, qFun κ θ hκ α' γ = x }, hS⟩ := by
        intro β
        obtain ⟨hS, heq⟩ := qFun_succ hκ hα'κ β
        have hset := set_image_Iio_min_eq htrunc β
        refine ⟨hset ▸ hS, ?_⟩
        rw [heq]
        congr 1
        exact Subtype.ext hset
      have heq_iff : ∀ β γ : Ordinal.{0},
          qFun κ θ hκ (Order.succ α') β = qFun κ θ hκ (Order.succ α') γ ↔
            min (Order.succ α') β = min (Order.succ α') γ := by
        intro β γ
        obtain ⟨hSβ, hβ⟩ := hsucc_set β
        obtain ⟨hSγ, hγ⟩ := hsucc_set γ
        rw [← (succEquiv κ θ α').injective.eq_iff, hβ, hγ]
        constructor
        · intro hsum
          have hset : { x | ∃ δ < β, qFun κ θ hκ α' δ = x } =
              { x | ∃ ε < γ, qFun κ θ hκ α' ε = x } :=
            congrArg Subtype.val (Sum.inl.inj hsum)
          rw [← min_succ_eq_min_succ_iff α' β γ]
          constructor
          · intro δ hδ
            have hm : qFun κ θ hκ α' δ ∈ { x | ∃ ε < γ, qFun κ θ hκ α' ε = x } := by
              rw [← hset]; exact ⟨δ, hδ, rfl⟩
            rcases hm with ⟨ε, hε, he⟩
            exact ⟨ε, hε, (ihα'.eq_iff δ ε).1 he.symm⟩
          · intro ε hε
            have hm : qFun κ θ hκ α' ε ∈ { x | ∃ δ < β, qFun κ θ hκ α' δ = x } := by
              rw [hset]; exact ⟨ε, hε, rfl⟩
            rcases hm with ⟨δ, hδ, he⟩
            exact ⟨δ, hδ, (ihα'.eq_iff δ ε).1 he⟩
        · intro hmin
          have hcond := (min_succ_eq_min_succ_iff α' β γ).2 hmin
          congr 1
          apply Subtype.ext
          ext x
          constructor
          · rintro ⟨δ, hδ, rfl⟩
            obtain ⟨ε, hε, he⟩ := hcond.1 δ hδ
            exact ⟨ε, hε, ((ihα'.eq_iff δ ε).2 he).symm⟩
          · rintro ⟨ε, hε, rfl⟩
            obtain ⟨δ, hδ, he⟩ := hcond.2 ε hε
            exact ⟨δ, hδ, (ihα'.eq_iff δ ε).2 he⟩
      have hstep_proj : ∀ β : Ordinal.{0},
          f (κ := κ) (θ := θ) (Order.le_succ α') (qFun κ θ hκ (Order.succ α') β) =
            qFun κ θ hκ α' β := by
        intro β
        rcases Ordinal.zero_or_succ_or_isSuccLimit α' with rfl | ⟨ξ, rfl⟩ | hlim'
        · rw [qFun_zero]
          exact (zeroEquiv κ θ).injective rfl
        · have hξκ : ξ < κ.ord := (Order.lt_succ ξ).trans hα'κ
          have ihξ := IH ξ ((Order.lt_succ ξ).trans (Order.lt_succ _)) hξκ.le
          have htruncξ : ∀ γ : Ordinal.{0}, qFun κ θ hκ ξ γ = qFun κ θ hκ ξ (min ξ γ) := by
            intro γ; rw [ihξ.eq_iff]; simp
          apply (succEquiv κ θ ξ).injective
          change succEquiv κ θ ξ (f (Order.succ_le_succ (Order.le_succ ξ))
              (qFun κ θ hκ (Order.succ (Order.succ ξ)) β)) =
            succEquiv κ θ ξ (qFun κ θ hκ (Order.succ ξ) β)
          rw [succEquiv_f_succ (Order.le_succ ξ)]
          obtain ⟨hS1, h1⟩ := hsucc_set β
          obtain ⟨hS2, h2⟩ := qFun_succ hκ hξκ β
          have hsetξ := set_image_Iio_min_eq htruncξ β
          rw [h1, h2]
          dsimp only [G.map]
          congr 1
          apply Subtype.ext
          dsimp only
          rw [hsetξ]
          ext x
          simp only [Set.mem_image, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨y, ⟨γ, hγ, rfl⟩, rfl⟩
            exact ⟨γ, hγ, (ihα'.proj (Order.le_succ ξ) γ).symm⟩
          · rintro ⟨γ, hγ, rfl⟩
            exact ⟨qFun κ θ hκ (Order.succ ξ) γ, ⟨γ, hγ, rfl⟩, ihα'.proj (Order.le_succ ξ) γ⟩
        · apply (limitEquiv κ θ hlim').injective
          apply Subtype.ext
          funext δ
          rw [limitEquiv_proj, limitEquiv_proj]
          have hsuccδ : Order.succ δ.toOrd.1 < α' := hlim'.succ_lt δ.toOrd.2
          have hδκ : δ.toOrd.1 < κ.ord := δ.toOrd.2.trans hα'κ
          have ihδ := IH δ.toOrd.1 (δ.toOrd.2.trans (Order.lt_succ α')) hδκ.le
          have ihsδ := IH (Order.succ δ.toOrd.1) (hsuccδ.trans (Order.lt_succ α'))
            (hsuccδ.trans hα'κ).le
          rw [← f_comp δ.toOrd.2.le (Order.le_succ α'), ihα'.proj δ.toOrd.2.le β]
          have hcomp_l : f (δ.toOrd.2.le.trans (Order.le_succ α'))
              (qFun κ θ hκ (Order.succ α') β) =
              f (Order.le_succ δ.toOrd.1)
                (f (Order.succ_le_succ δ.toOrd.2.le) (qFun κ θ hκ (Order.succ α') β)) :=
            f_comp (Order.le_succ δ.toOrd.1) (Order.succ_le_succ δ.toOrd.2.le) _
          rw [hcomp_l]
          have hmid : f (Order.succ_le_succ δ.toOrd.2.le) (qFun κ θ hκ (Order.succ α') β) =
              qFun κ θ hκ (Order.succ δ.toOrd.1) β := by
            apply (succEquiv κ θ δ.toOrd.1).injective
            rw [succEquiv_f_succ δ.toOrd.2.le]
            obtain ⟨hS1, h1⟩ := hsucc_set β
            obtain ⟨hS2, h2⟩ := qFun_succ hκ hδκ β
            have htruncδ : ∀ γ, qFun κ θ hκ δ.toOrd.1 γ =
                qFun κ θ hκ δ.toOrd.1 (min δ.toOrd.1 γ) := by
              intro γ; rw [ihδ.eq_iff]; simp
            have hsetδ := set_image_Iio_min_eq htruncδ β
            rw [h1, h2]
            dsimp only [G.map]
            congr 1
            apply Subtype.ext
            dsimp only
            rw [hsetδ]
            ext x
            simp only [Set.mem_image, Set.mem_ofPred_eq]
            constructor
            · rintro ⟨y, ⟨γ, hγ, rfl⟩, rfl⟩
              exact ⟨γ, hγ, (ihα'.proj δ.toOrd.2.le γ).symm⟩
            · rintro ⟨γ, hγ, rfl⟩
              exact ⟨qFun κ θ hκ α' γ, ⟨γ, hγ, rfl⟩, ihα'.proj δ.toOrd.2.le γ⟩
          rw [hmid]
          exact ihsδ.proj (Order.le_succ δ.toOrd.1) β
      refine ⟨heq_iff, ?_⟩
      intro δ hδ β
      rcases eq_or_lt_of_le hδ with rfl | hlt
      · exact f_id _
      · have hδα' : δ ≤ α' := Order.lt_succ_iff.1 hlt
        rw [f_comp hδα' (Order.le_succ α'), hstep_proj β]
        exact ihα'.proj hδα' β
    · have hcompat : ∀ (β : Ordinal.{0}) (i j : α.ToType) (hij : i.toOrd.1 ≤ j.toOrd.1),
          f (κ := κ) (θ := θ) hij (qFun κ θ hκ j.toOrd.1 β) = qFun κ θ hκ i.toOrd.1 β := by
        intro β i j hij
        exact (IH j.toOrd.1 j.toOrd.2 (j.toOrd.2.le.trans hακ)).proj hij β
      have hproj : ∀ ⦃δ : Ordinal.{0}⦄ (hδ : δ ≤ α) (β : Ordinal.{0}),
          f (κ := κ) (θ := θ) hδ (qFun κ θ hκ α β) = qFun κ θ hκ δ β := by
        intro δ hδ β
        rcases eq_or_lt_of_le hδ with rfl | hlt
        · exact f_id _
        · rw [qFun_limit hκ hlim β (hcompat β)]
          let i : α.ToType := Ordinal.ToType.mk ⟨δ, hlt⟩
          have hi : i.toOrd.1 = δ := by simp [i]
          have h := congrArg (fun t : { t : (j : α.ToType) → A κ θ j.toOrd.1 // _ } => t.1 i)
            ((limitEquiv κ θ hlim).apply_symm_apply
              ⟨fun j => qFun κ θ hκ j.toOrd.1 β, hcompat β⟩)
          rw [limitEquiv_proj] at h
          have hcast : ∀ (d : Ordinal.{0}) (hd : d ≤ α), d = δ →
              f (κ := κ) (θ := θ) hd
                  ((limitEquiv κ θ hlim).symm ⟨fun j => qFun κ θ hκ j.toOrd.1 β, hcompat β⟩) =
                qFun κ θ hκ d β →
              f (κ := κ) (θ := θ) hδ
                  ((limitEquiv κ θ hlim).symm ⟨fun j => qFun κ θ hκ j.toOrd.1 β, hcompat β⟩) =
                qFun κ θ hκ δ β := by
            rintro d _ rfl h'; exact h'
          exact hcast i.toOrd.1 i.toOrd.2.le hi h
      refine ⟨?_, hproj⟩
      intro β γ
      constructor
      · intro heq
        have hpt : ∀ δ < α, min δ β = min δ γ := by
          intro δ hδ
          have ihδ := IH δ hδ (hδ.le.trans hακ)
          have h1 := hproj hδ.le β
          have h2 := hproj hδ.le γ
          rw [heq, h2] at h1
          exact (ihδ.eq_iff β γ).1 h1.symm
        by_contra hne
        suffices hbad : ∀ x y : Ordinal.{0}, min α x < min α y →
            (∀ δ < α, min δ x = min δ y) → False by
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact hbad β γ hlt hpt
          · exact hbad γ β hgt (fun δ hδ => (hpt δ hδ).symm)
        intro x y hlt hsame
        let μ := min α x
        have hμ_lt : μ < α := lt_of_lt_of_le hlt (min_le_left α y)
        have hsucc_lt : Order.succ μ < α := hlim.succ_lt hμ_lt
        have hm1 : μ = x := by
          rcases min_cases α x with ⟨he, _⟩ | ⟨he, _⟩
          · exact absurd (he ▸ hμ_lt) (lt_irrefl α)
          · exact he
        have hmy : Order.succ μ ≤ y := by
          have h1 : Order.succ μ ≤ min α y := Order.succ_le_iff.2 hlt
          exact h1.trans (min_le_right α y)
        have heq_s := hsame (Order.succ μ) hsucc_lt
        have hlhs : min (Order.succ μ) x = μ := by
          rw [← hm1]
          exact min_eq_right (Order.lt_succ μ).le
        have hrhs : min (Order.succ μ) y = Order.succ μ := min_eq_left hmy
        rw [hlhs, hrhs] at heq_s
        exact ne_of_lt (Order.lt_succ μ) heq_s
      · intro hmin
        apply (limitEquiv κ θ hlim).injective
        apply Subtype.ext
        funext i
        rw [limitEquiv_proj, limitEquiv_proj, hproj i.toOrd.2.le β, hproj i.toOrd.2.le γ]
        have ihi := IH i.toOrd.1 i.toOrd.2 (i.toOrd.2.le.trans hακ)
        rw [ihi.eq_iff]
        rcases le_or_gt α β with hαβ | hβα
        · have hαγ : α ≤ γ := by
            have := min_eq_left hαβ
            rw [this] at hmin
            exact hmin ▸ min_le_right α γ
          rw [min_eq_left (i.toOrd.2.le.trans hαβ), min_eq_left (i.toOrd.2.le.trans hαγ)]
        · have hβγ : β = γ := by
            have h1 : min α β = β := min_eq_right hβα.le
            rw [h1] at hmin
            by_contra hne
            rcases le_or_gt α γ with hαγ | hγα
            · have := min_eq_left hαγ
              rw [this] at hmin
              exact absurd (hmin ▸ hβα) (lt_irrefl α)
            · rw [min_eq_right hγα.le] at hmin
              exact hne hmin
          subst hβγ
          rfl

end Step1Construction

/-! ### Main Theorem of Step 1: Non-Surjectivity of `f_κ^{κ+1}` -/

private theorem hit_unique {κ θ : Cardinal.{0}} (hκ : κ.IsRegular)
    (s : A κ θ κ.ord) {γ₁ γ₂ : Ordinal.{0}}
    (hγ₁ : γ₁ < κ.ord) (hγ₂ : γ₂ < κ.ord) (hlt : γ₁ < γ₂)
    (hs₁ : f (κ := κ) (θ := θ) (Order.succ_le_iff.2 hγ₁) s =
      qFun κ θ hκ (Order.succ γ₁) γ₁)
    (hs₂ : f (κ := κ) (θ := θ) (Order.succ_le_iff.2 hγ₂) s =
      qFun κ θ hκ (Order.succ γ₂) γ₂) : False := by
  have h12 : Order.succ γ₁ ≤ Order.succ γ₂ := Order.succ_le_succ hlt.le
  have h2κ : Order.succ γ₂ ≤ κ.ord := Order.succ_le_iff.2 hγ₂
  have hq : qFun κ θ hκ (Order.succ γ₁) γ₁ = qFun κ θ hκ (Order.succ γ₁) γ₂ := by
    calc
      qFun κ θ hκ (Order.succ γ₁) γ₁
          = f (Order.succ_le_iff.2 hγ₁) s := hs₁.symm
      _ = f h12 (f h2κ s) := f_comp h12 h2κ s
      _ = f h12 (qFun κ θ hκ (Order.succ γ₂) γ₂) := by rw [hs₂]
      _ = qFun κ θ hκ (Order.succ γ₁) γ₂ := (qProps_all hκ h2κ).proj h12 γ₂
  have hmin := ((qProps_all hκ (Order.succ_le_iff.2 hγ₁)).eq_iff γ₁ γ₂).1 hq
  have hm1 : min (Order.succ γ₁) γ₁ = γ₁ := min_eq_right (Order.lt_succ γ₁).le
  have hm2 : min (Order.succ γ₁) γ₂ = Order.succ γ₁ :=
    min_eq_left (Order.succ_le_iff.2 hlt)
  rw [hm1, hm2] at hmin
  exact ne_of_lt (Order.lt_succ γ₁) hmin

theorem step1_not_surjective_kappa (κ θ : Cardinal.{0}) (hκ : κ.IsRegular) :
    ∃ b_κ : A κ θ κ.ord, ∀ x : A κ θ (Order.succ κ.ord),
      f (κ := κ) (θ := θ) (Order.le_succ κ.ord) x ≠ b_κ := by
  have hlim_κ : Order.IsSuccLimit κ.ord := Cardinal.isSuccLimit_ord hκ.aleph0_le
  let b_κ : A κ θ κ.ord := qFun κ θ hκ κ.ord κ.ord
  refine ⟨b_κ, fun x hx => ?_⟩
  cases hu : succEquiv κ θ κ.ord x with
  | inr p =>
      have h1_lt : Order.succ (0 : Ordinal.{0}) < κ.ord := hlim_κ.succ_lt hκ.ord_pos
      have h1_le : Order.succ (0 : Ordinal.{0}) ≤ κ.ord := h1_lt.le
      have h1_le_succ : Order.succ (0 : Ordinal.{0}) ≤ Order.succ κ.ord :=
        Order.succ_le_succ bot_le
      have hL : succEquiv κ θ 0 (f h1_le_succ x) =
          G.map (f (κ := κ) (θ := θ) bot_le) (succEquiv κ θ κ.ord x) :=
        succEquiv_f_succ bot_le x
      rw [hu] at hL
      have hcomp : f h1_le_succ x = f h1_le (f (Order.le_succ κ.ord) x) :=
        f_comp h1_le (Order.le_succ κ.ord) x
      rw [hcomp, hx] at hL
      have hq : f h1_le b_κ = qFun κ θ hκ (Order.succ 0) κ.ord :=
        (qProps_all hκ le_rfl).proj h1_le κ.ord
      rw [hq] at hL
      obtain ⟨_, hq_inl⟩ := qFun_succ hκ hκ.ord_pos κ.ord
      rw [hq_inl] at hL
      dsimp only [G.map] at hL
      cases hL
  | inl S_pair =>
      rcases S_pair with ⟨S, hS⟩
      let hitPred (s : ↥S) (γ : Ordinal.{0}) : Prop :=
        ∃ hγ : γ < κ.ord,
          f (κ := κ) (θ := θ) (Order.succ_le_iff.2 hγ) s.1 = qFun κ θ hκ (Order.succ γ) γ
      let badOrd : ↥S → Ordinal.{0} := fun s =>
        if h : ∃ γ, hitPred s γ then Classical.choose h else 0
      have hbad_lt : ∀ s : ↥S, badOrd s < κ.ord := by
        intro s
        dsimp only [badOrd]
        split_ifs with h
        · exact (Classical.choose_spec h).1
        · exact hκ.ord_pos
      have hbdd : BddAbove (Set.range badOrd) :=
        ⟨κ.ord, Set.forall_mem_range.2 fun s => (hbad_lt s).le⟩
      have hsup : (⨆ s : ↥S, badOrd s) < κ.ord := by
        apply Ordinal.lift_iSup_lt_of_lt_cof
        · simpa [hκ.cof_ord, hκ.lift.cof_ord] using hS
        · exact hbad_lt
      let α : Ordinal.{0} := Order.succ (⨆ s : ↥S, badOrd s)
      have hα_lt : α < κ.ord := hlim_κ.succ_lt hsup
      have hδ_lt : Order.succ α < κ.ord := hlim_κ.succ_lt hα_lt
      have hδ_le : Order.succ α ≤ κ.ord := hδ_lt.le
      have hno_hit : ∀ s ∈ S,
          f (κ := κ) (θ := θ) hδ_le s ≠ qFun κ θ hκ (Order.succ α) α := by
        intro s hs hhit
        have hex : ∃ γ, hitPred ⟨s, hs⟩ γ := ⟨α, hα_lt, hhit⟩
        let γ₀ := Classical.choose hex
        have hγ₀_spec := Classical.choose_spec hex
        have hbad_eq : badOrd ⟨s, hs⟩ = γ₀ := by
          dsimp [badOrd]
          rw [dite_eq_left_of_eq_true (eq_true hex)]
        have hγ₀_le_sup : γ₀ ≤ ⨆ t : ↥S, badOrd t := by
          rw [← hbad_eq]
          exact le_ciSup hbdd ⟨s, hs⟩
        have hγ₀_lt_α : γ₀ < α := lt_of_le_of_lt hγ₀_le_sup (Order.lt_succ _)
        exact hit_unique hκ s hγ₀_spec.1 hα_lt hγ₀_lt_α hγ₀_spec.2 hhit
      have hδ2_lt : Order.succ (Order.succ α) < κ.ord := hlim_κ.succ_lt hδ_lt
      have hδ2_le : Order.succ (Order.succ α) ≤ κ.ord := hδ2_lt.le
      have hδ2_le_succ : Order.succ (Order.succ α) ≤ Order.succ κ.ord :=
        Order.succ_le_succ hδ_le
      have hL : succEquiv κ θ (Order.succ α) (f hδ2_le_succ x) =
          G.map (f (κ := κ) (θ := θ) hδ_le) (succEquiv κ θ κ.ord x) :=
        succEquiv_f_succ hδ_le x
      rw [hu] at hL
      have hcomp : f hδ2_le_succ x = f hδ2_le (f (Order.le_succ κ.ord) x) :=
        f_comp hδ2_le (Order.le_succ κ.ord) x
      rw [hcomp, hx] at hL
      have hq : f hδ2_le b_κ = qFun κ θ hκ (Order.succ (Order.succ α)) κ.ord :=
        (qProps_all hκ le_rfl).proj hδ2_le κ.ord
      rw [hq] at hL
      obtain ⟨_, hq_inl⟩ := qFun_succ hκ hδ_lt κ.ord
      rw [hq_inl] at hL
      dsimp only [G.map] at hL
      have him : f (κ := κ) (θ := θ) hδ_le '' S =
          Set.range fun i : (min κ.ord (Order.succ (Order.succ α))).ToType =>
            qFun κ θ hκ (Order.succ α) i.toOrd.1 :=
        (congrArg Subtype.val (Sum.inl.inj hL)).symm
      have hmem : qFun κ θ hκ (Order.succ α) α ∈ f (κ := κ) (θ := θ) hδ_le '' S := by
        rw [him]
        refine ⟨Ordinal.ToType.mk ⟨α, lt_min hα_lt ((Order.lt_succ α).trans (Order.lt_succ _))⟩, ?_⟩
        simp
      rcases hmem with ⟨s, hsS, hseq⟩
      exact hno_hit s hsS hseq

end TerminalSeq
