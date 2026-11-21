import TerminalSeq.Abstract.FinalSequence

/-!
# General Stabilization, Constant-Coalgebra Cone (Lemma 1.4), and Tail Monicity

For any `F : SetFunctor`:
1. `StabilizesAt F γ` (`Bijective (f_{γ}^{γ+1})`) and `Stabilizes F γ` (minimal stabilizing ordinal).
2. `stabilizesAt_upward`: stabilization persists to all larger ordinals.
3. `IsCone` / `coneElem` (Lemma 1.4): given `c : A F 1`, constructs a unique compatible cone
   `coneElem F c α : A F α` with `coneElem F c 1 = c` and `f h (coneElem F c β) = coneElem F c α`,
   inducing split sections `A F 1 → A F α` for all `1 ≤ α`.
4. `stab_zero_of_subsingleton`, `stab_one_of_isEmpty`: characterization at `0` and `1`.
5. `tail_monic_of_accessible`: for any regular `κ` and `κ`-accessible `F` with `Nonempty (A F 1)`,
   every tail transition `f (h : α ≤ β)` with `κ.ord ≤ α ≤ β` is injective.
-/

noncomputable section

open Classical Ordinal Cardinal

namespace TerminalSeq.Abstract

section StabilizationDefs

/-- The terminal sequence of `F` stabilizes at `γ` iff `f_γ^{γ+1}` is bijective. -/
def StabilizesAt (F : SetFunctor) (γ : Ordinal.{0}) : Prop :=
  Function.Bijective (f (F := F) (Order.le_succ γ))

/-- `γ` is the exact stabilization ordinal of `F`. -/
def Stabilizes (F : SetFunctor) (γ : Ordinal.{0}) : Prop :=
  StabilizesAt F γ ∧ ∀ δ < γ, ¬ StabilizesAt F δ

private theorem bijective_of_comp_left {X Y Z : Type 1} {g : X → Y} {k : Y → Z}
    (hkg : Function.Bijective (k ∘ g)) (hk : Function.Bijective k) :
    Function.Bijective g := by
  have h : g = (Equiv.ofBijective k hk).symm ∘ (k ∘ g) := by
    funext x
    exact ((Equiv.ofBijective k hk).left_inv (g x)).symm
  rw [h]
  exact (Equiv.ofBijective k hk).symm.bijective.comp hkg

theorem stabilizesAt_upward {F : SetFunctor} {δ : Ordinal.{0}} (hδ : StabilizesAt F δ) :
    ∀ {γ : Ordinal.{0}} (hδγ : δ ≤ γ),
      Function.Bijective (f (F := F) hδγ) ∧ StabilizesAt F γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
    intro hδγ
    rcases eq_or_lt_of_le hδγ with rfl | hlt
    · have hid : f (F := F) (le_refl δ) = id := funext f_id
      rw [hid]
      exact ⟨Function.bijective_id, hδ⟩
    · rcases Ordinal.zero_or_succ_or_isSuccLimit γ with rfl | ⟨γ', rfl⟩ | hlim
      · exact absurd hlt (not_lt_of_ge bot_le)
      · have hδγ' : δ ≤ γ' := Order.lt_succ_iff.1 hlt
        obtain ⟨hbij_γ', _⟩ := IH γ' (Order.lt_succ γ') hδγ'
        have hbij_succ : Function.Bijective
            (f (F := F) (Order.succ_le_succ hδγ')) := by
          have hcomm : F.map (f (F := F) hδγ') ∘ (succEquiv F γ') =
              (succEquiv F δ) ∘ f (F := F) (Order.succ_le_succ hδγ') := by
            funext x
            exact (succEquiv_f_succ hδγ' x).symm
          have hF : Function.Bijective
              ((succEquiv F δ) ∘ f (F := F) (Order.succ_le_succ hδγ')) := by
            rw [← hcomm]
            exact (F.map_bijective hbij_γ').comp (succEquiv F γ').bijective
          exact bijective_of_comp_left hF (succEquiv F δ).bijective
        have h_eq1 : (f (F := F) (Order.le_succ δ) ∘
            f (F := F) (Order.succ_le_succ hδγ')) =
            f (F := F) (hδγ'.trans (Order.le_succ γ')) := by
          funext x
          exact (f_comp (Order.le_succ δ) (Order.succ_le_succ hδγ') x).symm
        have hbij_tot : Function.Bijective (f (F := F) (hδγ'.trans (Order.le_succ γ'))) := by
          rw [← h_eq1]
          exact hδ.comp hbij_succ
        have hstep : Function.Bijective (f (F := F) (Order.le_succ γ')) := by
          have h_eq2 : (f (F := F) hδγ' ∘ f (F := F) (Order.le_succ γ')) =
              f (F := F) (hδγ'.trans (Order.le_succ γ')) := by
            funext x
            exact (f_comp hδγ' (Order.le_succ γ') x).symm
          have hcomp : Function.Bijective (f (F := F) hδγ' ∘ f (F := F) (Order.le_succ γ')) := by
            rw [h_eq2]; exact hbij_tot
          exact bijective_of_comp_left hcomp hbij_γ'
        have hstep2 : StabilizesAt F (Order.succ γ') := by
          unfold StabilizesAt
          have hcomm : F.map (f (F := F) (Order.le_succ γ')) ∘ (succEquiv F (Order.succ γ')) =
              (succEquiv F γ') ∘ f (F := F) (Order.le_succ (Order.succ γ')) := by
            funext x
            exact (succEquiv_f_succ (Order.le_succ γ') x).symm
          have hF : Function.Bijective
              ((succEquiv F γ') ∘ f (F := F) (Order.le_succ (Order.succ γ'))) := by
            rw [← hcomm]
            exact (F.map_bijective hstep).comp (succEquiv F (Order.succ γ')).bijective
          exact bijective_of_comp_left hF (succEquiv F γ').bijective
        exact ⟨hbij_tot, hstep2⟩
      · have hbij_lim : Function.Bijective (f (F := F) hδγ) := by
          constructor
          · intro x₁ x₂ hx
            apply (limitEquiv F hlim).injective
            apply Subtype.ext
            funext i
            rw [limitEquiv_proj, limitEquiv_proj]
            rcases le_or_gt i.toOrd.1 δ with hiδ | hδi
            · rw [f_comp hiδ hδγ x₁, f_comp hiδ hδγ x₂, hx]
            · exact (IH i.toOrd.1 i.toOrd.2 hδi.le).1.1 (by
                rw [← f_comp hδi.le i.toOrd.2.le x₁, ← f_comp hδi.le i.toOrd.2.le x₂, hx])
          · intro x
            let liftElem (i : γ.ToType) : A F i.toOrd.1 :=
              if hi : δ ≤ i.toOrd.1 then
                (Equiv.ofBijective _ (IH i.toOrd.1 i.toOrd.2 hi).1).symm x
              else
                f (F := F) (lt_of_not_ge hi).le x
            have hcompat : ∀ (i j : γ.ToType) (hij : i.toOrd.1 ≤ j.toOrd.1),
                f (F := F) hij (liftElem j) = liftElem i := by
              intro i j hij
              by_cases hi : δ ≤ i.toOrd.1
              · have hj : δ ≤ j.toOrd.1 := hi.trans hij
                dsimp only [liftElem]
                rw [dite_eq_left_of_eq_true (eq_true hj), dite_eq_left_of_eq_true (eq_true hi)]
                apply (IH i.toOrd.1 i.toOrd.2 hi).1.1
                rw [← f_comp hi hij]
                have hfx : f (F := F) hj ((Equiv.ofBijective _ (IH j.toOrd.1 j.toOrd.2 hj).1).symm x) = x :=
                  (Equiv.ofBijective _ (IH j.toOrd.1 j.toOrd.2 hj).1).apply_symm_apply x
                have hfy : f (F := F) hi ((Equiv.ofBijective _ (IH i.toOrd.1 i.toOrd.2 hi).1).symm x) = x :=
                  (Equiv.ofBijective _ (IH i.toOrd.1 i.toOrd.2 hi).1).apply_symm_apply x
                exact hfx.trans hfy.symm
              · have hi_lt : i.toOrd.1 < δ := lt_of_not_ge hi
                dsimp only [liftElem]
                rw [dite_eq_right_of_eq_false (eq_false hi)]
                by_cases hj : δ ≤ j.toOrd.1
                · rw [dite_eq_left_of_eq_true (eq_true hj), f_comp hi_lt.le hj]
                  have hfx : f (F := F) hj ((Equiv.ofBijective _ (IH j.toOrd.1 j.toOrd.2 hj).1).symm x) = x :=
                    (Equiv.ofBijective _ (IH j.toOrd.1 j.toOrd.2 hj).1).apply_symm_apply x
                  rw [hfx]
                · have hj_lt : j.toOrd.1 < δ := lt_of_not_ge hj
                  rw [dite_eq_right_of_eq_false (eq_false hj)]
                  exact (f_comp hij hj_lt.le x).symm
            let y : A F γ := (limitEquiv F hlim).symm ⟨liftElem, hcompat⟩
            refine ⟨y, ?_⟩
            let i₀ : γ.ToType := Ordinal.ToType.mk ⟨δ, hlt⟩
            have hi₀ : i₀.toOrd.1 = δ := by simp [i₀]
            have hproj := congrArg
              (fun t : { t : (j : γ.ToType) → A F j.toOrd.1 // _ } => t.1 i₀)
              ((limitEquiv F hlim).apply_symm_apply ⟨liftElem, hcompat⟩)
            rw [limitEquiv_proj] at hproj
            have hlhs : f (F := F) hδγ y =
                cast (congrArg (A F) hi₀) (liftElem i₀) := by
              have hc : ∀ (d : Ordinal.{0}) (hd : d ≤ γ) (heq : d = δ) (z : A F d),
                  f (F := F) hd y = z →
                  f (F := F) hδγ y = cast (congrArg (A F) heq) z := by
                rintro d _ rfl z rfl; rfl
              exact hc i₀.toOrd.1 i₀.toOrd.2.le hi₀ (liftElem i₀) hproj
            rw [hlhs]
            have hle_i₀ : δ ≤ i₀.toOrd.1 := hi₀.symm.le
            dsimp only [liftElem]
            rw [dite_eq_left_of_eq_true (eq_true hle_i₀)]
            have hid_bij : ∀ z : A F i₀.toOrd.1,
                cast (congrArg (A F) hi₀) z = f (F := F) hle_i₀ z := by
              intro z
              have hf : ∀ (d : Ordinal.{0}) (hd : δ ≤ d) (heq : d = δ) (w : A F d),
                  cast (congrArg (A F) heq) w = f (F := F) hd w := by
                rintro d _ rfl w; exact (f_id w).symm
              exact hf i₀.toOrd.1 hle_i₀ hi₀ z
            rw [hid_bij]
            exact (Equiv.ofBijective _ (IH i₀.toOrd.1 i₀.toOrd.2 hle_i₀).1).apply_symm_apply x
        have hstab_lim : StabilizesAt F γ := by
          unfold StabilizesAt
          have hsδ : Order.succ δ < γ := hlim.succ_lt hlt
          have hbij_succ_δ : Function.Bijective (f (F := F) (Order.succ_le_succ hδγ)) := by
            have hcomm : F.map (f (F := F) hδγ) ∘ (succEquiv F γ) =
                (succEquiv F δ) ∘ f (F := F) (Order.succ_le_succ hδγ) := by
              funext x; exact (succEquiv_f_succ hδγ x).symm
            have hF : Function.Bijective
                ((succEquiv F δ) ∘ f (F := F) (Order.succ_le_succ hδγ)) := by
              rw [← hcomm]
              exact (F.map_bijective hbij_lim).comp (succEquiv F γ).bijective
            exact bijective_of_comp_left hF (succEquiv F δ).bijective
          have hcomp1 : (f (F := F) (Order.le_succ δ) ∘
              f (F := F) hsδ.le) = f (F := F) hδγ := by
            funext x; exact (f_comp (Order.le_succ δ) hsδ.le x).symm
          have hbij_tot : Function.Bijective (f (F := F) hsδ.le) :=
            bijective_of_comp_left (by rw [hcomp1]; exact hbij_lim) hδ
          have hcomp2 : (f (F := F) hsδ.le ∘ f (F := F) (Order.le_succ γ)) =
              f (F := F) (Order.succ_le_succ hδγ) := by
            funext x; exact (f_comp hsδ.le (Order.le_succ γ) x).symm
          exact bijective_of_comp_left (by rw [hcomp2]; exact hbij_succ_δ) hbij_tot
        exact ⟨hbij_lim, hstab_lim⟩

/-- Least stabilizing ordinal theorem from any witness `StabilizesAt F γ₀`. -/
theorem exists_stabilizes_of_stabilizesAt {F : SetFunctor} {γ₀ : Ordinal.{0}}
    (hγ₀ : StabilizesAt F γ₀) : ∃ γ ≤ γ₀, Stabilizes F γ := by
  let S : Set Ordinal.{0} := { γ | StabilizesAt F γ }
  have hne : S.Nonempty := ⟨γ₀, hγ₀⟩
  let γ := sInf S
  have hγ_mem : StabilizesAt F γ := csInf_mem hne
  have hγ_le : γ ≤ γ₀ := csInf_le (OrderBot.bddBelow S) hγ₀
  refine ⟨γ, hγ_le, hγ_mem, fun δ hδ => ?_⟩
  exact fun hmem => absurd (csInf_le (OrderBot.bddBelow S) hmem) (not_le_of_gt hδ)

/-- Uniqueness of the exact stabilization ordinal. -/
theorem stabilizes_unique {F : SetFunctor} {γ₁ γ₂ : Ordinal.{0}}
    (h₁ : Stabilizes F γ₁) (h₂ : Stabilizes F γ₂) : γ₁ = γ₂ := by
  rcases lt_trichotomy γ₁ γ₂ with hlt | rfl | hgt
  · exact absurd h₁.1 (h₂.2 γ₁ hlt)
  · rfl
  · exact absurd h₂.1 (h₁.2 γ₂ hgt)

end StabilizationDefs

section ConstantCone

instance instSubsingletonA0 (F : SetFunctor) : Subsingleton (A F 0) :=
  (zeroEquiv F).subsingleton

instance instNonemptyA0 (F : SetFunctor) : Nonempty (A F 0) :=
  ⟨(zeroEquiv F).symm PUnit.unit⟩

private theorem succ_zero_ord : Order.succ (0 : Ordinal.{0}) = 1 := by simp

private theorem f_le_of_eq {F : SetFunctor} {α β : Ordinal.{0}} (hab : α = β) (x : A F β) :
    f (F := F) (le_of_eq hab) x = cast (congrArg (A F) hab.symm) x := by
  subst hab
  exact f_id x

/-- Characterization of an element `x : A F α` generated by the constant coalgebra `1 →^{c} F(1)`. -/
def IsCone (F : SetFunctor) (c : A F 1) (α : Ordinal.{0}) (x : A F α) : Prop :=
  ∀ (δ : Ordinal.{0}) (h : Order.succ δ ≤ α),
    succEquiv F δ (f h x) =
      F.map (fun _ : A F 0 => f ((Order.lt_succ δ).le.trans h) x)
        (succEquiv F 0 (cast (congrArg (A F) succ_zero_ord.symm) c))

private theorem isCone_proj {F : SetFunctor} {c : A F 1} {α β : Ordinal.{0}} (hαβ : α ≤ β)
    {x : A F β} (hx : IsCone F c β x) : IsCone F c α (f hαβ x) := by
  intro δ hδ
  rw [← f_comp hδ hαβ x, ← f_comp ((Order.lt_succ δ).le.trans hδ) hαβ x]
  exact hx δ (hδ.trans hαβ)

private theorem cone_unique {F : SetFunctor} {c : A F 1} :
    ∀ {α : Ordinal.{0}} {x y : A F α}, IsCone F c α x → IsCone F c α y → x = y := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
    intro x y hx hy
    rcases Ordinal.zero_or_succ_or_isSuccLimit α with rfl | ⟨α', rfl⟩ | hl
    · exact Subsingleton.elim x y
    · have hproj : f (F := F) (Order.le_succ α') x = f (F := F) (Order.le_succ α') y :=
        IH α' (Order.lt_succ α')
          (isCone_proj (Order.le_succ α') hx) (isCone_proj (Order.le_succ α') hy)
      have hx' := hx α' le_rfl
      have hy' := hy α' le_rfl
      rw [f_id] at hx' hy'
      apply (succEquiv F α').injective
      rw [hx', hy', hproj]
    · apply (limitEquiv F hl).injective
      apply Subtype.ext
      funext i
      rw [limitEquiv_proj, limitEquiv_proj]
      exact IH i.toOrd.1 i.toOrd.2
        (isCone_proj i.toOrd.2.le hx) (isCone_proj i.toOrd.2.le hy)

private theorem exists_cone_elem {F : SetFunctor} (c : A F 1) :
    ∀ α : Ordinal.{0}, ∃ x : A F α, IsCone F c α x := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
    rcases Ordinal.zero_or_succ_or_isSuccLimit α with rfl | ⟨α', rfl⟩ | hl
    · refine ⟨Classical.arbitrary _, fun δ hδ => ?_⟩
      exact absurd hδ (not_le_of_gt (bot_le.trans_lt (Order.lt_succ δ)))
    · obtain ⟨x', hx'⟩ := IH α' (Order.lt_succ α')
      let x : A F (Order.succ α') :=
        (succEquiv F α').symm
          (F.map (fun _ : A F 0 => x') (succEquiv F 0 (cast (congrArg (A F) succ_zero_ord.symm) c)))
      have hagree : ∀ (β : Ordinal.{0}) (hβ : β ≤ α'),
          f (F := F) (hβ.trans (Order.le_succ α')) x = f (F := F) hβ x' := by
        intro β
        induction β using WellFoundedLT.induction with
        | ind β IHβ =>
          intro hβ
          rcases Ordinal.zero_or_succ_or_isSuccLimit β with rfl | ⟨δ, rfl⟩ | hlim
          · exact Subsingleton.elim _ _
          · apply (succEquiv F δ).injective
            have hδ : δ ≤ α' := (Order.lt_succ δ).le.trans hβ
            have h_eq : hβ.trans (Order.le_succ α') = Order.succ_le_succ hδ := rfl
            rw [h_eq, succEquiv_f_succ hδ x]
            dsimp only [x]
            rw [Equiv.apply_symm_apply, ← F.map_comp_apply]
            exact (hx' δ hβ).symm
          · apply (limitEquiv F hlim).injective
            apply Subtype.ext
            funext i
            rw [limitEquiv_proj, limitEquiv_proj]
            rw [← f_comp i.toOrd.2.le (hβ.trans (Order.le_succ α')) x,
                ← f_comp i.toOrd.2.le hβ x']
            exact IHβ i.toOrd.1 i.toOrd.2 (i.toOrd.2.le.trans hβ)
      have hstep : f (F := F) (Order.le_succ α') x = x' := by
        simpa using hagree α' le_rfl
      refine ⟨x, fun δ hδ => ?_⟩
      rcases eq_or_lt_of_le (Order.succ_le_succ_iff.1 hδ) with rfl | hlt
      · rw [f_id, hstep]
        dsimp only [x]
        exact (succEquiv F δ).apply_symm_apply _
      · have hδ' : Order.succ δ ≤ α' := Order.succ_le_iff.2 hlt
        rw [f_comp hδ' (Order.le_succ α') x, hstep]
        rw [f_comp ((Order.lt_succ δ).le.trans hδ') (Order.le_succ α') x, hstep]
        exact hx' δ hδ'
    · let s : (i : α.ToType) → A F i.toOrd.1 := fun i => Classical.choose (IH i.toOrd.1 i.toOrd.2)
      have hs : ∀ i : α.ToType, IsCone F c i.toOrd.1 (s i) :=
        fun i => Classical.choose_spec (IH i.toOrd.1 i.toOrd.2)
      have hcompat : ∀ (i j : α.ToType) (hij : i.toOrd.1 ≤ j.toOrd.1),
          f (F := F) hij (s j) = s i :=
        fun i j hij => cone_unique (isCone_proj hij (hs j)) (hs i)
      let x : A F α := (limitEquiv F hl).symm ⟨s, hcompat⟩
      refine ⟨x, fun δ hδ => ?_⟩
      have hδ_lt : Order.succ δ < α := lt_of_le_of_ne hδ fun heq =>
        absurd hl (heq ▸ Order.not_isSuccLimit_succ δ)
      let iδ : α.ToType := Ordinal.ToType.mk ⟨Order.succ δ, hδ_lt⟩
      have hiδ : iδ.toOrd.1 = Order.succ δ := by simp [iδ]
      have hp := congrArg (fun t : { t : (j : α.ToType) → A F j.toOrd.1 // _ } => t.1 iδ)
        ((limitEquiv F hl).apply_symm_apply ⟨s, hcompat⟩)
      rw [limitEquiv_proj] at hp
      have hfx : f (F := F) hδ x = cast (congrArg (A F) hiδ) (s iδ) := by
        have hrew : ∀ (o : Ordinal.{0}) (ho : o ≤ α) (heq : o = Order.succ δ) (z : A F o),
            f (F := F) ho x = z → f (F := F) hδ x = cast (congrArg (A F) heq) z := by
          rintro o _ rfl z rfl; rfl
        exact hrew iδ.toOrd.1 iδ.toOrd.2.le hiδ (s iδ) hp
      have h_cone_s : IsCone F c (Order.succ δ) (cast (congrArg (A F) hiδ) (s iδ)) := by
        have hrew : ∀ (o : Ordinal.{0}) (heq : o = Order.succ δ) (z : A F o),
            IsCone F c o z → IsCone F c (Order.succ δ) (cast (congrArg (A F) heq) z) := by
          rintro o rfl z hz; exact hz
        exact hrew iδ.toOrd.1 hiδ (s iδ) (hs iδ)
      have hcs := h_cone_s δ le_rfl
      rw [f_id] at hcs
      rw [hfx, hcs]
      simp_rw [f_comp (Order.lt_succ δ).le hδ x, hfx]

/-- Lemma 1.4: section map `coneMap F α : A F 1 → A F α` for `1 ≤ α`. -/
def coneMap (F : SetFunctor) (α : Ordinal.{0}) (c : A F 1) : A F α :=
  Classical.choose (exists_cone_elem c α)

theorem coneMap_spec {F : SetFunctor} {α : Ordinal.{0}} (c : A F 1) :
    IsCone F c α (coneMap F α c) :=
  Classical.choose_spec (exists_cone_elem c α)

theorem coneMap_compat {F : SetFunctor} {α β : Ordinal.{0}} (hαβ : α ≤ β) (c : A F 1) :
    f (F := F) hαβ (coneMap F β c) = coneMap F α c :=
  cone_unique (isCone_proj hαβ (coneMap_spec c)) (coneMap_spec c)

theorem coneMap_one {F : SetFunctor} (c : A F 1) : coneMap F 1 c = c := by
  have h1 := coneMap_spec (F := F) (α := 1) c 0 (le_of_eq succ_zero_ord)
  rw [f_le_of_eq succ_zero_ord] at h1
  have hzero :
      (fun _ : A F 0 => f (F := F) ((Order.lt_succ (0 : Ordinal.{0})).le.trans (le_of_eq succ_zero_ord)) (coneMap F 1 c)) = id :=
    funext fun _ => Subsingleton.elim _ _
  rw [hzero, F.map_id_apply] at h1
  have hcast := (succEquiv F 0).injective h1
  simpa using congrArg (cast (congrArg (A F) succ_zero_ord)) hcast

/-- Lemma 1.4 consequence: for every `1 ≤ α`, `f_1^α` has a right inverse `coneMap F α`. -/
theorem coneMap_rightInverse {F : SetFunctor} {α : Ordinal.{0}} (h1α : 1 ≤ α) :
    f (F := F) h1α ∘ coneMap F α = id := by
  funext c
  exact (coneMap_compat h1α c).trans (coneMap_one c)

theorem nonempty_of_nonempty_one {F : SetFunctor} [Nonempty (A F 1)] (α : Ordinal.{0}) :
    Nonempty (A F α) :=
  ⟨coneMap F α (Classical.arbitrary _)⟩

theorem card_one_le_of_one_le {F : SetFunctor} {α : Ordinal.{0}} (h1α : 1 ≤ α) :
    Cardinal.mk (A F 1) ≤ Cardinal.mk (A F α) := by
  apply Cardinal.mk_le_of_injective (f := coneMap F α)
  intro c₁ c₂ heq
  have := congrArg (f (F := F) h1α) heq
  simpa [coneMap_compat h1α, coneMap_one] using this

end ConstantCone

section BoundaryCases

/-- If `|A F 1| = 1`, then `F` already stabilizes at `0`. -/
theorem stabilizesAt_zero_of_subsingleton {F : SetFunctor} [Subsingleton (A F 1)] [Nonempty (A F 1)] :
    StabilizesAt F 0 := by
  unfold StabilizesAt
  constructor
  · intro x y _
    have : Subsingleton (A F (Order.succ 0)) := (Equiv.cast (congrArg (A F) succ_zero_ord)).subsingleton
    exact Subsingleton.elim x y
  · intro y
    refine ⟨cast (congrArg (A F) succ_zero_ord.symm) (Classical.arbitrary (A F 1)), Subsingleton.elim _ _⟩

/-- If `A F 1` is empty, then `A F 2` is also empty and `F` stabilizes at `1`. -/
theorem stabilizes_one_of_isEmpty {F : SetFunctor} [IsEmpty (A F 1)] :
    Stabilizes F 1 := by
  have his2 : IsEmpty (A F (Order.succ 1)) :=
    ⟨fun x => IsEmpty.false (f (F := F) (Order.le_succ 1) x)⟩
  have h1 : StabilizesAt F 1 := by
    unfold StabilizesAt
    exact ⟨fun x => isEmptyElim x, fun y => isEmptyElim y⟩
  refine ⟨h1, fun δ hδ => ?_⟩
  have hδ0 : δ = 0 := le_antisymm (Order.lt_succ_iff.1 (by simpa using hδ)) bot_le
  subst hδ0
  intro hstab0
  have hsurj : Function.Surjective (f (F := F) (Order.le_succ 0)) := hstab0.2
  obtain ⟨x, _⟩ := hsurj (Classical.arbitrary (A F 0))
  exact IsEmpty.false (cast (by simp) x : A F 1)

end BoundaryCases

section AccessibleTailMonic

private theorem exists_proj_ne_of_ne {F : SetFunctor} {l : Ordinal.{0}}
    (hl : Order.IsSuccLimit l) {x y : A F l} (hxy : x ≠ y) :
    ∃ (α : Ordinal.{0}) (hα : α < l), f (F := F) hα.le x ≠ f (F := F) hα.le y := by
  by_contra hall
  push Not at hall
  apply hxy
  apply (limitEquiv F hl).injective
  apply Subtype.ext
  funext i
  rw [limitEquiv_proj, limitEquiv_proj]
  exact hall i.toOrd.1 i.toOrd.2

private theorem exists_proj_injective_on_lt {F : SetFunctor} {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (S : Set (A F κ.ord)) (hS : Cardinal.mk S < Cardinal.lift.{1, 0} κ) :
    ∃ (α : Ordinal.{0}) (hα : α < κ.ord),
      ∀ a ∈ S, ∀ b ∈ S, f (F := F) hα.le a = f (F := F) hα.le b → a = b := by
  have hlim : Order.IsSuccLimit κ.ord := Cardinal.isSuccLimit_ord hκ.aleph0_le
  let exists_diff {p : ↥S × ↥S} (h : p.1.1 ≠ p.2.1) := exists_proj_ne_of_ne hlim h
  let diffPair : (p : ↥S × ↥S) → Ordinal.{0} := fun p =>
    if h : p.1.1 ≠ p.2.1 then Classical.choose (exists_diff h) else 0
  have hdiff_lt : ∀ p : ↥S × ↥S, diffPair p < κ.ord := by
    intro p
    by_cases h : p.1.1 ≠ p.2.1
    · dsimp only [diffPair]; rw [dite_eq_left_of_eq_true (eq_true h)]
      exact (Classical.choose_spec (exists_diff h)).1
    · dsimp only [diffPair]; rw [dite_eq_right_of_eq_false (eq_false h)]
      exact hκ.ord_pos
  have hpair_card : Cardinal.mk (↥S × ↥S) < Cardinal.lift.{1, 0} κ := by
    rw [Cardinal.mk_prod, Cardinal.lift_id]
    have hinf : Cardinal.aleph0 ≤ Cardinal.lift.{1, 0} κ := hκ.lift.aleph0_le
    exact Cardinal.mul_lt_of_lt hinf hS hS
  have hsup : (⨆ p : ↥S × ↥S, diffPair p) < κ.ord := by
    apply Ordinal.lift_iSup_lt_of_lt_cof
    · rw [Cardinal.lift_uzero, ← Ordinal.lift_cof, hκ.cof_ord]; exact hpair_card
    · exact hdiff_lt
  refine ⟨⨆ p : ↥S × ↥S, diffPair p, hsup, fun a ha b hb heq => ?_⟩
  by_contra hne
  let p : ↥S × ↥S := (⟨a, ha⟩, ⟨b, hb⟩)
  let hspec := Classical.choose_spec (exists_diff (p := p) hne)
  have hdp_eq : diffPair p = Classical.choose (exists_diff (p := p) hne) := by
    dsimp only [diffPair, p]; rw [dite_eq_left_of_eq_true (eq_true hne)]
  have hle_sup : Classical.choose (exists_diff (p := p) hne) ≤ ⨆ q : ↥S × ↥S, diffPair q := by
    rw [← hdp_eq]
    exact le_ciSup ⟨κ.ord, Set.forall_mem_range.2 fun q => (hdiff_lt q).le⟩ p
  have hne_proj := hspec.2
  dsimp only [p] at hne_proj
  rw [f_comp hle_sup hsup.le a, f_comp hle_sup hsup.le b, heq] at hne_proj
  exact hne_proj rfl

/-- For any regular `κ` and `κ`-accessible `F` with `A F 1` nonempty, every tail transition
map `f (h : α ≤ β)` with `κ.ord ≤ α ≤ β` is injective. -/
theorem tail_monic_of_accessible {F : SetFunctor} {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hacc : F.IsAccessible κ) [Nonempty (A F 1)] :
    ∀ {α β : Ordinal.{0}}, κ.ord ≤ α → ∀ (hαβ : α ≤ β), Function.Injective (f (F := F) hαβ) := by
  have hlim_κ : Order.IsSuccLimit κ.ord := Cardinal.isSuccLimit_ord hκ.aleph0_le
  have hκ_pos : 0 < κ.ord := hκ.ord_pos
  have hne_stage : ∀ δ : Ordinal.{0}, Nonempty (A F δ) := fun δ => nonempty_of_nonempty_one δ
  have hstep_inj : ∀ {δ : Ordinal.{0}}, κ.ord ≤ δ →
      Function.Injective (f (F := F) (Order.le_succ δ)) := by
    intro δ
    induction δ using WellFoundedLT.induction with
    | ind δ IH =>
      intro hκδ x y hxy
      rcases Ordinal.zero_or_succ_or_isSuccLimit δ with rfl | ⟨δ', rfl⟩ | hlim_δ
      · exact absurd hκδ (not_le_of_gt hκ_pos)
      · have hκδ' : κ.ord ≤ δ' := by
          rcases lt_or_eq_of_le hκδ with hlt | heq
          · exact Order.lt_succ_iff.1 hlt
          · exact absurd hlim_κ (heq ▸ Order.not_isSuccLimit_succ δ')
        have h_inj_δ' := IH δ' (Order.lt_succ δ') hκδ'
        have : Nonempty (A F (Order.succ δ')) := hne_stage _
        have hF_inj : Function.Injective (F.map (f (F := F) (Order.le_succ δ'))) :=
          F.map_injective_of_nonempty h_inj_δ'
        apply (succEquiv F (Order.succ δ')).injective
        apply hF_inj
        rw [← succEquiv_f_succ (Order.le_succ δ') x, ← succEquiv_f_succ (Order.le_succ δ') y, hxy]
      · -- Limit case `κ.ord ≤ δ` (`hlim_δ : Order.IsSuccLimit δ`), proved using `hacc`!
        -- First note `f (hκδ) : A F δ → A F κ.ord` is injective by local projection induction below,
        -- Wait: we only need `f (α ≤ δ)` injective on `< κ` subsets, or prove `f (κ.ord ≤ δ)` injective
        -- directly when `δ` is limit by `IH` on `i < δ`! Wait: `IH` proves `f (le_succ γ)` injective
        -- for all `κ.ord ≤ γ < δ`, which gives `f (α ≤ γ)` injective for all `κ.ord ≤ α ≤ γ < δ`,
        -- hence by `limitEquiv` at `δ`, `f (κ.ord ≤ δ)` is injective!
        have htail_lt : ∀ {γ α : Ordinal.{0}}, γ < δ → κ.ord ≤ α → ∀ (hαγ : α ≤ γ),
            Function.Injective (f (F := F) hαγ) := by
          intro γ
          induction γ using WellFoundedLT.induction with
          | ind γ IHγ =>
            intro α hγδ hκα hαγ a b hab
            rcases eq_or_lt_of_le hαγ with rfl | hlt
            · simpa using hab
            · rcases Ordinal.zero_or_succ_or_isSuccLimit γ with rfl | ⟨γ', rfl⟩ | hlγ
              · exact absurd hlt (not_lt_of_ge bot_le)
              · have hαγ' : α ≤ γ' := Order.lt_succ_iff.1 hlt
                have hκγ' : κ.ord ≤ γ' := hκα.trans hαγ'
                have h_succ := IH γ' ((Order.lt_succ γ').trans hγδ) hκγ'
                have hab' := congrArg id hab
                rw [f_comp hαγ' (Order.le_succ γ') a, f_comp hαγ' (Order.le_succ γ') b] at hab'
                exact h_succ (IHγ γ' (Order.lt_succ γ') ((Order.lt_succ γ').trans hγδ) hκα hαγ' hab')
              · apply (limitEquiv F hlγ).injective
                apply Subtype.ext
                funext i
                rw [limitEquiv_proj, limitEquiv_proj]
                rcases le_or_gt i.toOrd.1 α with hiα | hαi
                · rw [f_comp hiα hlt.le a, f_comp hiα hlt.le b, hab]
                · exact IHγ i.toOrd.1 i.toOrd.2 (i.toOrd.2.trans hγδ) hκα hαi.le (by
                    rw [← f_comp hαi.le i.toOrd.2.le a, ← f_comp hαi.le i.toOrd.2.le b, hab])
        have h_inj_κδ : Function.Injective (f (F := F) hκδ) := by
          intro a b hab
          apply (limitEquiv F hlim_δ).injective
          apply Subtype.ext
          funext i
          rw [limitEquiv_proj, limitEquiv_proj]
          rcases le_or_gt i.toOrd.1 κ.ord with hiκ | hκi
          · rw [f_comp hiκ hκδ a, f_comp hiκ hκδ b, hab]
          · exact htail_lt i.toOrd.2 le_rfl hκi.le (by
              rw [← f_comp hκi.le i.toOrd.2.le a, ← f_comp hκi.le i.toOrd.2.le b, hab])
        obtain ⟨S₁, hS₁, u₁, hu₁⟩ := hacc (succEquiv F δ x)
        obtain ⟨S₂, hS₂, u₂, hu₂⟩ := hacc (succEquiv F δ y)
        let a₀ : A F δ := Classical.arbitrary _
        let S : Set (A F δ) := S₁ ∪ S₂ ∪ {a₀}
        have hS_card : Cardinal.mk S < Cardinal.lift.{1, 0} κ := by
          have h12 : Cardinal.mk (S₁ ∪ S₂ : Set (A F δ)) < Cardinal.lift.{1, 0} κ :=
            lt_of_le_of_lt (Cardinal.mk_union_le S₁ S₂)
              (Cardinal.add_lt_of_lt hκ.lift.aleph0_le hS₁ hS₂)
          have hsing : Cardinal.mk ({a₀} : Set (A F δ)) < Cardinal.lift.{1, 0} κ := by
            rw [Cardinal.mk_singleton]
            exact lt_of_lt_of_le Cardinal.one_lt_aleph0 hκ.lift.aleph0_le
          exact lt_of_le_of_lt (Cardinal.mk_union_le (S₁ ∪ S₂) {a₀})
            (Cardinal.add_lt_of_lt hκ.lift.aleph0_le h12 hsing)
        let Sκ : Set (A F κ.ord) := f (F := F) hκδ '' S
        have hSκ_card : Cardinal.mk Sκ < Cardinal.lift.{1, 0} κ :=
          lt_of_le_of_lt Cardinal.mk_image_le hS_card
        obtain ⟨α, hακ, hinj_α⟩ := exists_proj_injective_on_lt hκ Sκ hSκ_card
        have hα_lt : α < δ := hακ.trans_le hκδ
        have hinj_S : ∀ a ∈ S, ∀ b ∈ S,
            f (F := F) hα_lt.le a = f (F := F) hα_lt.le b → a = b := by
          intro a ha b hb heq
          apply h_inj_κδ
          apply hinj_α (f (F := F) hκδ a) ⟨a, ha, rfl⟩ (f (F := F) hκδ b) ⟨b, hb, rfl⟩
          rw [← f_comp hακ.le hκδ a, ← f_comp hακ.le hκδ b]
          exact heq
        have : Nonempty ↥S := ⟨⟨a₀, Set.mem_union_right _ (Set.mem_singleton a₀)⟩⟩
        have hg_inj : Function.Injective (f (F := F) hα_lt.le ∘ SetFunctor.inc S) := by
          intro a b heq
          exact Subtype.ext (hinj_S a.1 a.2 b.1 b.2 heq)
        have hFg_inj : Function.Injective (F.map (f (F := F) hα_lt.le ∘ SetFunctor.inc S)) :=
          F.map_injective_of_nonempty hg_inj
        let inc₁ : ↥S₁ → ↥S := Set.inclusion (Set.subset_union_left.trans Set.subset_union_left)
        let inc₂ : ↥S₂ → ↥S := Set.inclusion (Set.subset_union_right.trans Set.subset_union_left)
        let v₁ : F.obj ↥S := F.map inc₁ u₁
        let v₂ : F.obj ↥S := F.map inc₂ u₂
        have hv₁ : F.map (SetFunctor.inc S) v₁ = succEquiv F δ x := by
          dsimp only [v₁]
          rw [← F.map_comp_apply]
          exact hu₁
        have hv₂ : F.map (SetFunctor.inc S) v₂ = succEquiv F δ y := by
          dsimp only [v₂]
          rw [← F.map_comp_apply]
          exact hu₂
        have hfeq : F.map (f (F := F) hα_lt.le ∘ SetFunctor.inc S) v₁ =
            F.map (f (F := F) hα_lt.le ∘ SetFunctor.inc S) v₂ := by
          rw [F.map_comp_apply, F.map_comp_apply, hv₁, hv₂]
          rw [← succEquiv_f_succ hα_lt.le x, ← succEquiv_f_succ hα_lt.le y]
          rw [f_comp (hlim_δ.succ_lt hα_lt).le (Order.le_succ δ) x,
              f_comp (hlim_δ.succ_lt hα_lt).le (Order.le_succ δ) y, hxy]
        have hv_eq : v₁ = v₂ := hFg_inj hfeq
        apply (succEquiv F δ).injective
        rw [← hv₁, ← hv₂, hv_eq]
  intro α β hκα hαβ
  induction β using WellFoundedLT.induction generalizing α with
  | ind β IHβ =>
    intro x y hxy
    rcases eq_or_lt_of_le hαβ with rfl | hlt
    · simpa using hxy
    · rcases Ordinal.zero_or_succ_or_isSuccLimit β with rfl | ⟨β', rfl⟩ | hlim_β
      · exact absurd hlt (not_lt_of_ge bot_le)
      · have hαβ' : α ≤ β' := Order.lt_succ_iff.1 hlt
        rw [f_comp hαβ' (Order.le_succ β') x, f_comp hαβ' (Order.le_succ β') y] at hxy
        exact hstep_inj (hκα.trans hαβ') (IHβ β' (Order.lt_succ β') hκα hαβ' hxy)
      · apply (limitEquiv F hlim_β).injective
        apply Subtype.ext
        funext i
        rw [limitEquiv_proj, limitEquiv_proj]
        rcases le_or_gt i.toOrd.1 α with hiα | hαi
        · rw [f_comp hiα hαβ x, f_comp hiα hαβ y, hxy]
        · exact IHβ i.toOrd.1 i.toOrd.2 hκα hαi.le (by
            rw [← f_comp hαi.le i.toOrd.2.le x, ← f_comp hαi.le i.toOrd.2.le y, hxy])

end AccessibleTailMonic

end TerminalSeq.Abstract
