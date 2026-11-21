import TerminalSeq.Abstract.SetFunctor
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Abstract Terminal Sequence of an Arbitrary `SetFunctor`

Constructs the ordinal-indexed terminal sequence `(A F α, f h)` for any `F : SetFunctor`
directly in `Type 1` via uniqueness (`agree_on_prefix`) and transfinite induction
(`exists_validSeq`), without encoding `F` into `ZFSet`, and exposes:
- `A F α : Type 1` and transition maps `f (h : α ≤ β) : A F β → A F α`
- `f_id`, `f_comp`
- `zeroEquiv : A F 0 ≃ PUnit.{2}`
- `succEquiv : A F (Order.succ α) ≃ F.obj (A F α)` and `succEquiv_f_succ`
- `limitEquiv` and `limitEquiv_proj`
-/

noncomputable section

open Classical Ordinal

namespace TerminalSeq.Abstract

section Construction

private structure SeqPrefix (F : SetFunctor) (α : Ordinal.{0}) : Type 2 where
  obj : Ordinal.{0} → Type 1
  map : ∀ {β γ : Ordinal.{0}}, β ≤ γ → γ ≤ α → obj γ → obj β

private structure IsValidSeq (F : SetFunctor) (α : Ordinal.{0}) (S : SeqPrefix F α) : Prop where
  map_id : ∀ {β} (hβα : β ≤ α) (x : S.obj β), S.map le_rfl hβα x = x
  map_comp : ∀ {β γ δ} (hβγ : β ≤ γ) (hγδ : γ ≤ δ) (hδα : δ ≤ α) (x : S.obj δ),
    S.map (hβγ.trans hγδ) hδα x = S.map hβγ (hγδ.trans hδα) (S.map hγδ hδα x)
  zero_eq : S.obj 0 = PUnit.{2}
  succ_eq : ∀ {δ}, Order.succ δ ≤ α → S.obj (Order.succ δ) = F.obj (S.obj δ)
  map_succ_succ : ∀ {β δ} (hβδ : β ≤ δ) (hδα : Order.succ δ ≤ α) (x : S.obj (Order.succ δ)),
    cast (succ_eq ((Order.succ_le_succ hβδ).trans hδα)) (S.map (Order.succ_le_succ hβδ) hδα x) =
      F.map (S.map hβδ ((Order.lt_succ δ).le.trans hδα)) (cast (succ_eq hδα) x)
  limit_eq : ∀ {l}, Order.IsSuccLimit l → ∀ (hlα : l ≤ α),
    S.obj l = { t : (i : l.ToType) → S.obj i.toOrd.1 //
      ∀ (i j : l.ToType) (hij : i.toOrd.1 ≤ j.toOrd.1),
        S.map hij (j.toOrd.2.le.trans hlα) (t j) = t i }
  limit_proj : ∀ {l} (hl : Order.IsSuccLimit l) (hlα : l ≤ α) (i : l.ToType) (x : S.obj l),
    S.map i.toOrd.2.le hlα x = (cast (limit_eq hl hlα) x).1 i

private theorem cast_injective {A B : Type 1} (h : A = B) : Function.Injective (cast h) := by
  subst h
  intro a b hab
  exact hab

@[simp]
private theorem cast_cast_symm {A B : Type 1} (h : A = B) (x : B) :
    cast h (cast h.symm x) = x := by
  subst h; rfl

@[simp]
private theorem cast_symm_cast {A B : Type 1} (h : A = B) (x : A) :
    cast h.symm (cast h x) = x := by
  subst h; rfl

private theorem cast_trans_eq {A B C : Type 1} (h1 : A = B) (h2 : B = C) (x : A) :
    cast h2 (cast h1 x) = cast (h1.trans h2) x := by
  subst h1 h2; rfl

private theorem subtype_pi_eq {I : Type 0} {T₁ T₂ : I → Type 1} (hT : ∀ i, T₁ i = T₂ i)
    {P₁ : ((i : I) → T₁ i) → Prop} {P₂ : ((i : I) → T₂ i) → Prop}
    (hP : ∀ (t₁ : (i : I) → T₁ i) (t₂ : (i : I) → T₂ i),
      (∀ i, cast (hT i) (t₁ i) = t₂ i) → (P₁ t₁ ↔ P₂ t₂)) :
    ({ t : (i : I) → T₁ i // P₁ t } : Type 1) = { t : (i : I) → T₂ i // P₂ t } := by
  have hfun : T₁ = T₂ := funext hT
  subst hfun
  have hPeq : P₁ = P₂ := funext fun t => propext (hP t t fun _ => rfl)
  subst hPeq
  rfl

private theorem cast_limit_proj {I : Type 0} {T₁ T₂ : I → Type 1} (hT : ∀ i, T₁ i = T₂ i)
    {P₁ : ((i : I) → T₁ i) → Prop} {P₂ : ((i : I) → T₂ i) → Prop}
    (hEq : ({ t : (i : I) → T₁ i // P₁ t } : Type 1) = { t : (i : I) → T₂ i // P₂ t })
    (hCompat : ∀ (t₁ : (i : I) → T₁ i) (t₂ : (i : I) → T₂ i),
      (∀ i, cast (hT i) (t₁ i) = t₂ i) → (P₁ t₁ ↔ P₂ t₂))
    (x : { t : (i : I) → T₁ i // P₁ t }) (i : I) :
    cast (hT i) (x.1 i) = (cast hEq x).1 i := by
  have hfun : T₁ = T₂ := funext hT
  subst hfun
  have hPeq : P₁ = P₂ := funext fun t => propext (hCompat t t fun _ => rfl)
  subst hPeq
  rfl

private theorem cast_F_map {F : SetFunctor} {A₁ A₂ B₁ B₂ : Type 1}
    (hA : A₁ = A₂) (hB : B₁ = B₂) (g₁ : A₁ → B₁) (g₂ : A₂ → B₂)
    (hg : ∀ x : A₁, cast hB (g₁ x) = g₂ (cast hA x)) (u : F.obj A₁) :
    cast (congrArg F.obj hB) (F.map g₁ u) = F.map g₂ (cast (congrArg F.obj hA) u) := by
  subst hA; subst hB
  have hgeq : g₁ = g₂ := funext hg
  subst hgeq
  rfl

private theorem limit_compat_iff {F : SetFunctor} {α₁ α₂ l : Ordinal.{0}}
    {S₁ : SeqPrefix F α₁} {S₂ : SeqPrefix F α₂}
    (hl₁ : l ≤ α₁) (hl₂ : l ≤ α₂)
    (hT : ∀ i : l.ToType, S₁.obj i.toOrd.1 = S₂.obj i.toOrd.1)
    (hMap : ∀ (i j : l.ToType) (hij : i.toOrd.1 ≤ j.toOrd.1) (z : S₁.obj j.toOrd.1),
      cast (hT i) (S₁.map hij (j.toOrd.2.le.trans hl₁) z) =
        S₂.map hij (j.toOrd.2.le.trans hl₂) (cast (hT j) z))
    (t₁ : (i : l.ToType) → S₁.obj i.toOrd.1) (t₂ : (i : l.ToType) → S₂.obj i.toOrd.1)
    (ht : ∀ i, cast (hT i) (t₁ i) = t₂ i) :
    (∀ (i j : l.ToType) (hij : i.toOrd.1 ≤ j.toOrd.1),
      S₁.map hij (j.toOrd.2.le.trans hl₁) (t₁ j) = t₁ i) ↔
    (∀ (i j : l.ToType) (hij : i.toOrd.1 ≤ j.toOrd.1),
      S₂.map hij (j.toOrd.2.le.trans hl₂) (t₂ j) = t₂ i) := by
  constructor
  · intro hc i j hij
    have hjm := hMap i j hij (t₁ j)
    rw [hc i j hij, ht i] at hjm
    rw [← ht j, ← hjm]
  · intro hc i j hij
    have hjm := hMap i j hij (t₁ j)
    rw [ht j, hc i j hij, ← ht i] at hjm
    exact cast_injective (hT i) hjm

private theorem agree_on_prefix {F : SetFunctor} {α₁ α₂ : Ordinal.{0}}
    {S₁ : SeqPrefix F α₁} {S₂ : SeqPrefix F α₂}
    (hV₁ : IsValidSeq F α₁ S₁) (hV₂ : IsValidSeq F α₂ S₂) :
    ∀ γ : Ordinal.{0}, ∀ (hγ₁ : γ ≤ α₁) (hγ₂ : γ ≤ α₂),
      (S₁.obj γ = S₂.obj γ) ∧
      (∀ (β : Ordinal.{0}) (hβγ : β ≤ γ) (hobj_β : S₁.obj β = S₂.obj β)
         (hobj_γ : S₁.obj γ = S₂.obj γ) (x : S₁.obj γ),
        cast hobj_β (S₁.map hβγ hγ₁ x) = S₂.map hβγ hγ₂ (cast hobj_γ x)) := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
    intro hγ₁ hγ₂
    have hobj : S₁.obj γ = S₂.obj γ := by
      rcases Ordinal.zero_or_succ_or_isSuccLimit γ with rfl | ⟨δ, rfl⟩ | hl
      · rw [hV₁.zero_eq, hV₂.zero_eq]
      · have hδ_obj := (IH δ (Order.lt_succ δ) ((Order.lt_succ δ).le.trans hγ₁)
          ((Order.lt_succ δ).le.trans hγ₂)).1
        rw [hV₁.succ_eq hγ₁, hV₂.succ_eq hγ₂, hδ_obj]
      · rw [hV₁.limit_eq hl hγ₁, hV₂.limit_eq hl hγ₂]
        have hT : ∀ i : γ.ToType, S₁.obj i.toOrd.1 = S₂.obj i.toOrd.1 :=
          fun i => (IH i.toOrd.1 i.toOrd.2 (i.toOrd.2.le.trans hγ₁)
            (i.toOrd.2.le.trans hγ₂)).1
        have hMap : ∀ (i j : γ.ToType) (hij : i.toOrd.1 ≤ j.toOrd.1) (z : S₁.obj j.toOrd.1),
            cast (hT i) (S₁.map hij (j.toOrd.2.le.trans hγ₁) z) =
              S₂.map hij (j.toOrd.2.le.trans hγ₂) (cast (hT j) z) :=
          fun i j hij z => (IH j.toOrd.1 j.toOrd.2 (j.toOrd.2.le.trans hγ₁)
            (j.toOrd.2.le.trans hγ₂)).2 i.toOrd.1 hij (hT i) (hT j) z
        exact subtype_pi_eq hT (limit_compat_iff hγ₁ hγ₂ hT hMap)
    refine ⟨hobj, fun β hβγ hobj_β hobj_γ x => ?_⟩
    rcases eq_or_lt_of_le hβγ with rfl | hlt
    · rw [hV₁.map_id hγ₁ x, hV₂.map_id hγ₂ (cast hobj_γ x)]
    · rcases Ordinal.zero_or_succ_or_isSuccLimit γ with rfl | ⟨δ, rfl⟩ | hl
      · exact absurd hlt (not_lt_of_ge bot_le)
      · have hβδ : β ≤ δ := Order.lt_succ_iff.1 hlt
        have hδ₁ : δ ≤ α₁ := (Order.lt_succ δ).le.trans hγ₁
        have hδ₂ : δ ≤ α₂ := (Order.lt_succ δ).le.trans hγ₂
        have hδ_res := IH δ (Order.lt_succ δ) hδ₁ hδ₂
        have hstep_agree : ∀ y : S₁.obj (Order.succ δ),
            cast hδ_res.1 (S₁.map (Order.le_succ δ) hγ₁ y) =
              S₂.map (Order.le_succ δ) hγ₂ (cast hobj_γ y) := by
          clear x
          intro y
          rcases Ordinal.zero_or_succ_or_isSuccLimit δ with hδ0 | ⟨δ', rfl⟩ | hdl
          · subst hδ0
            have hSub : Subsingleton (S₂.obj 0) := by rw [hV₂.zero_eq]; infer_instance
            exact Subsingleton.elim _ _
          · have hδ'_obj := (IH δ' ((Order.lt_succ δ').trans (Order.lt_succ _))
              ((Order.lt_succ δ').le.trans hδ₁) ((Order.lt_succ δ').le.trans hδ₂)).1
            have h1 := hV₁.map_succ_succ (Order.le_succ δ') hγ₁ y
            have h2 := hV₂.map_succ_succ (Order.le_succ δ') hγ₂ (cast hobj_γ y)
            have hFm := cast_F_map hδ_res.1 hδ'_obj
              (S₁.map (Order.le_succ δ') hδ₁) (S₂.map (Order.le_succ δ') hδ₂)
              (fun z => hδ_res.2 δ' (Order.le_succ δ') hδ'_obj hδ_res.1 z)
              (cast (hV₁.succ_eq hγ₁) y)
            rw [← h1] at hFm
            have hc1 : cast (congrArg F.obj hδ_res.1) (cast (hV₁.succ_eq hγ₁) y) =
                cast (hV₂.succ_eq hγ₂) (cast hobj_γ y) := by
              have hS1 := hV₁.succ_eq hγ₁
              have hS2 := hV₂.succ_eq hγ₂
              grind
            rw [hc1, ← h2] at hFm
            apply cast_injective (hV₂.succ_eq hδ₂)
            have hc2 : cast (congrArg F.obj hδ'_obj)
                (cast (hV₁.succ_eq hδ₁) (S₁.map (Order.le_succ (Order.succ δ')) hγ₁ y)) =
                cast (hV₂.succ_eq hδ₂) (cast hδ_res.1 (S₁.map (Order.le_succ (Order.succ δ')) hγ₁ y)) := by
              have hS1 := hV₁.succ_eq hδ₁
              have hS2 := hV₂.succ_eq hδ₂
              grind
            rw [← hc2]
            exact hFm
          · have hT : ∀ i : δ.ToType, S₁.obj i.toOrd.1 = S₂.obj i.toOrd.1 :=
              fun i => (IH i.toOrd.1 (i.toOrd.2.trans (Order.lt_succ δ))
                (i.toOrd.2.le.trans hδ₁) (i.toOrd.2.le.trans hδ₂)).1
            have hMap : ∀ (i j : δ.ToType) (hij : i.toOrd.1 ≤ j.toOrd.1) (z : S₁.obj j.toOrd.1),
                cast (hT i) (S₁.map hij (j.toOrd.2.le.trans hδ₁) z) =
                  S₂.map hij (j.toOrd.2.le.trans hδ₂) (cast (hT j) z) :=
              fun i j hij z => (IH j.toOrd.1 (j.toOrd.2.trans (Order.lt_succ δ))
                (j.toOrd.2.le.trans hδ₁) (j.toOrd.2.le.trans hδ₂)).2
                i.toOrd.1 hij (hT i) (hT j) z
            have hLim1 := hV₁.limit_eq hdl hδ₁
            have hLim2 := hV₂.limit_eq hdl hδ₂
            have hCompat := limit_compat_iff hδ₁ hδ₂ hT hMap
            apply cast_injective hLim2
            apply Subtype.ext
            funext i
            have hrhs := hV₂.limit_proj hdl hδ₂ i (S₂.map (Order.le_succ δ) hγ₂ (cast hobj_γ y))
            rw [← hrhs, ← hV₂.map_comp i.toOrd.2.le (Order.le_succ δ) hγ₂]
            have hEqLim := subtype_pi_eq hT hCompat
            have hlim_c := cast_limit_proj hT hEqLim hCompat (cast hLim1 (S₁.map (Order.le_succ δ) hγ₁ y)) i
            have hlim_cast : cast hEqLim (cast hLim1 (S₁.map (Order.le_succ δ) hγ₁ y)) =
                cast hLim2 (cast hδ_res.1 (S₁.map (Order.le_succ δ) hγ₁ y)) := by grind
            rw [hlim_cast] at hlim_c
            rw [← hlim_c, ← hV₁.limit_proj hdl hδ₁ i, ← hV₁.map_comp i.toOrd.2.le (Order.le_succ δ) hγ₁]
            have hs_i : Order.succ i.toOrd.1 ≤ δ := (hdl.succ_lt i.toOrd.2).le
            have hi_le_succ : i.toOrd.1 ≤ Order.succ i.toOrd.1 := Order.le_succ i.toOrd.1
            have hsi_obj := (IH (Order.succ i.toOrd.1) ((hdl.succ_lt i.toOrd.2).trans (Order.lt_succ δ))
              (hs_i.trans hδ₁) (hs_i.trans hδ₂)).1
            rw [hV₁.map_comp hi_le_succ (Order.succ_le_succ i.toOrd.2.le) hγ₁ y,
                hV₂.map_comp hi_le_succ (Order.succ_le_succ i.toOrd.2.le) hγ₂ (cast hobj_γ y)]
            have hsucc_agree : cast hsi_obj (S₁.map (Order.succ_le_succ i.toOrd.2.le) hγ₁ y) =
                S₂.map (Order.succ_le_succ i.toOrd.2.le) hγ₂ (cast hobj_γ y) := by
              have hFm := cast_F_map hδ_res.1 (hT i)
                (S₁.map i.toOrd.2.le hδ₁) (S₂.map i.toOrd.2.le hδ₂)
                (fun z => hδ_res.2 i.toOrd.1 i.toOrd.2.le (hT i) hδ_res.1 z)
                (cast (hV₁.succ_eq hγ₁) y)
              rw [← hV₁.map_succ_succ i.toOrd.2.le hγ₁ y] at hFm
              have hc1 : cast (congrArg F.obj hδ_res.1) (cast (hV₁.succ_eq hγ₁) y) =
                  cast (hV₂.succ_eq hγ₂) (cast hobj_γ y) := by
                have hS1 := hV₁.succ_eq hγ₁
                have hS2 := hV₂.succ_eq hγ₂
                grind
              rw [hc1, ← hV₂.map_succ_succ i.toOrd.2.le hγ₂ (cast hobj_γ y)] at hFm
              apply cast_injective (hV₂.succ_eq (hs_i.trans hδ₂))
              have hc2 : cast (congrArg F.obj (hT i))
                  (cast (hV₁.succ_eq (hs_i.trans hδ₁)) (S₁.map (Order.succ_le_succ i.toOrd.2.le) hγ₁ y)) =
                  cast (hV₂.succ_eq (hs_i.trans hδ₂))
                    (cast hsi_obj (S₁.map (Order.succ_le_succ i.toOrd.2.le) hγ₁ y)) := by
                have hS1 := hV₁.succ_eq (hs_i.trans hδ₁)
                have hS2 := hV₂.succ_eq (hs_i.trans hδ₂)
                grind
              rw [← hc2]
              exact hFm
            rw [← hsucc_agree]
            exact (IH (Order.succ i.toOrd.1) ((hdl.succ_lt i.toOrd.2).trans (Order.lt_succ δ))
              (hs_i.trans hδ₁) (hs_i.trans hδ₂)).2 i.toOrd.1 hi_le_succ (hT i) hsi_obj
              (S₁.map (Order.succ_le_succ i.toOrd.2.le) hγ₁ y)
        rw [hV₁.map_comp hβδ (Order.le_succ δ) hγ₁ x,
            hV₂.map_comp hβδ (Order.le_succ δ) hγ₂ (cast hobj_γ x),
            ← hstep_agree x]
        exact hδ_res.2 β hβδ hobj_β hδ_res.1 (S₁.map (Order.le_succ δ) hγ₁ x)
      · let iβ : γ.ToType := Ordinal.ToType.mk ⟨β, hlt⟩
        have hiβ : iβ.toOrd.1 = β := by simp [iβ]
        have hT : ∀ i : γ.ToType, S₁.obj i.toOrd.1 = S₂.obj i.toOrd.1 :=
          fun i => (IH i.toOrd.1 i.toOrd.2 (i.toOrd.2.le.trans hγ₁)
            (i.toOrd.2.le.trans hγ₂)).1
        have hMap : ∀ (i j : γ.ToType) (hij : i.toOrd.1 ≤ j.toOrd.1) (z : S₁.obj j.toOrd.1),
            cast (hT i) (S₁.map hij (j.toOrd.2.le.trans hγ₁) z) =
              S₂.map hij (j.toOrd.2.le.trans hγ₂) (cast (hT j) z) :=
          fun i j hij z => (IH j.toOrd.1 j.toOrd.2 (j.toOrd.2.le.trans hγ₁)
            (j.toOrd.2.le.trans hγ₂)).2 i.toOrd.1 hij (hT i) (hT j) z
        have hLim1 := hV₁.limit_eq hl hγ₁
        have hLim2 := hV₂.limit_eq hl hγ₂
        have hCompat := limit_compat_iff hγ₁ hγ₂ hT hMap
        have hEqLim := subtype_pi_eq hT hCompat
        have hlim_c := cast_limit_proj hT hEqLim hCompat (cast hLim1 x) iβ
        have hlim_cast : cast hEqLim (cast hLim1 x) = cast hLim2 (cast hobj_γ x) := by grind
        rw [hlim_cast, ← hV₂.limit_proj hl hγ₂ iβ (cast hobj_γ x),
            ← hV₁.limit_proj hl hγ₁ iβ x] at hlim_c
        have hfix : ∀ (o : Ordinal.{0}) (ho : o ≤ γ) (heq : o = β) (hobj_o : S₁.obj o = S₂.obj o),
            cast hobj_o (S₁.map ho hγ₁ x) = S₂.map ho hγ₂ (cast hobj_γ x) →
            cast hobj_β (S₁.map hlt.le hγ₁ x) = S₂.map hlt.le hγ₂ (cast hobj_γ x) := by
          rintro o _ rfl hobj_o h
          exact h
        exact hfix iβ.toOrd.1 iβ.toOrd.2.le hiβ (hT iβ) hlim_c

private theorem exists_validSeq (F : SetFunctor) :
    ∀ α : Ordinal.{0}, ∃ S : SeqPrefix F α, IsValidSeq F α S := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
    rcases Ordinal.zero_or_succ_or_isSuccLimit α with rfl | ⟨α', rfl⟩ | hl
    · refine ⟨⟨fun _ => PUnit.{2}, fun _ _ x => x⟩, ?_⟩
      refine ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, rfl, fun {δ} hδ => ?_, ?_, ?_, ?_⟩
      · exact absurd hδ (not_le_of_gt (bot_le.trans_lt (Order.lt_succ δ)))
      · intro β δ _ hδ
        exact absurd hδ (not_le_of_gt (bot_le.trans_lt (Order.lt_succ δ)))
      · intro l hl hll; exact absurd hll (not_le_of_gt hl.bot_lt)
      · intro l hl hll; exact absurd hll (not_le_of_gt hl.bot_lt)
    · obtain ⟨S', hS'⟩ := IH α' (Order.lt_succ α')
      let obj : Ordinal.{0} → Type 1 := fun β =>
        if β ≤ α' then S'.obj β else if β = Order.succ α' then F.obj (S'.obj α') else PUnit.{2}
      have h_le : ∀ {β} (h : β ≤ α'), obj β = S'.obj β := by
        intro β h; dsimp only [obj]; rw [ite_eq_left_iff.2 fun hn => absurd h hn]
      have h_top : obj (Order.succ α') = F.obj (S'.obj α') := by
        dsimp only [obj]
        rw [ite_eq_right_iff.2 fun hle => absurd hle (not_le_of_gt (Order.lt_succ α')),
            ite_eq_left_iff.2 fun hne => absurd rfl hne]
      let tLim (hlim : Order.IsSuccLimit α') (u : F.obj (S'.obj α')) :
          (i : α'.ToType) → S'.obj i.toOrd.1 := fun i =>
        S'.map (Order.le_succ i.toOrd.1) (hlim.succ_lt i.toOrd.2).le
          (cast (hS'.succ_eq (hlim.succ_lt i.toOrd.2).le).symm
            (F.map (S'.map i.toOrd.2.le le_rfl) u))
      have hcompatLim (hlim : Order.IsSuccLimit α') (u : F.obj (S'.obj α')) :
          ∀ (i j : α'.ToType) (hij : i.toOrd.1 ≤ j.toOrd.1),
            S'.map hij j.toOrd.2.le (tLim hlim u j) = tLim hlim u i := by
        intro i j hij
        dsimp only [tLim]
        rw [← hS'.map_comp hij (Order.le_succ j.toOrd.1) (hlim.succ_lt j.toOrd.2).le]
        rw [hS'.map_comp (Order.le_succ i.toOrd.1) (Order.succ_le_succ hij)
          (hlim.succ_lt j.toOrd.2).le]
        congr 1
        apply cast_injective (hS'.succ_eq (hlim.succ_lt i.toOrd.2).le)
        rw [hS'.map_succ_succ hij (hlim.succ_lt j.toOrd.2).le]
        have hcomp_f : S'.map hij j.toOrd.2.le ∘ S'.map j.toOrd.2.le le_rfl =
            S'.map i.toOrd.2.le le_rfl :=
          funext fun z => (hS'.map_comp hij j.toOrd.2.le le_rfl z).symm
        rw [cast_cast_symm, ← F.map_comp_apply, hcomp_f, cast_cast_symm]
      let stepDown : F.obj (S'.obj α') → S'.obj α' :=
        if h0 : α' = 0 then
          have hze : S'.obj α' = PUnit.{2} := h0 ▸ hS'.zero_eq
          fun _ => cast hze.symm PUnit.unit
        else if hex : ∃ δ, Order.succ δ = α' then
          let δ := Classical.choose hex
          have hδ : Order.succ δ = α' := Classical.choose_spec hex
          fun u => cast (congrArg S'.obj hδ) (cast (hS'.succ_eq (le_of_eq hδ)).symm
            (F.map (S'.map (Order.le_succ δ) (le_of_eq hδ))
              (cast (congrArg F.obj (congrArg S'.obj hδ.symm)) u)))
        else
          have hlim : Order.IsSuccLimit α' := by
            rcases Ordinal.zero_or_succ_or_isSuccLimit α' with h | ⟨δ, hd⟩ | hlim
            · exact absurd h h0
            · exact absurd ⟨δ, hd⟩ hex
            · exact hlim
          fun u => cast (hS'.limit_eq hlim le_rfl).symm ⟨tLim hlim u, hcompatLim hlim u⟩
      have hstep_succ : ∀ (δ : Ordinal.{0}) (hδ : Order.succ δ = α') (u : F.obj (S'.obj α')),
          cast (hS'.succ_eq (le_of_eq hδ)) (cast (congrArg S'.obj hδ.symm) (stepDown u)) =
            F.map (S'.map (Order.le_succ δ) (le_of_eq hδ))
              (cast (congrArg F.obj (congrArg S'.obj hδ.symm)) u) := by
        intro δ hδ u
        have hne0 : α' ≠ 0 := by rw [← hδ]; exact Order.succ_ne_bot δ
        have hex : ∃ d, Order.succ d = α' := ⟨δ, hδ⟩
        dsimp only [stepDown]
        rw [dite_eq_right_of_eq_false (eq_false hne0), dite_eq_left_of_eq_true (eq_true hex)]
        have hδ0 : Classical.choose hex = δ :=
          Order.succ_injective ((Classical.choose_spec hex).trans hδ.symm)
        subst hδ0
        grind
      have hstep_limit : ∀ (hlim : Order.IsSuccLimit α') (β : Ordinal.{0}) (hβ : β < α')
          (u : F.obj (S'.obj α')),
          S'.map hβ.le le_rfl (stepDown u) =
            S'.map (Order.le_succ β) (hlim.succ_lt hβ).le
              (cast (hS'.succ_eq (hlim.succ_lt hβ).le).symm (F.map (S'.map hβ.le le_rfl) u)) := by
        intro hlim β hβ u
        have hne0 : α' ≠ 0 := hlim.bot_lt.ne'
        have hno : ¬ ∃ d, Order.succ d = α' := fun ⟨d, hd⟩ =>
          absurd (hd ▸ hlim) (Order.not_isSuccLimit_succ d)
        dsimp only [stepDown]
        rw [dite_eq_right_of_eq_false (eq_false hne0), dite_eq_right_of_eq_false (eq_false hno)]
        let iβ : α'.ToType := Ordinal.ToType.mk ⟨β, hβ⟩
        have hiβ : iβ.toOrd.1 = β := by simp [iβ]
        have hp := hS'.limit_proj hlim le_rfl iβ
          (cast (hS'.limit_eq hlim le_rfl).symm ⟨tLim hlim u, hcompatLim hlim u⟩)
        rw [cast_cast_symm] at hp
        dsimp only [tLim] at hp
        have hfix : ∀ (o : Ordinal.{0}) (ho : o ≤ α') (hs : Order.succ o ≤ α') (heq : o = β),
            S'.map ho le_rfl (cast (hS'.limit_eq hlim le_rfl).symm ⟨tLim hlim u, hcompatLim hlim u⟩) =
              S'.map (Order.le_succ o) hs
                (cast (hS'.succ_eq hs).symm (F.map (S'.map ho le_rfl) u)) →
            S'.map hβ.le le_rfl (cast (hS'.limit_eq hlim le_rfl).symm ⟨tLim hlim u, hcompatLim hlim u⟩) =
              S'.map (Order.le_succ β) (hlim.succ_lt hβ).le
                (cast (hS'.succ_eq (hlim.succ_lt hβ).le).symm (F.map (S'.map hβ.le le_rfl) u)) := by
          rintro o ho hs rfl h; exact h
        exact hfix iβ.toOrd.1 iβ.toOrd.2.le (hlim.succ_lt iβ.toOrd.2).le hiβ hp
      let map : ∀ {β γ : Ordinal.{0}}, β ≤ γ → γ ≤ Order.succ α' → obj γ → obj β :=
        fun {β γ} hβγ hγα x =>
          if hγ : γ ≤ α' then
            cast (h_le (hβγ.trans hγ)).symm (S'.map hβγ hγ (cast (h_le hγ) x))
          else
            have hγeq : γ = Order.succ α' := le_antisymm hγα (Order.succ_le_iff.2 (lt_of_not_ge hγ))
            if hβ : β ≤ α' then
              cast (h_le hβ).symm (S'.map hβ le_rfl (stepDown (cast (hγeq ▸ h_top) x)))
            else
              have hβeq : β = Order.succ α' := le_antisymm (hβγ.trans hγα) (Order.succ_le_iff.2 (lt_of_not_ge hβ))
              cast (by rw [hβeq, hγeq]) x
      have hmap_le : ∀ {β γ} (hβγ : β ≤ γ) (hγ : γ ≤ α') (x : obj γ),
          map hβγ (hγ.trans (Order.le_succ α')) x =
            cast (h_le (hβγ.trans hγ)).symm (S'.map hβγ hγ (cast (h_le hγ) x)) := by
        intro β γ hβγ hγ x; dsimp only [map]; rw [dite_eq_left_of_eq_true (eq_true hγ)]
      have hmap_top_le : ∀ {β} (hβ : β ≤ α') (x : obj (Order.succ α')),
          map (hβ.trans (Order.le_succ α')) le_rfl x =
            cast (h_le hβ).symm (S'.map hβ le_rfl (stepDown (cast h_top x))) := by
        intro β hβ x; dsimp only [map]
        rw [dite_eq_right_of_eq_false (eq_false (not_le_of_gt (Order.lt_succ α'))),
            dite_eq_left_of_eq_true (eq_true hβ)]
      have h_id : ∀ {β} (hβα : β ≤ Order.succ α') (x : obj β), map le_rfl hβα x = x := by
        intro β hβα x
        by_cases hβ : β ≤ α'
        · rw [hmap_le le_rfl hβ x, hS'.map_id hβ]; grind
        · have hβeq : β = Order.succ α' := le_antisymm hβα (Order.succ_le_iff.2 (lt_of_not_ge hβ))
          subst hβeq
          dsimp only [map]
          rw [dite_eq_right_of_eq_false (eq_false (not_le_of_gt (Order.lt_succ α'))),
              dite_eq_right_of_eq_false (eq_false (not_le_of_gt (Order.lt_succ α')))]
          rfl
      have h_comp : ∀ {β γ δ} (hβγ : β ≤ γ) (hγδ : γ ≤ δ) (hδα : δ ≤ Order.succ α') (x : obj δ),
          map (hβγ.trans hγδ) hδα x = map hβγ (hγδ.trans hδα) (map hγδ hδα x) := by
        intro β γ δ hβγ hγδ hδα x
        by_cases hδ : δ ≤ α'
        · have hγ : γ ≤ α' := hγδ.trans hδ
          rw [hmap_le (hβγ.trans hγδ) hδ x, hmap_le hγδ hδ x, hmap_le hβγ hγ]
          rw [hS'.map_comp hβγ hγδ hδ]; grind
        · have hδeq : δ = Order.succ α' := le_antisymm hδα (Order.succ_le_iff.2 (lt_of_not_ge hδ))
          subst hδeq
          by_cases hγ : γ ≤ α'
          · have hβ : β ≤ α' := hβγ.trans hγ
            rw [hmap_top_le hβ x, hmap_top_le hγ x, hmap_le hβγ hγ]
            rw [hS'.map_comp hβγ hγ le_rfl]; grind
          · have hγeq : γ = Order.succ α' := le_antisymm hγδ (Order.succ_le_iff.2 (lt_of_not_ge hγ))
            subst hγeq
            rw [h_id le_rfl x]
      have h_zero : obj 0 = PUnit.{2} := by
        have h0le : (0 : Ordinal.{0}) ≤ α' := bot_le
        rw [h_le h0le, hS'.zero_eq]
      have h_succ_eq : ∀ {δ}, Order.succ δ ≤ Order.succ α' → obj (Order.succ δ) = F.obj (obj δ) := by
        intro δ hδ
        have hδα : δ ≤ α' := Order.succ_le_succ_iff.1 hδ
        rcases eq_or_lt_of_le hδα with rfl | hlt
        · rw [h_top, h_le le_rfl]
        · have hsd : Order.succ δ ≤ α' := Order.succ_le_iff.2 hlt
          rw [h_le hsd, h_le hδα, hS'.succ_eq hsd]
      let S_next : SeqPrefix F (Order.succ α') := ⟨obj, map⟩
      refine ⟨S_next, h_id, h_comp, h_zero, h_succ_eq, ?_, ?_, ?_⟩
      · dsimp only [S_next]
        intro β δ hβδ hδα x
        have hδα' : δ ≤ α' := Order.succ_le_succ_iff.1 hδα
        rcases eq_or_lt_of_le hδα' with rfl | hlt
        · rcases eq_or_lt_of_le hβδ with rfl | hβlt
          · rw [h_id hδα x]
            have hid_eq : map le_rfl (Order.le_succ β) = id := funext (h_id (Order.le_succ β))
            rw [hid_eq, F.map_id_apply]
          · have hsβ : Order.succ β ≤ δ := Order.succ_le_iff.2 hβlt
            have hmap_fn : map hβδ (Order.le_succ δ) =
                fun z => cast (h_le hβδ).symm (S'.map hβδ le_rfl (cast (h_le le_rfl) z)) :=
              funext fun z => hmap_le hβlt.le le_rfl z
            rw [hmap_top_le hsβ x, hmap_fn]
            have hF_rhs := cast_F_map (h_le le_rfl).symm (h_le hβlt.le).symm
              (S'.map hβlt.le le_rfl)
              (fun z => cast (h_le hβlt.le).symm (S'.map hβlt.le le_rfl (cast (h_le le_rfl) z)))
              (fun z => by rw [cast_symm_cast]) (cast h_top x)
            have hc_top : cast (congrArg F.obj (h_le le_rfl).symm) (cast h_top x) =
                cast (h_succ_eq hδα) x :=
              cast_trans_eq h_top (congrArg F.obj (h_le le_rfl).symm) x
            rw [hc_top] at hF_rhs
            rw [← hF_rhs]
            have h_lhs_c : cast (h_succ_eq (hsβ.trans (Order.le_succ δ)))
                (cast (h_le hsβ).symm (S'.map hsβ le_rfl (stepDown (cast h_top x)))) =
                cast (congrArg F.obj (h_le hβlt.le).symm)
                  (cast (hS'.succ_eq hsβ) (S'.map hsβ le_rfl (stepDown (cast h_top x)))) := by
              rw [cast_trans_eq, cast_trans_eq]
            rw [h_lhs_c]
            congr 1
            rcases Ordinal.zero_or_succ_or_isSuccLimit δ with h0 | ⟨δ', hδ'⟩ | hlim
            · exact absurd (h0 ▸ hβlt) (not_lt_of_ge bot_le)
            · have hcase_succ : ∀ (d : Ordinal.{0}) (hd : Order.succ d = δ)
                  (hsb : Order.succ β ≤ δ) (hbl : β < δ),
                  cast (hS'.succ_eq hsb) (S'.map hsb le_rfl (stepDown (cast h_top x))) =
                    F.map (S'.map hbl.le le_rfl) (cast h_top x) := by
                rintro d rfl hsb hbl
                have hβd : β ≤ d := Order.lt_succ_iff.1 hbl
                have hstep := hstep_succ d rfl (cast h_top x)
                have hss := hS'.map_succ_succ hβd le_rfl (stepDown (cast h_top x))
                change cast (hS'.succ_eq (Order.succ_le_succ hβd))
                    (S'.map (Order.succ_le_succ hβd) le_rfl (stepDown (cast h_top x))) =
                    F.map (S'.map hβd (Order.le_succ d)) (cast (hS'.succ_eq le_rfl) (stepDown (cast h_top x))) at hss
                have hstep' : cast (hS'.succ_eq le_rfl) (stepDown (cast h_top x)) =
                    F.map (S'.map (Order.le_succ d) le_rfl) (cast h_top x) := by
                  simpa using hstep
                rw [hstep', ← F.map_comp_apply] at hss
                have hcomp_s : S'.map hβd (Order.le_succ d) ∘ S'.map (Order.le_succ d) le_rfl =
                    S'.map hbl.le le_rfl :=
                  funext fun z => (hS'.map_comp hβd (Order.le_succ d) le_rfl z).symm
                rw [hcomp_s] at hss
                exact hss
              exact hcase_succ δ' hδ' hsβ hβlt
            · have hsβ_lt : Order.succ β < δ := hlim.succ_lt hβlt
              have hlim_step := hstep_limit hlim (Order.succ β) hsβ_lt (cast h_top x)
              have hss := hS'.map_succ_succ (Order.le_succ β) (hlim.succ_lt hsβ_lt).le
                (cast (hS'.succ_eq (hlim.succ_lt hsβ_lt).le).symm (F.map (S'.map hsβ_lt.le le_rfl) (cast h_top x)))
              rw [← hlim_step] at hss
              rw [cast_cast_symm, ← F.map_comp_apply] at hss
              have hcomp_s : S'.map (Order.le_succ β) hsβ_lt.le ∘ S'.map hsβ_lt.le le_rfl =
                  S'.map hβlt.le le_rfl :=
                funext fun z => (hS'.map_comp (Order.le_succ β) hsβ_lt.le le_rfl z).symm
              rw [hcomp_s] at hss
              exact hss
        · have hsd : Order.succ δ ≤ α' := Order.succ_le_iff.2 hlt
          rw [hmap_le (Order.succ_le_succ hβδ) hsd x]
          have hmap_fn : map hβδ (Order.le_succ δ |>.trans hδα) =
              fun z => cast (h_le (hβδ.trans hδα')).symm (S'.map hβδ hδα' (cast (h_le hδα') z)) :=
            funext fun z => hmap_le hβδ hδα' z
          rw [hmap_fn]
          have hss := hS'.map_succ_succ hβδ hsd (cast (h_le hsd) x)
          have hc : cast (hS'.succ_eq hsd) (cast (h_le hsd) x) =
              cast (congrArg F.obj (h_le hδα')) (cast (h_succ_eq hδα) x) := by
            rw [cast_trans_eq, cast_trans_eq]
          rw [hc] at hss
          have hF := cast_F_map (h_le hδα').symm (h_le (hβδ.trans hδα')).symm
            (S'.map hβδ hδα')
            (fun z => cast (h_le (hβδ.trans hδα')).symm (S'.map hβδ hδα' (cast (h_le hδα') z)))
            (fun z => by rw [cast_symm_cast])
            (cast (congrArg F.obj (h_le hδα')) (cast (h_succ_eq hδα) x))
          have h_l : cast (h_succ_eq ((Order.succ_le_succ hβδ).trans hδα))
              (cast (h_le ((Order.succ_le_succ hβδ).trans hsd)).symm
                (S'.map (Order.succ_le_succ hβδ) hsd (cast (h_le hsd) x))) =
              cast (congrArg F.obj (h_le (hβδ.trans hδα')).symm)
                (cast (hS'.succ_eq ((Order.succ_le_succ hβδ).trans hsd))
                  (S'.map (Order.succ_le_succ hβδ) hsd (cast (h_le hsd) x))) := by
            rw [cast_trans_eq, cast_trans_eq]
          rw [h_l, hss]
          rw [cast_symm_cast] at hF
          exact hF
      · dsimp only [S_next]
        intro l hl hlα
        have hl' : l ≤ α' := by
          rcases lt_or_eq_of_le hlα with hlt | heq
          · exact Order.lt_succ_iff.1 hlt
          · exact absurd hl (heq ▸ Order.not_isSuccLimit_succ α')
        rw [h_le hl', hS'.limit_eq hl hl']
        have hT : ∀ i : l.ToType, S'.obj i.toOrd.1 = obj i.toOrd.1 :=
          fun i => (h_le (i.toOrd.2.le.trans hl')).symm
        have hCompat : ∀ (t₁ : (i : l.ToType) → S'.obj i.toOrd.1)
            (t₂ : (i : l.ToType) → obj i.toOrd.1),
            (∀ i, cast (hT i) (t₁ i) = t₂ i) →
              ((∀ i j (hij : i.toOrd.1 ≤ j.toOrd.1), S'.map hij (j.toOrd.2.le.trans hl') (t₁ j) = t₁ i) ↔
               (∀ i j (hij : i.toOrd.1 ≤ j.toOrd.1), map hij (j.toOrd.2.le.trans hlα) (t₂ j) = t₂ i)) := by
          intro t₁ t₂ ht
          constructor
          · intro hc i j hij
            rw [hmap_le hij (j.toOrd.2.le.trans hl')]
            rw [← ht j, ← ht i]
            have : cast (h_le (j.toOrd.2.le.trans hl')) (cast (hT j) (t₁ j)) = t₁ j := by grind
            rw [this, hc i j hij]
          · intro hc i j hij
            have h := hc i j hij
            rw [hmap_le hij (j.toOrd.2.le.trans hl'), ← ht j, ← ht i] at h
            have h1 : cast (h_le (j.toOrd.2.le.trans hl')) (cast (hT j) (t₁ j)) = t₁ j := by grind
            rw [h1] at h
            exact cast_injective (hT i) (by grind)
        exact subtype_pi_eq hT hCompat
      · dsimp only [S_next]
        intro l hl hlα i x
        have hl' : l ≤ α' := by
          rcases lt_or_eq_of_le hlα with hlt | heq
          · exact Order.lt_succ_iff.1 hlt
          · exact absurd hl (heq ▸ Order.not_isSuccLimit_succ α')
        rw [hmap_le i.toOrd.2.le hl']
        have hlp := hS'.limit_proj hl hl' i (cast (h_le hl') x)
        have hT : ∀ i : l.ToType, S'.obj i.toOrd.1 = obj i.toOrd.1 :=
          fun i => (h_le (i.toOrd.2.le.trans hl')).symm
        have hCompat : ∀ (t₁ : (i : l.ToType) → S'.obj i.toOrd.1)
            (t₂ : (i : l.ToType) → obj i.toOrd.1),
            (∀ i, cast (hT i) (t₁ i) = t₂ i) →
              ((∀ i j (hij : i.toOrd.1 ≤ j.toOrd.1), S'.map hij (j.toOrd.2.le.trans hl') (t₁ j) = t₁ i) ↔
               (∀ i j (hij : i.toOrd.1 ≤ j.toOrd.1), map hij (j.toOrd.2.le.trans hlα) (t₂ j) = t₂ i)) := by
          intro t₁ t₂ ht
          constructor
          · intro hc i j hij
            rw [hmap_le hij (j.toOrd.2.le.trans hl'), ← ht j, ← ht i]
            have : cast (h_le (j.toOrd.2.le.trans hl')) (cast (hT j) (t₁ j)) = t₁ j := by grind
            rw [this, hc i j hij]
          · intro hc i j hij
            have h := hc i j hij
            rw [hmap_le hij (j.toOrd.2.le.trans hl'), ← ht j, ← ht i] at h
            have h1 : cast (h_le (j.toOrd.2.le.trans hl')) (cast (hT j) (t₁ j)) = t₁ j := by grind
            rw [h1] at h
            exact cast_injective (hT i) (by grind)
        have hEqLim := subtype_pi_eq hT hCompat
        have hcp := cast_limit_proj hT hEqLim hCompat (cast (hS'.limit_eq hl hl') (cast (h_le hl') x)) i
        rw [← hlp] at hcp
        rw [cast_trans_eq, cast_trans_eq] at hcp
        exact hcp
    · -- Limit case α
      let l := α
      have hl' : Order.IsSuccLimit l := hl
      let S_of : ∀ (β : Ordinal.{0}), β < l → SeqPrefix F β :=
        fun β hβ => Classical.choose (IH β hβ)
      have hV_of : ∀ (β : Ordinal.{0}) (hβ : β < l), IsValidSeq F β (S_of β hβ) :=
        fun β hβ => Classical.choose_spec (IH β hβ)
      have hobj_agree : ∀ {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < l),
          (S_of γ hγ).obj β = (S_of β (hβγ.trans_lt hγ)).obj β :=
        fun hβγ hγ => (agree_on_prefix (hV_of _ hγ) (hV_of _ (hβγ.trans_lt hγ)) _ hβγ le_rfl).1
      have hmap_agree : ∀ {β γ δ : Ordinal.{0}} (hβγ : β ≤ γ) (hγδ : γ ≤ δ) (hδ : δ < l)
          (x : (S_of δ hδ).obj γ),
          cast (agree_on_prefix (hV_of _ hδ) (hV_of _ (hγδ.trans_lt hδ)) _
            (hβγ.trans hγδ) hβγ).1 ((S_of δ hδ).map hβγ hγδ x) =
            (S_of γ (hγδ.trans_lt hδ)).map hβγ le_rfl (cast (hobj_agree hγδ hδ) x) :=
        fun hβγ hγδ hδ x =>
          (agree_on_prefix (hV_of _ hδ) (hV_of _ (hγδ.trans_lt hδ)) _ hγδ le_rfl).2 _ hβγ
            (agree_on_prefix (hV_of _ hδ) (hV_of _ (hγδ.trans_lt hδ)) _ (hβγ.trans hγδ) hβγ).1
            (hobj_agree hγδ hδ) x
      let limType : Type 1 :=
        { t : (i : l.ToType) → (S_of i.toOrd.1 i.toOrd.2).obj i.toOrd.1 //
          ∀ (i j : l.ToType) (hij : i.toOrd.1 ≤ j.toOrd.1),
            cast (hobj_agree hij j.toOrd.2) ((S_of j.toOrd.1 j.toOrd.2).map hij le_rfl (t j)) = t i }
      let obj : Ordinal.{0} → Type 1 := fun β =>
        if hβ : β < l then (S_of β hβ).obj β
        else if β = l then limType else PUnit.{2}
      have h_lt : ∀ {β} (hβ : β < l), obj β = (S_of β hβ).obj β := by
        intro β hβ; dsimp only [obj]; rw [dite_eq_left_of_eq_true (eq_true hβ)]
      have h_top : obj l = limType := by
        dsimp only [obj]
        rw [dite_eq_right_of_eq_false (eq_false (lt_irrefl l)), ite_eq_left_iff.2 fun h => absurd rfl h]
      let map : ∀ {β γ : Ordinal.{0}}, β ≤ γ → γ ≤ l → obj γ → obj β :=
        fun {β γ} hβγ hγl x =>
          if hγ : γ < l then
            have hβ : β < l := hβγ.trans_lt hγ
            cast (h_lt hβ).symm (cast (hobj_agree hβγ hγ) ((S_of γ hγ).map hβγ le_rfl (cast (h_lt hγ) x)))
          else
            have hγeq : γ = l := le_antisymm hγl (not_lt.1 hγ)
            if hβ : β < l then
              let iβ : l.ToType := Ordinal.ToType.mk ⟨β, hβ⟩
              have hiβ : iβ.toOrd = ⟨β, hβ⟩ := Subtype.ext (by simp [iβ])
              cast (h_lt hβ).symm
                (cast (congrArg (fun p : Set.Iio l => (S_of p.1 p.2).obj p.1) hiβ)
                  ((cast (hγeq ▸ h_top) x).1 iβ))
            else
              have hβeq : β = l := le_antisymm (hβγ.trans hγl) (not_lt.1 hβ)
              cast (by rw [hβeq, hγeq]) x
      have hmap_lt : ∀ {β γ} (hβγ : β ≤ γ) (hγ : γ < l) (x : obj γ),
          map hβγ hγ.le x =
            cast (h_lt (hβγ.trans_lt hγ)).symm (cast (hobj_agree hβγ hγ) ((S_of γ hγ).map hβγ le_rfl (cast (h_lt hγ) x))) := by
        intro β γ hβγ hγ x; dsimp only [map]; rw [dite_eq_left_of_eq_true (eq_true hγ)]
      have hmap_top_lt : ∀ {β} (hβ : β < l) (x : obj l),
          map hβ.le le_rfl x =
            cast (h_lt hβ).symm
              (cast (congrArg (fun p : Set.Iio l => (S_of p.1 p.2).obj p.1)
                (Subtype.ext (by simp) : (Ordinal.ToType.mk ⟨β, hβ⟩).toOrd = (⟨β, hβ⟩ : Set.Iio l)))
                ((cast h_top x).1 (Ordinal.ToType.mk ⟨β, hβ⟩))) := by
        intro β hβ x
        dsimp only [map]
        rw [dite_eq_right_of_eq_false (eq_false (lt_irrefl l)), dite_eq_left_of_eq_true (eq_true hβ)]
      have h_id : ∀ {β} (hβl : β ≤ l) (x : obj β), map le_rfl hβl x = x := by
        intro β hβl x
        by_cases hβ : β < l
        · rw [hmap_lt le_rfl hβ x, (hV_of β hβ).map_id le_rfl]
          rw [cast_trans_eq, cast_trans_eq]
          rfl
        · have hβeq : β = l := le_antisymm hβl (not_lt.1 hβ)
          subst hβeq
          dsimp only [map]
          rw [dite_eq_right_of_eq_false (eq_false (lt_irrefl l)),
              dite_eq_right_of_eq_false (eq_false (lt_irrefl l))]
          rfl
      have h_comp : ∀ {β γ δ} (hβγ : β ≤ γ) (hγδ : γ ≤ δ) (hδl : δ ≤ l) (x : obj δ),
          map (hβγ.trans hγδ) hδl x = map hβγ (hγδ.trans hδl) (map hγδ hδl x) := by
        intro β γ δ hβγ hγδ hδl x
        by_cases hδ : δ < l
        · have hγ : γ < l := hγδ.trans_lt hδ
          have hβ : β < l := hβγ.trans_lt hγ
          rw [hmap_lt (hβγ.trans hγδ) hδ x, hmap_lt hγδ hδ x, hmap_lt hβγ hγ]
          rw [(hV_of δ hδ).map_comp hβγ hγδ le_rfl, cast_symm_cast]
          have hm := hmap_agree hβγ hγδ hδ ((S_of δ hδ).map hγδ le_rfl (cast (h_lt hδ) x))
          rw [← hm, cast_trans_eq, cast_trans_eq, cast_trans_eq]
        · have hδeq : δ = l := le_antisymm hδl (not_lt.1 hδ)
          subst hδeq
          by_cases hγ : γ < l
          · have hβ : β < l := hβγ.trans_lt hγ
            rw [hmap_top_lt hβ x, hmap_top_lt hγ x, hmap_lt hβγ hγ, cast_symm_cast]
            have hc := (cast h_top x).2 (Ordinal.ToType.mk ⟨β, hβ⟩) (Ordinal.ToType.mk ⟨γ, hγ⟩)
              (by simpa using hβγ)
            have hc_eval : ∀ (p₁ p₂ q₁ q₂ : Set.Iio l) (hle : p₁.1 ≤ p₂.1)
                (hqle : q₁.1 ≤ q₂.1)
                (hp₁ : p₁ = q₁) (hp₂ : p₂ = q₂)
                (a₁ : (S_of p₁.1 p₁.2).obj p₁.1) (a₂ : (S_of p₂.1 p₂.2).obj p₂.1),
                cast (hobj_agree hle p₂.2) ((S_of p₂.1 p₂.2).map hle le_rfl a₂) = a₁ →
                cast (congrArg (fun p : Set.Iio l => (S_of p.1 p.2).obj p.1) hp₁) a₁ =
                  cast (hobj_agree hqle q₂.2) ((S_of q₂.1 q₂.2).map hqle le_rfl
                    (cast (congrArg (fun p : Set.Iio l => (S_of p.1 p.2).obj p.1) hp₂) a₂)) := by
              rintro p₁ p₂ q₁ q₂ hle hqle rfl rfl a₁ a₂ h
              exact h.symm
            have hce := hc_eval (Ordinal.ToType.mk ⟨β, hβ⟩).toOrd (Ordinal.ToType.mk ⟨γ, hγ⟩).toOrd
              ⟨β, hβ⟩ ⟨γ, hγ⟩ (by simpa using hβγ) hβγ
              (Subtype.ext (by simp)) (Subtype.ext (by simp))
              ((cast h_top x).1 _) ((cast h_top x).1 _) hc
            exact congrArg (cast (h_lt hβ).symm) hce
          · have hγeq : γ = l := le_antisymm hγδ (not_lt.1 hγ)
            subst hγeq
            rw [h_id le_rfl x]
      have h_zero : obj 0 = PUnit.{2} := by
        have h0le : (0 : Ordinal.{0}) < l := hl'.bot_lt
        rw [h_lt h0le, (hV_of 0 h0le).zero_eq]
      have h_succ_eq : ∀ {δ}, Order.succ δ ≤ l → obj (Order.succ δ) = F.obj (obj δ) := by
        intro δ hδ
        have hsd : Order.succ δ < l := lt_of_le_of_ne hδ fun heq =>
          absurd hl' (heq ▸ Order.not_isSuccLimit_succ δ)
        have hδl : δ < l := (Order.lt_succ δ).trans hsd
        rw [h_lt hsd, h_lt hδl, (hV_of _ hsd).succ_eq le_rfl, hobj_agree (Order.le_succ δ) hsd]
      let S_lim : SeqPrefix F l := ⟨obj, map⟩
      refine ⟨S_lim, h_id, h_comp, h_zero, h_succ_eq, ?_, ?_, ?_⟩
      · dsimp only [S_lim]
        intro β δ hβδ hδl x
        have hsd : Order.succ δ < l := lt_of_le_of_ne hδl fun heq =>
          absurd hl' (heq ▸ Order.not_isSuccLimit_succ δ)
        have hδlt : δ < l := (Order.lt_succ δ).trans hsd
        have hβlt : β < l := hβδ.trans_lt hδlt
        have hsβ : Order.succ β < l := (Order.succ_le_succ hβδ).trans_lt hsd
        rw [hmap_lt (Order.succ_le_succ hβδ) hsd x]
        have hmap_fn : map hβδ (Order.le_succ δ |>.trans hδl) =
            fun z => cast (h_lt hβlt).symm (cast (hobj_agree hβδ hδlt)
              ((S_of δ hδlt).map hβδ le_rfl (cast (h_lt hδlt) z))) :=
          funext fun z => hmap_lt hβδ hδlt z
        rw [hmap_fn]
        have hss := (hV_of _ hsd).map_succ_succ hβδ le_rfl (cast (h_lt hsd) x)
        have hFm := cast_F_map (hobj_agree (Order.le_succ δ) hsd)
          (agree_on_prefix (hV_of _ hsd) (hV_of _ hδlt) _ (hβδ.trans (Order.le_succ δ)) hβδ).1
          ((S_of _ hsd).map hβδ (Order.le_succ δ))
          ((S_of _ hδlt).map hβδ le_rfl)
          (fun z => hmap_agree hβδ (Order.le_succ δ) hsd z)
          (cast ((hV_of _ hsd).succ_eq le_rfl) (cast (h_lt hsd) x))
        have hF2 := cast_F_map (h_lt hδlt).symm
          ((hobj_agree hβδ hδlt).trans (h_lt hβlt).symm)
          ((S_of _ hδlt).map hβδ le_rfl)
          (fun z => cast (h_lt hβlt).symm (cast (hobj_agree hβδ hδlt)
            ((S_of _ hδlt).map hβδ le_rfl (cast (h_lt hδlt) z))))
          (fun z => by rw [cast_symm_cast, cast_trans_eq])
          (cast (congrArg F.obj (hobj_agree (Order.le_succ δ) hsd))
            (cast ((hV_of _ hsd).succ_eq le_rfl) (cast (h_lt hsd) x)))
        rw [← hss] at hFm
        have h_lhs_c : cast (h_succ_eq ((Order.succ_le_succ hβδ).trans hδl))
            (cast (h_lt hsβ).symm (cast (hobj_agree (Order.succ_le_succ hβδ) hsd)
              ((S_of _ hsd).map (Order.succ_le_succ hβδ) le_rfl (cast (h_lt hsd) x)))) =
            cast (congrArg F.obj ((hobj_agree hβδ hδlt).trans (h_lt hβlt).symm))
              (cast (congrArg F.obj (agree_on_prefix (hV_of _ hsd) (hV_of _ hδlt) _
                (hβδ.trans (Order.le_succ δ)) hβδ).1)
                (cast ((hV_of _ hsd).succ_eq (Order.succ_le_succ hβδ))
                  ((S_of _ hsd).map (Order.succ_le_succ hβδ) le_rfl (cast (h_lt hsd) x)))) := by
          rw [cast_trans_eq, cast_trans_eq, cast_trans_eq, cast_trans_eq]
        rw [h_lhs_c, hFm, hF2, cast_trans_eq, cast_trans_eq, cast_trans_eq]
      · dsimp only [S_lim]
        intro l' hl'' hl'l
        rcases lt_or_eq_of_le hl'l with hlt | heq
        · rw [h_lt hlt, (hV_of l' hlt).limit_eq hl'' le_rfl]
          have hT : ∀ i : l'.ToType, (S_of l' hlt).obj i.toOrd.1 = obj i.toOrd.1 :=
            fun i => (hobj_agree i.toOrd.2.le hlt).trans (h_lt (i.toOrd.2.trans hlt)).symm
          have hCompat : ∀ (t₁ : (i : l'.ToType) → (S_of l' hlt).obj i.toOrd.1)
              (t₂ : (i : l'.ToType) → obj i.toOrd.1),
              (∀ i, cast (hT i) (t₁ i) = t₂ i) →
                ((∀ i j (hij : i.toOrd.1 ≤ j.toOrd.1), (S_of l' hlt).map hij j.toOrd.2.le (t₁ j) = t₁ i) ↔
                 (∀ i j (hij : i.toOrd.1 ≤ j.toOrd.1), map hij (j.toOrd.2.le.trans hl'l) (t₂ j) = t₂ i)) := by
            intro t₁ t₂ ht
            constructor
            · intro hc i j hij
              rw [hmap_lt hij (j.toOrd.2.trans hlt), ← ht j, ← ht i]
              rw [cast_trans_eq, cast_trans_eq]
              have hm := hmap_agree hij j.toOrd.2.le hlt (t₁ j)
              rw [← hm, cast_trans_eq, hc i j hij]
            · intro hc i j hij
              have h := hc i j hij
              rw [hmap_lt hij (j.toOrd.2.trans hlt), ← ht j, ← ht i] at h
              rw [cast_trans_eq, cast_trans_eq] at h
              have hm := hmap_agree hij j.toOrd.2.le hlt (t₁ j)
              rw [← hm, cast_trans_eq] at h
              have h' : cast (hT i) ((S_of l' hlt).map hij j.toOrd.2.le (t₁ j)) = cast (hT i) (t₁ i) := h
              exact cast_injective (hT i) h'
          exact subtype_pi_eq hT hCompat
        · subst heq
          rw [h_top]
          have hT : ∀ i : l.ToType, (S_of i.toOrd.1 i.toOrd.2).obj i.toOrd.1 = obj i.toOrd.1 :=
            fun i => (h_lt i.toOrd.2).symm
          have hCompat : ∀ (t₁ : (i : l.ToType) → (S_of i.toOrd.1 i.toOrd.2).obj i.toOrd.1)
              (t₂ : (i : l.ToType) → obj i.toOrd.1),
              (∀ i, cast (hT i) (t₁ i) = t₂ i) →
                ((∀ i j (hij : i.toOrd.1 ≤ j.toOrd.1),
                    cast (hobj_agree hij j.toOrd.2) ((S_of j.toOrd.1 j.toOrd.2).map hij le_rfl (t₁ j)) = t₁ i) ↔
                 (∀ i j (hij : i.toOrd.1 ≤ j.toOrd.1),
                    map hij (j.toOrd.2.le.trans le_rfl) (t₂ j) = t₂ i)) := by
            intro t₁ t₂ ht
            constructor
            · intro hc i j hij
              rw [hmap_lt hij j.toOrd.2, ← ht j, ← ht i, cast_symm_cast, hc i j hij]
            · intro hc i j hij
              have h := hc i j hij
              rw [hmap_lt hij j.toOrd.2, ← ht j, ← ht i, cast_symm_cast] at h
              exact cast_injective (hT i) h
          exact subtype_pi_eq hT hCompat
      · dsimp only [S_lim]
        intro l' hl'' hl'l i x
        rcases lt_or_eq_of_le hl'l with hlt | heq
        · rw [hmap_lt i.toOrd.2.le hlt]
          have hlp := (hV_of l' hlt).limit_proj hl'' le_rfl i (cast (h_lt hlt) x)
          have hT : ∀ i : l'.ToType, (S_of l' hlt).obj i.toOrd.1 = obj i.toOrd.1 :=
            fun i => (hobj_agree i.toOrd.2.le hlt).trans (h_lt (i.toOrd.2.trans hlt)).symm
          have hCompat : ∀ (t₁ : (i : l'.ToType) → (S_of l' hlt).obj i.toOrd.1)
              (t₂ : (i : l'.ToType) → obj i.toOrd.1),
              (∀ i, cast (hT i) (t₁ i) = t₂ i) →
                ((∀ i j (hij : i.toOrd.1 ≤ j.toOrd.1), (S_of l' hlt).map hij j.toOrd.2.le (t₁ j) = t₁ i) ↔
                 (∀ i j (hij : i.toOrd.1 ≤ j.toOrd.1), map hij (j.toOrd.2.le.trans hl'l) (t₂ j) = t₂ i)) := by
            intro t₁ t₂ ht
            constructor
            · intro hc i j hij
              rw [hmap_lt hij (j.toOrd.2.trans hlt), ← ht j, ← ht i]
              rw [cast_trans_eq, cast_trans_eq]
              have hm := hmap_agree hij j.toOrd.2.le hlt (t₁ j)
              rw [← hm, cast_trans_eq, hc i j hij]
            · intro hc i j hij
              have h := hc i j hij
              rw [hmap_lt hij (j.toOrd.2.trans hlt), ← ht j, ← ht i] at h
              rw [cast_trans_eq, cast_trans_eq] at h
              have hm := hmap_agree hij j.toOrd.2.le hlt (t₁ j)
              rw [← hm, cast_trans_eq] at h
              have h' : cast (hT i) ((S_of l' hlt).map hij j.toOrd.2.le (t₁ j)) = cast (hT i) (t₁ i) := h
              exact cast_injective (hT i) h'
          have hEqLim := subtype_pi_eq hT hCompat
          have hcp := cast_limit_proj hT hEqLim hCompat
            (cast ((hV_of l' hlt).limit_eq hl'' le_rfl) (cast (h_lt hlt) x)) i
          rw [← hlp] at hcp
          rw [cast_trans_eq]
          rw [cast_trans_eq, cast_trans_eq] at hcp
          exact hcp
        · subst heq
          rw [hmap_top_lt i.toOrd.2 x]
          have hT : ∀ i : l.ToType, (S_of i.toOrd.1 i.toOrd.2).obj i.toOrd.1 = obj i.toOrd.1 :=
            fun i => (h_lt i.toOrd.2).symm
          have hCompat : ∀ (t₁ : (i : l.ToType) → (S_of i.toOrd.1 i.toOrd.2).obj i.toOrd.1)
              (t₂ : (i : l.ToType) → obj i.toOrd.1),
              (∀ i, cast (hT i) (t₁ i) = t₂ i) →
                ((∀ i j (hij : i.toOrd.1 ≤ j.toOrd.1),
                    cast (hobj_agree hij j.toOrd.2) ((S_of j.toOrd.1 j.toOrd.2).map hij le_rfl (t₁ j)) = t₁ i) ↔
                 (∀ i j (hij : i.toOrd.1 ≤ j.toOrd.1),
                    map hij (j.toOrd.2.le.trans le_rfl) (t₂ j) = t₂ i)) := by
            intro t₁ t₂ ht
            constructor
            · intro hc i j hij
              rw [hmap_lt hij j.toOrd.2, ← ht j, ← ht i, cast_symm_cast, hc i j hij]
            · intro hc i j hij
              have h := hc i j hij
              rw [hmap_lt hij j.toOrd.2, ← ht j, ← ht i, cast_symm_cast] at h
              exact cast_injective (hT i) h
          have hEqLim := subtype_pi_eq hT hCompat
          have hcp := cast_limit_proj hT hEqLim hCompat (cast h_top x) i
          have hmk : Ordinal.ToType.mk ⟨i.toOrd.1, i.toOrd.2⟩ = i := by simp
          rw [← cast_trans_eq h_top hEqLim x, ← hcp, cast_trans_eq]
          have hc_id : ∀ (p : Ordinal.ToType l) (hp : p = i)
              (he : (S_of p.toOrd.1 p.toOrd.2).obj p.toOrd.1 = obj i.toOrd.1)
              (he' : (S_of i.toOrd.1 i.toOrd.2).obj i.toOrd.1 = obj i.toOrd.1),
              cast he ((cast h_top x).1 p) = cast he' ((cast h_top x).1 i) := by
            rintro p rfl he he'; rfl
          exact hc_id _ hmk _ _

private def seqPrefix (F : SetFunctor) (α : Ordinal.{0}) : SeqPrefix F α :=
  Classical.choose (exists_validSeq F α)

private theorem seqPrefix_valid (F : SetFunctor) (α : Ordinal.{0}) :
    IsValidSeq F α (seqPrefix F α) :=
  Classical.choose_spec (exists_validSeq F α)

end Construction

section PublicAPI

/-- Stage `α` of the terminal sequence of `F`. -/
def A (F : SetFunctor) (α : Ordinal.{0}) : Type 1 :=
  (seqPrefix F α).obj α

/-- Transition map `f_α^β : A F β → A F α` for `α ≤ β`. -/
def f {F : SetFunctor} {α β : Ordinal.{0}} (h : α ≤ β) (x : A F β) : A F α :=
  cast (agree_on_prefix (seqPrefix_valid F β) (seqPrefix_valid F α) α h le_rfl).1
    ((seqPrefix F β).map h le_rfl x)

@[simp]
theorem f_id {F : SetFunctor} {α : Ordinal.{0}} (x : A F α) :
    f (F := F) (le_refl α) x = x := by
  dsimp only [f]
  rw [(seqPrefix_valid F α).map_id le_rfl x]
  rfl

theorem f_comp {F : SetFunctor} {α β γ : Ordinal.{0}} (h₁ : α ≤ β) (h₂ : β ≤ γ) (x : A F γ) :
    f (F := F) (h₁.trans h₂) x = f h₁ (f h₂ x) := by
  dsimp only [f]
  rw [(seqPrefix_valid F γ).map_comp h₁ h₂ le_rfl x]
  have hm := (agree_on_prefix (seqPrefix_valid F γ) (seqPrefix_valid F β) β h₂ le_rfl).2
    α h₁ (agree_on_prefix (seqPrefix_valid F γ) (seqPrefix_valid F α) α (h₁.trans h₂) le_rfl |>.1.trans
      (agree_on_prefix (seqPrefix_valid F β) (seqPrefix_valid F α) α h₁ le_rfl).1.symm)
    (agree_on_prefix (seqPrefix_valid F γ) (seqPrefix_valid F β) β h₂ le_rfl).1
    ((seqPrefix F γ).map h₂ le_rfl x)
  grind

/-- Stage `0` equivalence `A F 0 ≃ PUnit.{2}`. -/
def zeroEquiv (F : SetFunctor) : A F 0 ≃ PUnit.{2} :=
  Equiv.cast (seqPrefix_valid F 0).zero_eq

/-- Stage `Order.succ α` equivalence `A F (Order.succ α) ≃ F.obj (A F α)`. -/
def succEquiv (F : SetFunctor) (α : Ordinal.{0}) : A F (Order.succ α) ≃ F.obj (A F α) :=
  Equiv.cast ((seqPrefix_valid F (Order.succ α)).succ_eq le_rfl |>.trans
    (congrArg F.obj (agree_on_prefix (seqPrefix_valid F (Order.succ α))
      (seqPrefix_valid F α) α (Order.le_succ α) le_rfl).1))

theorem succEquiv_f_succ {F : SetFunctor} {α β : Ordinal.{0}} (h : α ≤ β)
    (x : A F (Order.succ β)) :
    succEquiv F α (f (Order.succ_le_succ h) x) = F.map (f h) (succEquiv F β x) := by
  have h1 := (seqPrefix_valid F (Order.succ β)).map_succ_succ h le_rfl x
  have h_obj_succ := (agree_on_prefix (seqPrefix_valid F (Order.succ β))
    (seqPrefix_valid F (Order.succ α)) (Order.succ α) (Order.succ_le_succ h) le_rfl).1
  have h_obj_α := (agree_on_prefix (seqPrefix_valid F (Order.succ β))
    (seqPrefix_valid F α) α (h.trans (Order.le_succ β)) le_rfl).1
  have h_obj_β := (agree_on_prefix (seqPrefix_valid F (Order.succ β))
    (seqPrefix_valid F β) β (Order.le_succ β) le_rfl).1
  have h_obj_βα := (agree_on_prefix (seqPrefix_valid F β)
    (seqPrefix_valid F α) α h le_rfl).1
  have h_α_eq := (agree_on_prefix (seqPrefix_valid F (Order.succ α))
    (seqPrefix_valid F α) α (Order.le_succ α) le_rfl).1
  have hm := cast_F_map h_obj_β h_obj_α
    ((seqPrefix F (Order.succ β)).map h (Order.le_succ β))
    (f (F := F) h)
    (fun z => by
      dsimp only [f]
      have ha := (agree_on_prefix (seqPrefix_valid F (Order.succ β))
        (seqPrefix_valid F β) β (Order.le_succ β) le_rfl).2 α h
        (h_obj_α.trans h_obj_βα.symm) h_obj_β z
      rw [← ha]
      exact (cast_trans_eq (h_obj_α.trans h_obj_βα.symm) h_obj_βα _).symm)
    (cast ((seqPrefix_valid F (Order.succ β)).succ_eq le_rfl) x)
  rw [← h1] at hm
  change cast ((seqPrefix_valid F (Order.succ α)).succ_eq le_rfl |>.trans (congrArg F.obj h_α_eq))
      (cast h_obj_succ ((seqPrefix F (Order.succ β)).map (Order.succ_le_succ h) le_rfl x)) =
      F.map (f h) (cast ((seqPrefix_valid F (Order.succ β)).succ_eq le_rfl |>.trans (congrArg F.obj h_obj_β)) x)
  have hc_lhs : cast ((seqPrefix_valid F (Order.succ α)).succ_eq le_rfl |>.trans (congrArg F.obj h_α_eq))
      (cast h_obj_succ ((seqPrefix F (Order.succ β)).map (Order.succ_le_succ h) le_rfl x)) =
      cast (congrArg F.obj h_obj_α)
        (cast ((seqPrefix_valid F (Order.succ β)).succ_eq (Order.succ_le_succ h))
          ((seqPrefix F (Order.succ β)).map (Order.succ_le_succ h) le_rfl x)) := by
    rw [cast_trans_eq, cast_trans_eq]
  rw [hc_lhs, hm]
  congr 1
  exact cast_trans_eq ((seqPrefix_valid F (Order.succ β)).succ_eq le_rfl)
    (congrArg F.obj h_obj_β) x

private theorem limit_compat_public (F : SetFunctor) {l : Ordinal.{0}} :
    let hT : ∀ i : l.ToType, (seqPrefix F l).obj i.toOrd.1 = A F i.toOrd.1 :=
      fun i => (agree_on_prefix (seqPrefix_valid F l) (seqPrefix_valid F i.toOrd.1)
        i.toOrd.1 i.toOrd.2.le le_rfl).1
    ∀ (t₁ : (i : l.ToType) → (seqPrefix F l).obj i.toOrd.1)
      (t₂ : (i : l.ToType) → A F i.toOrd.1),
      (∀ i, cast (hT i) (t₁ i) = t₂ i) →
        ((∀ i j (hij : i.toOrd.1 ≤ j.toOrd.1),
            (seqPrefix F l).map hij j.toOrd.2.le (t₁ j) = t₁ i) ↔
         (∀ i j (hij : i.toOrd.1 ≤ j.toOrd.1), f hij (t₂ j) = t₂ i)) := by
  intro hT t₁ t₂ ht
  constructor
  · intro hc i j hij
    have hj_eq := (agree_on_prefix (seqPrefix_valid F l) (seqPrefix_valid F j.toOrd.1)
      j.toOrd.1 j.toOrd.2.le le_rfl).1
    have hij_eq := (agree_on_prefix (seqPrefix_valid F j.toOrd.1) (seqPrefix_valid F i.toOrd.1)
      i.toOrd.1 hij le_rfl).1
    have hi_eq : (seqPrefix F l).obj i.toOrd.1 = (seqPrefix F j.toOrd.1).obj i.toOrd.1 :=
      (hT i).trans hij_eq.symm
    have ha := (agree_on_prefix (seqPrefix_valid F l) (seqPrefix_valid F j.toOrd.1)
      j.toOrd.1 j.toOrd.2.le le_rfl).2 i.toOrd.1 hij hi_eq hj_eq (t₁ j)
    dsimp only [f]
    have hci : cast (hT i) ((seqPrefix F l).map hij j.toOrd.2.le (t₁ j)) = t₂ i := by
      rw [hc i j hij, ht i]
    rw [← hci]
    have hct : cast (hT i) ((seqPrefix F l).map hij j.toOrd.2.le (t₁ j)) =
        cast hij_eq (cast hi_eq ((seqPrefix F l).map hij j.toOrd.2.le (t₁ j))) :=
      (cast_trans_eq hi_eq hij_eq _).symm
    rw [hct, ha]
    have htj : cast hj_eq (t₁ j) = t₂ j := ht j
    rw [htj]
    rfl
  · intro hc i j hij
    have hj_eq := (agree_on_prefix (seqPrefix_valid F l) (seqPrefix_valid F j.toOrd.1)
      j.toOrd.1 j.toOrd.2.le le_rfl).1
    have hij_eq := (agree_on_prefix (seqPrefix_valid F j.toOrd.1) (seqPrefix_valid F i.toOrd.1)
      i.toOrd.1 hij le_rfl).1
    have hi_eq : (seqPrefix F l).obj i.toOrd.1 = (seqPrefix F j.toOrd.1).obj i.toOrd.1 :=
      (hT i).trans hij_eq.symm
    have ha := (agree_on_prefix (seqPrefix_valid F l) (seqPrefix_valid F j.toOrd.1)
      j.toOrd.1 j.toOrd.2.le le_rfl).2 i.toOrd.1 hij hi_eq hj_eq (t₁ j)
    have h := hc i j hij
    dsimp only [f] at h
    apply cast_injective (hT i)
    rw [ht i, ← h]
    have htj : cast hj_eq (t₁ j) = t₂ j := ht j
    rw [← htj, ← ha]
    exact (cast_trans_eq hi_eq hij_eq _).symm

/-- Limit stage equivalence `A F l ≃ lim_{i < l} A F i`. -/
def limitEquiv (F : SetFunctor) {l : Ordinal.{0}} (hl : Order.IsSuccLimit l) :
    A F l ≃ { t : (i : l.ToType) → A F i.toOrd.1 //
      ∀ (i j : l.ToType) (hij : i.toOrd.1 ≤ j.toOrd.1), f hij (t j) = t i } :=
  let hT : ∀ i : l.ToType, (seqPrefix F l).obj i.toOrd.1 = A F i.toOrd.1 :=
    fun i => (agree_on_prefix (seqPrefix_valid F l) (seqPrefix_valid F i.toOrd.1)
      i.toOrd.1 i.toOrd.2.le le_rfl).1
  Equiv.cast ((seqPrefix_valid F l).limit_eq hl le_rfl |>.trans (subtype_pi_eq hT (limit_compat_public F)))

theorem limitEquiv_proj (F : SetFunctor) {l : Ordinal.{0}} (hl : Order.IsSuccLimit l)
    (i : l.ToType) (x : A F l) :
    (limitEquiv F hl x).1 i = f i.toOrd.2.le x := by
  have hlp := (seqPrefix_valid F l).limit_proj hl le_rfl i x
  have hT : ∀ i : l.ToType, (seqPrefix F l).obj i.toOrd.1 = A F i.toOrd.1 :=
    fun i => (agree_on_prefix (seqPrefix_valid F l) (seqPrefix_valid F i.toOrd.1)
      i.toOrd.1 i.toOrd.2.le le_rfl).1
  have hEqLim := subtype_pi_eq hT (limit_compat_public F)
  have hcp := cast_limit_proj hT hEqLim (limit_compat_public F)
    (cast ((seqPrefix_valid F l).limit_eq hl le_rfl) x) i
  rw [← hlp] at hcp
  change (cast ((seqPrefix_valid F l).limit_eq hl le_rfl |>.trans hEqLim) x).1 i =
    cast (hT i) ((seqPrefix F l).map i.toOrd.2.le le_rfl x)
  rw [← cast_trans_eq ((seqPrefix_valid F l).limit_eq hl le_rfl) hEqLim x, ← hcp]

end PublicAPI

end TerminalSeq.Abstract
