import TerminalSeq.AccessibleAndMonic
import TerminalSeq.Step1_BoundedPowerset

/-!
# Step 2: General Stabilization Order `κ + θ`

For any infinite regular cardinals `θ ≤ κ`, proves that the terminal sequence of
`G_{κ,θ}` stabilizes at ordinal `κ.ord + θ.ord` and at no smaller ordinal:
1. `stabilizesAt_upward`: stabilization persists upward; combined with Step 1, no ordinal `< κ.ord`
   can stabilize.
2. Subobjects `B_β = im(f_κ^{κ+β}) ⊆ A_κ` satisfy `B_0 = univ`, antitone inclusion,
   successor recursion via `G_{κ,θ}(B_β)`, and limit intersection `⋂_{γ < l} B_γ`.
3. Rank delay operators `σ` (successor delay) and `τ_μ` (cofinal limit delay along `μ = cof l`)
   realize every rank `α < θ.ord`, showing `¬ Bijective (f_δ^{δ+1})` for `δ < κ.ord + θ.ord`.
4. Regularity of `θ` closes `B_{θ+1} = B_θ`, yielding `Bijective (f_{κ+θ}^{κ+θ+1})`.
-/

noncomputable section

open Classical Ordinal Cardinal

namespace TerminalSeq

/-! ### 1. Stabilization Predicates (via `TerminalSeq.Abstract`) and Lower Bound -/

/-- The terminal sequence stabilizes at ordinal `γ` iff `f_γ^{γ+1} : A_{γ+1} → A_γ` is bijective. -/
abbrev StabilizesAt (κ θ : Cardinal.{0}) (γ : Ordinal.{0}) : Prop :=
  Abstract.StabilizesAt (GFunctor κ θ) γ

/-- Exact stabilization order: stabilizes at `γ` and at no strictly smaller ordinal. -/
abbrev Stabilizes (κ θ : Cardinal.{0}) (γ : Ordinal.{0}) : Prop :=
  Abstract.Stabilizes (GFunctor κ θ) γ

theorem not_stabilizesAt_lt_kappa (κ θ : Cardinal.{0}) (hκ : κ.IsRegular)
    {δ : Ordinal.{0}} (hδ : δ < κ.ord) : ¬ StabilizesAt κ θ δ := by
  intro hstab
  obtain ⟨_, hκ_stab⟩ := Abstract.stabilizesAt_upward hstab hδ.le
  obtain ⟨b_κ, hb_κ⟩ := step1_not_surjective_kappa κ θ hκ
  obtain ⟨x, hx⟩ := hκ_stab.surjective b_κ
  exact hb_κ x hx

/-! ### 2. Subobjects `B_β` and Recursive Characterization -/

private theorem ord_le_add_right (a b : Ordinal.{0}) : a ≤ a + b :=
  le_add_of_nonneg_right bot_le

/-- Image `B_β = im(f_{κ}^{κ+β}) ⊆ A_κ` for `β : Ordinal.{0}`. -/
def B (κ θ : Cardinal.{0}) (β : Ordinal.{0}) : Set (A κ θ κ.ord) :=
  Set.range (f (κ := κ) (θ := θ) (ord_le_add_right κ.ord β))

theorem B_zero (κ θ : Cardinal.{0}) : B κ θ 0 = Set.univ := by
  ext x
  simp only [B, Set.mem_univ, iff_true]
  have h0 : κ.ord + 0 = κ.ord := add_zero κ.ord
  let y : A κ θ (κ.ord + 0) := cast (congrArg (A κ θ) h0.symm) x
  refine ⟨y, ?_⟩
  have hrew : ∀ (o : Ordinal.{0}) (ho : κ.ord ≤ o) (heq : o = κ.ord) (z : A κ θ κ.ord),
      f (κ := κ) (θ := θ) ho (cast (congrArg (A κ θ) heq.symm) z) = z := by
    rintro o _ rfl z
    exact f_id z
  exact hrew (κ.ord + 0) (ord_le_add_right κ.ord 0) h0 x

theorem B_antitone (κ θ : Cardinal.{0}) {β γ : Ordinal.{0}} (h : β ≤ γ) :
    B κ θ γ ⊆ B κ θ β := by
  intro c hc
  rcases hc with ⟨y, rfl⟩
  have hle : κ.ord + β ≤ κ.ord + γ := add_le_add_right h κ.ord
  refine ⟨f hle y, ?_⟩
  exact (f_comp (ord_le_add_right κ.ord β) hle y).symm

theorem B_nonempty {κ θ : Cardinal.{0}} (hκ : κ.IsRegular) (β : Ordinal.{0}) :
    (B κ θ β).Nonempty := by
  obtain ⟨y⟩ := nonempty_A (κ := κ) (θ := θ) hκ.pos (κ.ord + β)
  exact ⟨f (ord_le_add_right κ.ord β) y, y, rfl⟩

/-- Subfunctor predicate `u ∈ G_{κ,θ}(P)` for `P : Set X`. -/
def inSubFunctor {κ θ : Cardinal.{0}} {X : Type 1} (P : Set X) : G κ θ X → Prop
  | .inl ⟨S, _⟩ => S ⊆ P
  | .inr ⟨μ, q⟩ => ∃ b : μ.1.ord.ToType → X,
      (∀ i, b i ∈ P) ∧ Quotient.mk (ltDiffSetoid X μ) b = q

theorem inSubFunctor_iff_mem_range {κ θ : Cardinal.{0}} {X : Type 1}
    (P : Set X) (u : G κ θ X) :
    inSubFunctor P u ↔ u ∈ Set.range (G.map (κ := κ) (θ := θ) (Subtype.val : ↥P → X)) := by
  constructor
  · intro hu
    cases u with
    | inl S =>
        rcases S with ⟨S, hS⟩
        dsimp only [inSubFunctor] at hu
        let S' : Set ↥P := { y | y.1 ∈ S }
        have hcard : Cardinal.mk S' = Cardinal.mk S :=
          Cardinal.mk_congr
            { toFun := fun y => ⟨y.1.1, y.2⟩
              invFun := fun x => ⟨⟨x.1, hu x.2⟩, x.2⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
        refine ⟨.inl ⟨S', hcard ▸ hS⟩, ?_⟩
        dsimp only [G.map]
        congr 1
        apply Subtype.ext
        ext x
        simp only [S', Set.mem_image, Set.mem_ofPred_eq, Subtype.exists]
        exact ⟨fun ⟨_, hxP, hxS, rfl⟩ => hxS, fun hxS => ⟨x, hu hxS, hxS, rfl⟩⟩
    | inr p =>
        rcases p with ⟨μ, q⟩
        dsimp only [inSubFunctor] at hu
        rcases hu with ⟨b, hbP, rfl⟩
        let b' : μ.1.ord.ToType → ↥P := fun i => ⟨b i, hbP i⟩
        refine ⟨.inr ⟨μ, Quotient.mk (ltDiffSetoid (↥P) μ) b'⟩, ?_⟩
        rfl
  · rintro ⟨v, rfl⟩
    cases v with
    | inl S =>
        rcases S with ⟨S, hS⟩
        rintro _ ⟨y, _, rfl⟩
        exact y.2
    | inr p =>
        rcases p with ⟨μ, q⟩
        induction q using Quotient.ind with
        | _ a =>
            exact ⟨Subtype.val ∘ a, fun i => (a i).2, rfl⟩

private theorem add_succ_ord (α β : Ordinal.{0}) :
    α + Order.succ β = Order.succ (α + β) := by
  rw [Order.succ_eq_add_one, Order.succ_eq_add_one, add_assoc]

theorem B_succ (κ θ : Cardinal.{0}) (β : Ordinal.{0}) :
    B κ θ (Order.succ β) =
      (f (κ := κ) (θ := θ) (Order.le_succ κ.ord)) ''
        ((succEquiv κ θ κ.ord) ⁻¹' { u | inSubFunctor (B κ θ β) u }) := by
  have hadd : κ.ord + Order.succ β = Order.succ (κ.ord + β) := add_succ_ord κ.ord β
  have hκβ : κ.ord ≤ κ.ord + β := ord_le_add_right κ.ord β
  have hκ_succ : κ.ord ≤ κ.ord + Order.succ β := ord_le_add_right κ.ord (Order.succ β)
  ext c
  constructor
  · intro hc
    rw [B] at hc
    rcases hc with ⟨y, rfl⟩
    let y' : A κ θ (Order.succ (κ.ord + β)) := cast (congrArg (A κ θ) hadd) y
    have hproj_y : f (κ := κ) (θ := θ) hκ_succ y =
        f (κ := κ) (θ := θ) (Order.le_succ κ.ord)
          (f (Order.succ_le_succ hκβ) y') := by
      have hrew : ∀ (o : Ordinal.{0}) (ho : κ.ord ≤ o) (heq : o = Order.succ (κ.ord + β))
          (z : A κ θ o),
          f (κ := κ) (θ := θ) ho z =
            f (Order.le_succ κ.ord)
              (f (Order.succ_le_succ hκβ) (cast (congrArg (A κ θ) heq) z)) := by
        rintro o ho rfl z
        exact f_comp (Order.le_succ κ.ord) (Order.succ_le_succ hκβ) z
      exact hrew (κ.ord + Order.succ β) hκ_succ hadd y
    rw [hproj_y]
    refine ⟨f (Order.succ_le_succ hκβ) y', ?_, rfl⟩
    change inSubFunctor (B κ θ β) (succEquiv κ θ κ.ord (f (Order.succ_le_succ hκβ) y'))
    rw [succEquiv_f_succ hκβ y', inSubFunctor_iff_mem_range]
    let g_fact : A κ θ (κ.ord + β) → ↥(B κ θ β) :=
      fun z => ⟨f hκβ z, z, rfl⟩
    refine ⟨G.map g_fact (succEquiv κ θ (κ.ord + β) y'), ?_⟩
    rw [← G.map_comp]
    rfl
  · rintro ⟨w, hw, rfl⟩
    change inSubFunctor (B κ θ β) (succEquiv κ θ κ.ord w) at hw
    rw [inSubFunctor_iff_mem_range] at hw
    rcases hw with ⟨v, hv⟩
    have hsurj : Function.Surjective
        (fun z : A κ θ (κ.ord + β) => (⟨f hκβ z, z, rfl⟩ : ↥(B κ θ β))) := by
      rintro ⟨b, z, rfl⟩
      exact ⟨z, rfl⟩
    let liftB : ↥(B κ θ β) → A κ θ (κ.ord + β) := Function.surjInv hsurj
    have hliftB : ∀ b : ↥(B κ θ β), f hκβ (liftB b) = b.1 :=
      fun b => congrArg Subtype.val (Function.surjInv_eq hsurj b)
    let y' : A κ θ (Order.succ (κ.ord + β)) :=
      (succEquiv κ θ (κ.ord + β)).symm (G.map liftB v)
    let y : A κ θ (κ.ord + Order.succ β) := cast (congrArg (A κ θ) hadd.symm) y'
    rw [B]
    refine ⟨y, ?_⟩
    have hstep : f (Order.succ_le_succ hκβ) y' = w := by
      apply (succEquiv κ θ κ.ord).injective
      rw [succEquiv_f_succ hκβ y', Equiv.apply_symm_apply, ← G.map_comp, ← hv]
      have hfun : (f (κ := κ) (θ := θ) hκβ ∘ liftB) = Subtype.val := funext hliftB
      rw [hfun]
    have hrew : ∀ (o : Ordinal.{0}) (ho : κ.ord ≤ o) (heq : o = Order.succ (κ.ord + β))
        (z : A κ θ (Order.succ (κ.ord + β))),
        f (κ := κ) (θ := θ) ho (cast (congrArg (A κ θ) heq.symm) z) =
          f (Order.le_succ κ.ord) (f (Order.succ_le_succ hκβ) z) := by
      rintro o ho rfl z
      exact f_comp (Order.le_succ κ.ord) (Order.succ_le_succ hκβ) z
    rw [hrew (κ.ord + Order.succ β) hκ_succ hadd y', hstep]

theorem B_limit {κ θ : Cardinal.{0}} (hκ : κ.IsRegular) (hθ : θ ≤ κ)
    {l : Ordinal.{0}} (hl : Order.IsSuccLimit l) :
    B κ θ l = ⋂ (β : Ordinal.{0}) (_ : β < l), B κ θ β := by
  ext c
  constructor
  · intro hc
    simp only [Set.mem_iInter]
    intro β hβ
    exact B_antitone κ θ hβ.le hc
  · intro hc
    simp only [Set.mem_iInter, B, Set.mem_range] at hc
    have hlim : Order.IsSuccLimit (κ.ord + l) := Ordinal.isSuccLimit_add κ.ord hl
    let tFun (i : (κ.ord + l).ToType) : A κ θ i.toOrd.1 :=
      if hκi : κ.ord ≤ i.toOrd.1 then
        let β := i.toOrd.1 - κ.ord
        have hβ : β < l := Ordinal.sub_lt_of_lt_add i.toOrd.2 hl.bot_lt
        have hadd : κ.ord + β = i.toOrd.1 := Ordinal.add_sub_cancel_of_le hκi
        cast (congrArg (A κ θ) hadd) (Classical.choose (hc β hβ))
      else
        f (lt_of_not_ge hκi).le c
    have ht_ge : ∀ (i : (κ.ord + l).ToType) (hκi : κ.ord ≤ i.toOrd.1),
        f (κ := κ) (θ := θ) hκi (tFun i) = c := by
      intro i hκi
      dsimp only [tFun]
      rw [dite_eq_left_of_eq_true (eq_true hκi)]
      have hβ : i.toOrd.1 - κ.ord < l := Ordinal.sub_lt_of_lt_add i.toOrd.2 hl.bot_lt
      have hadd : κ.ord + (i.toOrd.1 - κ.ord) = i.toOrd.1 := Ordinal.add_sub_cancel_of_le hκi
      have hspec := Classical.choose_spec (hc (i.toOrd.1 - κ.ord) hβ)
      have hrew : ∀ (o : Ordinal.{0}) (ho : κ.ord ≤ o) (heq : κ.ord + (i.toOrd.1 - κ.ord) = o),
          f (κ := κ) (θ := θ) ho (cast (congrArg (A κ θ) heq)
            (Classical.choose (hc (i.toOrd.1 - κ.ord) hβ))) = c := by
        rintro o _ rfl
        exact hspec
      exact hrew i.toOrd.1 hκi hadd
    have ht_lt : ∀ (i : (κ.ord + l).ToType) (hiκ : i.toOrd.1 < κ.ord),
        tFun i = f (κ := κ) (θ := θ) hiκ.le c := by
      intro i hiκ
      dsimp only [tFun]
      exact dite_eq_right_of_eq_false (eq_false (not_le_of_gt hiκ))
    have hcompat : ∀ (i j : (κ.ord + l).ToType) (hij : i.toOrd.1 ≤ j.toOrd.1),
        f (κ := κ) (θ := θ) hij (tFun j) = tFun i := by
      intro i j hij
      by_cases hκi : κ.ord ≤ i.toOrd.1
      · have hκj : κ.ord ≤ j.toOrd.1 := hκi.trans hij
        apply tail_monic hκ hθ le_rfl hκi
        rw [← f_comp hκi hij (tFun j), ht_ge j hκj, ht_ge i hκi]
      · have hiκ : i.toOrd.1 < κ.ord := lt_of_not_ge hκi
        rw [ht_lt i hiκ]
        by_cases hκj : κ.ord ≤ j.toOrd.1
        · rw [f_comp hiκ.le hκj (tFun j), ht_ge j hκj]
        · have hjκ : j.toOrd.1 < κ.ord := lt_of_not_ge hκj
          rw [ht_lt j hjκ]
          exact (f_comp hij hjκ.le c).symm
    let y : A κ θ (κ.ord + l) := (limitEquiv κ θ hlim).symm ⟨tFun, hcompat⟩
    rw [B]
    refine ⟨y, ?_⟩
    have hκ_lt : κ.ord < κ.ord + l := lt_add_of_pos_right κ.ord hl.bot_lt
    let i₀ : (κ.ord + l).ToType := Ordinal.ToType.mk ⟨κ.ord, hκ_lt⟩
    have hi₀ : i₀.toOrd.1 = κ.ord := by simp [i₀]
    have hproj : f (κ := κ) (θ := θ) i₀.toOrd.2.le y = tFun i₀ := by
      have h := congrArg
        (fun t : { t : (j : (κ.ord + l).ToType) → A κ θ j.toOrd.1 // _ } => t.1 i₀)
        ((limitEquiv κ θ hlim).apply_symm_apply ⟨tFun, hcompat⟩)
      rw [limitEquiv_proj] at h
      exact h
    have hκi₀ : κ.ord ≤ i₀.toOrd.1 := hi₀.symm.le
    have hf_eq := ht_ge i₀ hκi₀
    rw [← hproj, ← f_comp hκi₀ i₀.toOrd.2.le y] at hf_eq
    exact hf_eq

/-! ### 3. Membership Criteria for `σ` and `τ_μ` and Rank Realization -/

private theorem singleton_card_lt_lift {X : Type 1} {κ : Cardinal.{0}} (hκ : κ.IsRegular)
    (x : X) : Cardinal.mk ({x} : Set X) < Cardinal.lift.{1, 0} κ := by
  have h1 : Cardinal.mk ({x} : Set X) = 1 := Cardinal.mk_singleton x
  rw [h1]
  have hlt : (1 : Cardinal.{1}) < Cardinal.aleph0 := Cardinal.one_lt_aleph0
  exact lt_of_lt_of_le hlt hκ.lift.aleph0_le

/-- Successor delay operator `σ : A_κ → A_κ`. -/
def sigma {κ θ : Cardinal.{0}} (hκ : κ.IsRegular) (x : A κ θ κ.ord) : A κ θ κ.ord :=
  f (κ := κ) (θ := θ) (Order.le_succ κ.ord)
    ((succEquiv κ θ κ.ord).symm (.inl ⟨{x}, singleton_card_lt_lift hκ x⟩))

/-- Limit delay operator `τ_μ : (μ → A_κ) → A_κ` for any regular `μ < θ`. -/
def tau {κ θ : Cardinal.{0}} (μ : RegBelow θ)
    (a : μ.1.ord.ToType → A κ θ κ.ord) : A κ θ κ.ord :=
  f (κ := κ) (θ := θ) (Order.le_succ κ.ord)
    ((succEquiv κ θ κ.ord).symm (.inr ⟨μ, Quotient.mk (ltDiffSetoid _ μ) a⟩))

theorem sigma_mem_B_succ {κ θ : Cardinal.{0}} (hκ : κ.IsRegular) (hθ : θ ≤ κ)
    (x : A κ θ κ.ord) (β : Ordinal.{0}) :
    sigma hκ x ∈ B κ θ (Order.succ β) ↔ x ∈ B κ θ β := by
  rw [B_succ]
  constructor
  · rintro ⟨w, hw, hweq⟩
    have hwinj := f_kappa_succ_injective hκ hθ hweq
    change inSubFunctor (B κ θ β) (succEquiv κ θ κ.ord w) at hw
    rw [hwinj, Equiv.apply_symm_apply] at hw
    exact hw (Set.mem_singleton x)
  · intro hx
    refine ⟨(succEquiv κ θ κ.ord).symm (.inl ⟨{x}, singleton_card_lt_lift hκ x⟩), ?_, rfl⟩
    change inSubFunctor (B κ θ β) _
    rw [Equiv.apply_symm_apply]
    intro z hz
    rw [Set.mem_singleton_iff.1 hz]
    exact hx

theorem tau_mem_B_succ {κ θ : Cardinal.{0}} (hκ : κ.IsRegular) (hθ : θ ≤ κ)
    (μ : RegBelow θ) (a : μ.1.ord.ToType → A κ θ κ.ord) (β : Ordinal.{0}) :
    tau (κ := κ) (θ := θ) μ a ∈ B κ θ (Order.succ β) ↔
      Cardinal.mk { i : μ.1.ord.ToType // a i ∉ B κ θ β } < μ.1 := by
  rw [B_succ]
  constructor
  · rintro ⟨w, hw, hweq⟩
    have hwinj := f_kappa_succ_injective hκ hθ hweq
    change inSubFunctor (B κ θ β) (succEquiv κ θ κ.ord w) at hw
    rw [hwinj, Equiv.apply_symm_apply] at hw
    rcases hw with ⟨b, hbB, hbq⟩
    have hdiff : ltDiff μ.1 b a := Quotient.exact hbq
    have hinj : Function.Injective (fun i : { i : μ.1.ord.ToType // a i ∉ B κ θ β } =>
        (⟨i.1, fun heq => i.2 (heq ▸ hbB i.1)⟩ : { i : μ.1.ord.ToType // b i ≠ a i })) := by
      intro i j hij
      exact Subtype.ext (congrArg (fun z : { i : μ.1.ord.ToType // b i ≠ a i } => z.1) hij)
    exact lt_of_le_of_lt (Cardinal.mk_le_of_injective hinj) hdiff
  · intro hsmall
    refine ⟨(succEquiv κ θ κ.ord).symm (.inr ⟨μ, Quotient.mk _ a⟩), ?_, rfl⟩
    change inSubFunctor (B κ θ β) _
    rw [Equiv.apply_symm_apply]
    obtain ⟨b₀, hb₀⟩ := B_nonempty (κ := κ) (θ := θ) hκ β
    let b : μ.1.ord.ToType → A κ θ κ.ord := fun i => if a i ∈ B κ θ β then a i else b₀
    refine ⟨b, fun i => ?_, ?_⟩
    · dsimp only [b]; split_ifs with hi
      · exact hi
      · exact hb₀
    · apply Quotient.sound
      change ltDiff μ.1 b a
      unfold ltDiff
      have hinj : Function.Injective (fun i : { i : μ.1.ord.ToType // b i ≠ a i } =>
          (⟨i.1, fun hi => i.2 (by simp [b, hi])⟩ :
            { i : μ.1.ord.ToType // a i ∉ B κ θ β })) := by
        intro i j hij
        exact Subtype.ext (by have h := congrArg Subtype.val hij; exact h)
      exact lt_of_le_of_lt (Cardinal.mk_le_of_injective hinj) hsmall

private theorem exists_cofinal_seq_limit {l : Ordinal.{0}} (_hl : Order.IsSuccLimit l) :
    ∃ c : l.cof.ord.ToType → Ordinal.{0},
      (∀ i, c i < l) ∧ (∀ β < l, ∃ i₀, ∀ j ≥ i₀, β ≤ c j) := by
  obtain ⟨s, hs_cof, hs_type⟩ := Ordinal.exists_ord_cof_eq l.ToType
  have hs_type' : typeLT s = typeLT l.cof.ord.ToType := by
    rw [hs_type, Ordinal.cof_toType, Ordinal.type_toType]
  obtain ⟨iso⟩ := Ordinal.type_eq.1 hs_type'.symm
  let e : l.cof.ord.ToType ≃o s := OrderIso.ofRelIsoLT iso
  let c : l.cof.ord.ToType → Ordinal.{0} := fun i => (e i).1.toOrd.1
  refine ⟨c, fun i => (e i).1.toOrd.2, fun β hβ => ?_⟩
  obtain ⟨y, hy_s, hxy⟩ := hs_cof (Ordinal.ToType.mk ⟨β, hβ⟩)
  let i₀ := e.symm ⟨y, hy_s⟩
  refine ⟨i₀, fun j hj => ?_⟩
  have he : e i₀ ≤ e j := e.monotone hj
  have h1 : (Ordinal.ToType.mk ⟨β, hβ⟩).toOrd.1 ≤ y.toOrd.1 :=
    (Ordinal.ToType.mk.symm).monotone hxy
  have h2 : y.toOrd.1 ≤ (e j).1.toOrd.1 := by
    change (⟨y, hy_s⟩ : s).1.toOrd.1 ≤ (e j).1.toOrd.1
    rw [← e.apply_symm_apply ⟨y, hy_s⟩]
    exact (Ordinal.ToType.mk.symm).monotone he
  simpa [c] using h1.trans h2

theorem exists_witness_rank {κ θ : Cardinal.{0}} (hκ : κ.IsRegular) (_hθ : θ.IsRegular)
    (hθκ : θ ≤ κ) :
    ∀ ⦃α : Ordinal.{0}⦄, α < θ.ord →
      ∃ x : A κ θ κ.ord, x ∈ B κ θ α ∧ x ∉ B κ θ (Order.succ α) := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
    intro hαθ
    rcases Ordinal.zero_or_succ_or_isSuccLimit α with rfl | ⟨α', rfl⟩ | hl
    · obtain ⟨b_κ, hb_κ⟩ := step1_not_surjective_kappa κ θ hκ
      refine ⟨b_κ, ?_, ?_⟩
      · rw [B_zero]; trivial
      · rw [B]
        rintro ⟨y, hy⟩
        have h1 : κ.ord + Order.succ (0 : Ordinal.{0}) = Order.succ κ.ord := by
          rw [Order.succ_eq_add_one, zero_add]
          exact (Order.succ_eq_add_one κ.ord).symm
        let y' : A κ θ (Order.succ κ.ord) := cast (congrArg (A κ θ) h1) y
        have hrew : ∀ (o : Ordinal.{0}) (ho : κ.ord ≤ o) (heq : o = Order.succ κ.ord)
            (z : A κ θ o),
            f (κ := κ) (θ := θ) ho z =
              f (Order.le_succ κ.ord) (cast (congrArg (A κ θ) heq) z) := by
          rintro o _ rfl z; rfl
        exact hb_κ y' ((hrew (κ.ord + Order.succ 0) _ h1 y).symm.trans hy)
    · have hα'θ : α' < θ.ord := (Order.lt_succ α').trans hαθ
      obtain ⟨x, hx_in, hx_out⟩ := IH α' (Order.lt_succ α') hα'θ
      refine ⟨sigma hκ x, ?_, ?_⟩
      · rwa [sigma_mem_B_succ hκ hθκ]
      · rwa [sigma_mem_B_succ hκ hθκ]
    · have hμ_reg : α.cof.IsRegular := Cardinal.isRegular_cof hl
      have hμ_lt : α.cof < θ := (Ordinal.cof_le_card α).trans_lt (Cardinal.lt_ord.1 hαθ)
      let μ : RegBelow θ := ⟨α.cof, hμ_reg, hμ_lt⟩
      obtain ⟨c, hc_lt, hc_cof⟩ := exists_cofinal_seq_limit hl
      let a : μ.1.ord.ToType → A κ θ κ.ord := fun j =>
        Classical.choose (IH (c j) (hc_lt j) ((hc_lt j).trans hαθ))
      have ha_spec : ∀ j, a j ∈ B κ θ (c j) ∧ a j ∉ B κ θ (Order.succ (c j)) :=
        fun j => Classical.choose_spec (IH (c j) (hc_lt j) ((hc_lt j).trans hαθ))
      refine ⟨tau μ a, ?_, ?_⟩
      · rw [B_limit hκ hθκ hl]
        simp only [Set.mem_iInter]
        intro β hβ
        apply B_antitone κ θ (Order.le_succ β)
        rw [tau_mem_B_succ hκ hθκ]
        obtain ⟨i₀, hi₀⟩ := hc_cof β hβ
        let emb : { j : μ.1.ord.ToType // a j ∉ B κ θ β } → i₀.toOrd.1.ToType :=
          fun j => Ordinal.ToType.mk ⟨j.1.toOrd.1, by
            by_contra hnot
            have hle : i₀ ≤ j.1 := not_lt.mp (fun hlt => hnot hlt)
            exact j.2 (B_antitone κ θ (hi₀ j.1 hle) (ha_spec j.1).1)⟩
        have hemb : Function.Injective emb := by
          intro j₁ j₂ heq
          dsimp only [emb] at heq
          have heq' := (@Ordinal.ToType.mk i₀.toOrd.1).injective heq
          have h1 : j₁.1.toOrd.1 = j₂.1.toOrd.1 :=
            congrArg (fun x : Set.Iio i₀.toOrd.1 => x.1) heq'
          exact Subtype.ext (Ordinal.ToType.mk.symm.injective (Subtype.ext h1))
        have hle_card := Cardinal.mk_le_of_injective hemb
        have hi₀_card : Cardinal.mk i₀.toOrd.1.ToType = i₀.toOrd.1.card := by simp
        rw [hi₀_card] at hle_card
        exact lt_of_le_of_lt hle_card (Cardinal.lt_ord.1 i₀.toOrd.2)
      · rw [tau_mem_B_succ hκ hθκ]
        intro hbad
        have hnot : ∀ j : μ.1.ord.ToType, a j ∉ B κ θ α := by
          intro j hj
          have hs_lt : Order.succ (c j) < α := hl.succ_lt (hc_lt j)
          exact (ha_spec j).2 (B_antitone κ θ hs_lt.le hj)
        let fn : μ.1.ord.ToType → { j : μ.1.ord.ToType // a j ∉ B κ θ α } :=
          fun j => ⟨j, hnot j⟩
        have hinj : Function.Injective fn := fun j₁ j₂ hij => congrArg Subtype.val hij
        have hle : Cardinal.mk μ.1.ord.ToType ≤
            Cardinal.mk { j : μ.1.ord.ToType // a j ∉ B κ θ α } :=
          Cardinal.mk_le_of_injective hinj
        have hmucard : Cardinal.mk μ.1.ord.ToType = μ.1 := by simp
        rw [hmucard] at hle
        exact (lt_irrefl μ.1 (lt_of_le_of_lt hle hbad))

/-! ### 4. Regularity Closure at `θ.ord` and Final Stabilization Theorem -/

theorem B_theta_closed {κ θ : Cardinal.{0}} (hκ : κ.IsRegular) (hθ : θ.IsRegular)
    (hθκ : θ ≤ κ) : B κ θ (Order.succ θ.ord) = B κ θ θ.ord := by
  apply Set.Subset.antisymm (B_antitone κ θ (Order.le_succ θ.ord))
  intro x hxθ
  have hlim_θ : Order.IsSuccLimit θ.ord := Cardinal.isSuccLimit_ord hθ.aleph0_le
  have hx1 : x ∈ B κ θ (Order.succ 0) :=
    B_antitone κ θ (Order.succ_le_iff.2 hθ.ord_pos) hxθ
  rw [B_succ] at hx1
  rcases hx1 with ⟨y, _, rfl⟩
  let u := succEquiv κ θ κ.ord y
  have hu_all : ∀ β < θ.ord, inSubFunctor (B κ θ β) u := by
    intro β hβ
    have hxs : f (κ := κ) (θ := θ) (Order.le_succ κ.ord) y ∈ B κ θ (Order.succ β) :=
      B_antitone κ θ (hlim_θ.succ_lt hβ).le hxθ
    rw [B_succ] at hxs
    rcases hxs with ⟨w, hw, hweq⟩
    have hwy : w = y := f_kappa_succ_injective hκ hθκ hweq
    rw [hwy] at hw
    exact hw
  rw [B_succ]
  refine ⟨y, ?_, rfl⟩
  change inSubFunctor (B κ θ θ.ord) u
  cases hu : u with
  | inl S_pair =>
      rcases S_pair with ⟨S, hS⟩
      dsimp only [inSubFunctor]
      rw [B_limit hκ hθκ hlim_θ]
      simp only [Set.subset_iInter_iff]
      intro β hβ
      have huβ := hu_all β hβ
      rw [hu] at huβ
      exact huβ
  | inr p =>
      rcases p with ⟨μ, q⟩
      let a : μ.1.ord.ToType → A κ θ κ.ord := Quotient.out q
      have hexit : ∀ i : μ.1.ord.ToType, a i ∉ B κ θ θ.ord →
          ∃ γ < θ.ord, a i ∉ B κ θ γ := by
        intro i hi
        rw [B_limit hκ hθκ hlim_θ] at hi
        simpa using hi
      let exitOrd (i : μ.1.ord.ToType) : Ordinal.{0} :=
        if h : a i ∉ B κ θ θ.ord then Classical.choose (hexit i h) else 0
      have hexit_lt : ∀ i, exitOrd i < θ.ord := by
        intro i
        by_cases h : a i ∉ B κ θ θ.ord
        · simp only [exitOrd, dite_eq_left_of_eq_true (eq_true h)]
          exact (Classical.choose_spec (hexit i h)).1
        · simp only [exitOrd, dite_eq_right_of_eq_false (eq_false h)]
          exact hθ.ord_pos
      have hbdd : BddAbove (Set.range exitOrd) :=
        ⟨θ.ord, Set.forall_mem_range.2 fun i => (hexit_lt i).le⟩
      have hμcard : Cardinal.mk μ.1.ord.ToType = μ.1 := by simp
      have hsup : (⨆ i : μ.1.ord.ToType, exitOrd i) < θ.ord := by
        apply Ordinal.iSup_lt_of_lt_cof
        · rw [hθ.cof_ord, hμcard]
          exact μ.2.2
        · exact hexit_lt
      let βstar := ⨆ i : μ.1.ord.ToType, exitOrd i
      have huβ := hu_all βstar hsup
      rw [hu] at huβ
      rcases huβ with ⟨b, hbB, hbq⟩
      have hdiff : ltDiff μ.1 b a := by
        rw [← Quotient.out_eq q] at hbq
        exact Quotient.exact hbq
      have hsmall : Cardinal.mk { i : μ.1.ord.ToType // a i ∉ B κ θ θ.ord } < μ.1 := by
        have hinj : Function.Injective (fun i : { i : μ.1.ord.ToType // a i ∉ B κ θ θ.ord } =>
            (⟨i.1, fun heq => by
              have hmem : a i.1 ∈ B κ θ βstar := heq ▸ hbB i.1
              have hex_spec := Classical.choose_spec (hexit i.1 i.2)
              have hle : exitOrd i.1 ≤ βstar := le_ciSup hbdd i.1
              have heq_e : exitOrd i.1 = Classical.choose (hexit i.1 i.2) := by
                dsimp [exitOrd]
                exact dite_eq_left_of_eq_true (eq_true i.2)
              rw [heq_e] at hle
              exact hex_spec.2 (B_antitone κ θ hle hmem)⟩ :
              { i : μ.1.ord.ToType // b i ≠ a i })) := by
          intro i j hij
          exact Subtype.ext (congrArg (fun z : { i : μ.1.ord.ToType // b i ≠ a i } => z.1) hij)
        exact lt_of_le_of_lt (Cardinal.mk_le_of_injective hinj) hdiff
      obtain ⟨b₀, hb₀⟩ := B_nonempty (κ := κ) (θ := θ) hκ θ.ord
      let b' : μ.1.ord.ToType → A κ θ κ.ord := fun i => if a i ∈ B κ θ θ.ord then a i else b₀
      refine ⟨b', fun i => ?_, ?_⟩
      · dsimp only [b']; split_ifs with hi
        · exact hi
        · exact hb₀
      · rw [← Quotient.out_eq q]
        apply Quotient.sound
        change ltDiff μ.1 b' a
        unfold ltDiff
        have hinj : Function.Injective (fun i : { i : μ.1.ord.ToType // b' i ≠ a i } =>
            (⟨i.1, fun hi => i.2 (by simp [b', hi])⟩ :
              { i : μ.1.ord.ToType // a i ∉ B κ θ θ.ord })) := by
          intro i j hij
          exact Subtype.ext (by have h := congrArg Subtype.val hij; exact h)
        exact lt_of_le_of_lt (Cardinal.mk_le_of_injective hinj) hsmall

theorem stab_general_kappa_theta {κ θ : Cardinal.{0}} (hκ : κ.IsRegular) (hθ : θ.IsRegular)
    (hθκ : θ ≤ κ) : Stabilizes κ θ (κ.ord + θ.ord) := by
  constructor
  · unfold Abstract.StabilizesAt
    have h_inj : Function.Injective
        (f (κ := κ) (θ := θ) (Order.le_succ (κ.ord + θ.ord))) :=
      tail_monic hκ hθκ (ord_le_add_right κ.ord θ.ord) (Order.le_succ (κ.ord + θ.ord))
    refine ⟨h_inj, fun x => ?_⟩
    have hxB : f (κ := κ) (θ := θ) (ord_le_add_right κ.ord θ.ord) x ∈ B κ θ θ.ord := by
      rw [B]
      exact ⟨x, rfl⟩
    rw [← B_theta_closed hκ hθ hθκ, B] at hxB
    rcases hxB with ⟨y, hy⟩
    have hadd : κ.ord + Order.succ θ.ord = Order.succ (κ.ord + θ.ord) :=
      add_succ_ord κ.ord θ.ord
    let y' : A κ θ (Order.succ (κ.ord + θ.ord)) := cast (congrArg (A κ θ) hadd) y
    have hrew : ∀ (o : Ordinal.{0}) (ho : κ.ord ≤ o) (heq : o = Order.succ (κ.ord + θ.ord))
        (z : A κ θ o),
        f (κ := κ) (θ := θ) ho z =
          f (ord_le_add_right κ.ord θ.ord)
            (f (Order.le_succ (κ.ord + θ.ord)) (cast (congrArg (A κ θ) heq) z)) := by
      rintro o _ rfl z
      exact f_comp (ord_le_add_right κ.ord θ.ord) (Order.le_succ (κ.ord + θ.ord)) z
    have heq_top := (hrew (κ.ord + Order.succ θ.ord) _ hadd y).symm.trans hy
    have htail_inj := tail_monic hκ hθκ (le_refl κ.ord) (ord_le_add_right κ.ord θ.ord)
    exact ⟨y', htail_inj heq_top⟩
  · intro δ hδ hstab
    rcases lt_or_ge δ κ.ord with hlt_κ | hge_κ
    · exact not_stabilizesAt_lt_kappa κ θ hκ hlt_κ hstab
    · let β := δ - κ.ord
      have hβ : β < θ.ord := Ordinal.sub_lt_of_le hge_κ |>.mpr hδ
      have hadd : κ.ord + β = δ := Ordinal.add_sub_cancel_of_le hge_κ
      obtain ⟨x, hx_in, hx_out⟩ := exists_witness_rank hκ hθ hθκ hβ
      rw [B] at hx_in
      rcases hx_in with ⟨y, rfl⟩
      have hy' : ∃ w : A κ θ (Order.succ (κ.ord + β)),
          f (κ := κ) (θ := θ) (Order.le_succ (κ.ord + β)) w = y := by
        have hrew : ∀ (o : Ordinal.{0}) (ho : o = κ.ord + β),
            StabilizesAt κ θ o →
            ∃ w : A κ θ (Order.succ (κ.ord + β)),
              f (κ := κ) (θ := θ) (Order.le_succ (κ.ord + β)) w = y := by
          rintro o rfl hst
          exact hst.surjective y
        exact hrew δ hadd.symm hstab
      rcases hy' with ⟨w, rfl⟩
      have hadd_s : κ.ord + Order.succ β = Order.succ (κ.ord + β) := add_succ_ord κ.ord β
      let w' : A κ θ (κ.ord + Order.succ β) := cast (congrArg (A κ θ) hadd_s.symm) w
      apply hx_out
      rw [B]
      refine ⟨w', ?_⟩
      have hrew : ∀ (o : Ordinal.{0}) (ho : κ.ord ≤ o) (heq : o = Order.succ (κ.ord + β))
          (z : A κ θ (Order.succ (κ.ord + β))),
          f (κ := κ) (θ := θ) ho (cast (congrArg (A κ θ) heq.symm) z) =
            f (ord_le_add_right κ.ord β) (f (Order.le_succ (κ.ord + β)) z) := by
        rintro o _ rfl z
        exact f_comp (ord_le_add_right κ.ord β) (Order.le_succ (κ.ord + β)) z
      exact hrew (κ.ord + Order.succ β) _ hadd_s w

end TerminalSeq
