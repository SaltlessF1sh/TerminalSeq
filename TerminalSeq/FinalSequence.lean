import TerminalSeq.Abstract.Stabilization

/-!
# Terminal Sequence for `G_{κ,θ}` via `TerminalSeq.Abstract`

Defines the set endofunctor
$$G_{\kappa,\theta}(X) = \mathcal{P}_{<\kappa}(X) \sqcup \sum_{\mu < \theta\text{ regular}} (X^\mu / {\equiv_{<\mu}})$$
on `Type 1`, packages it as `GFunctor κ θ : TerminalSeq.Abstract.SetFunctor`, and exposes its
terminal sequence `(A κ θ α, f h)` together with `zeroEquiv`, `succEquiv`, `limitEquiv`, and
`nonempty_A` directly on top of the shared `TerminalSeq.Abstract` infrastructure.
-/

noncomputable section

open Classical Ordinal Cardinal

namespace TerminalSeq

/-! ### 1. Pure Lean Type Definition of `G_{κ,θ}` -/

section PureFunctor

/-- Infinite regular cardinals strictly below `θ`. -/
abbrev RegBelow (θ : Cardinal.{0}) : Type 1 :=
  { μ : Cardinal.{0} // μ.IsRegular ∧ μ < θ }

/-- Two `μ`-indexed sequences in `X` are equivalent iff they differ on fewer than `μ` indices. -/
def ltDiff {X : Type 1} (μ : Cardinal.{0}) (a b : μ.ord.ToType → X) : Prop :=
  Cardinal.mk { i : μ.ord.ToType // a i ≠ b i } < μ

theorem ltDiff_refl {X : Type 1} (μ : Cardinal.{0}) (hμ : 0 < μ) (a : μ.ord.ToType → X) :
    ltDiff μ a a := by
  unfold ltDiff
  have hem : IsEmpty { i : μ.ord.ToType // a i ≠ a i } := ⟨fun i => i.2 rfl⟩
  simpa using hμ

theorem ltDiff_symm {X : Type 1} (μ : Cardinal.{0}) {a b : μ.ord.ToType → X}
    (h : ltDiff μ a b) : ltDiff μ b a := by
  unfold ltDiff at *
  have heq : Cardinal.mk { i : μ.ord.ToType // b i ≠ a i } =
      Cardinal.mk { i : μ.ord.ToType // a i ≠ b i } :=
    Cardinal.mk_congr (Equiv.subtypeEquivRight fun _ => ne_comm)
  rwa [heq]

theorem ltDiff_trans {X : Type 1} (μ : Cardinal.{0}) (hμ : μ.IsRegular)
    {a b c : μ.ord.ToType → X} (hab : ltDiff μ a b) (hbc : ltDiff μ b c) :
    ltDiff μ a c := by
  unfold ltDiff at *
  let U : Set μ.ord.ToType := { i | a i ≠ b i } ∪ { i | b i ≠ c i }
  let mapFn : { i : μ.ord.ToType // a i ≠ c i } → ↥U := fun i =>
    ⟨i.1, by
      by_cases h1 : a i.1 = b i.1
      · right; intro h2; exact i.2 (h1.trans h2)
      · left; exact h1⟩
  have hinj : Function.Injective mapFn := fun _ _ hxy =>
    Subtype.ext (by have h := congrArg Subtype.val hxy; exact h)
  have hle : Cardinal.mk { i : μ.ord.ToType // a i ≠ c i } ≤ Cardinal.mk ↥U :=
    Cardinal.mk_le_of_injective hinj
  have hU : Cardinal.mk ↥U ≤
      Cardinal.mk { i : μ.ord.ToType // a i ≠ b i } +
      Cardinal.mk { i : μ.ord.ToType // b i ≠ c i } :=
    Cardinal.mk_union_le _ _
  have hadd : Cardinal.mk { i : μ.ord.ToType // a i ≠ b i } +
      Cardinal.mk { i : μ.ord.ToType // b i ≠ c i } < μ :=
    Cardinal.add_lt_of_lt hμ.aleph0_le hab hbc
  exact lt_of_le_of_lt (hle.trans hU) hadd

def ltDiffSetoid {θ : Cardinal.{0}} (X : Type 1) (μ : RegBelow θ) : Setoid (μ.1.ord.ToType → X) where
  r := ltDiff μ.1
  iseqv :=
    ⟨ltDiff_refl μ.1 μ.2.1.pos,
     fun h => ltDiff_symm μ.1 h,
     fun h1 h2 => ltDiff_trans μ.1 μ.2.1 h1 h2⟩

/-- Set endofunctor `G_{κ,θ}` on `Type 1`. -/
abbrev G (κ θ : Cardinal.{0}) (X : Type 1) : Type 1 :=
  { S : Set X // Cardinal.mk S < Cardinal.lift.{1, 0} κ } ⊕
    (μ : RegBelow θ) × Quotient (ltDiffSetoid X μ)

/-- Functorial action `G_{κ,θ}(g)` on maps `g : X → Y`. -/
def G.map {κ θ : Cardinal.{0}} {X Y : Type 1} (g : X → Y) : G κ θ X → G κ θ Y
  | .inl ⟨S, hS⟩ => .inl ⟨g '' S, lt_of_le_of_lt Cardinal.mk_image_le hS⟩
  | .inr ⟨μ, q⟩ =>
      .inr ⟨μ, Quotient.liftOn q (fun a => Quotient.mk (ltDiffSetoid Y μ) (g ∘ a)) (fun a b hab => by
        apply Quotient.sound
        change ltDiff μ.1 (g ∘ a) (g ∘ b)
        unfold ltDiff
        let hmap : { i : μ.1.ord.ToType // g (a i) ≠ g (b i) } → { i : μ.1.ord.ToType // a i ≠ b i } :=
          fun i => ⟨i.1, fun h => i.2 (congrArg g h)⟩
        have hinj : Function.Injective hmap := fun _ _ hxy =>
          Subtype.ext (by have h := congrArg Subtype.val hxy; exact h)
        exact lt_of_le_of_lt (Cardinal.mk_le_of_injective hinj) hab)⟩

@[simp]
theorem G.map_id {κ θ : Cardinal.{0}} {X : Type 1} (x : G κ θ X) : G.map id x = x := by
  cases x with
  | inl S =>
      rcases S with ⟨S, hS⟩
      change (Sum.inl ⟨id '' S, _⟩ : G κ θ X) = Sum.inl ⟨S, hS⟩
      congr 1
      exact Subtype.ext (Set.image_id S)
  | inr p =>
      rcases p with ⟨μ, q⟩
      induction q using Quotient.ind
      rfl

theorem G.map_comp {κ θ : Cardinal.{0}} {X Y Z : Type 1} (h : Y → Z) (g : X → Y)
    (x : G κ θ X) : G.map (h ∘ g) x = G.map h (G.map g x) := by
  cases x with
  | inl S =>
      rcases S with ⟨S, hS⟩
      change (Sum.inl ⟨(h ∘ g) '' S, _⟩ : G κ θ Z) = Sum.inl ⟨h '' (g '' S), _⟩
      congr 1
      exact Subtype.ext (Set.image_image h g S).symm
  | inr p =>
      rcases p with ⟨μ, q⟩
      induction q using Quotient.ind
      rfl

/-- `G_{κ,θ}` packaged as an abstract `TerminalSeq.Abstract.SetFunctor`. -/
def GFunctor (κ θ : Cardinal.{0}) : Abstract.SetFunctor where
  obj := G κ θ
  map := G.map
  map_id := G.map_id
  map_comp := G.map_comp

end PureFunctor

/-! ### 2. Unified Terminal Sequence API via `TerminalSeq.Abstract` -/

section PublicAPI

/-- Terminal sequence object `A_α` for `GFunctor κ θ`. -/
abbrev A (κ θ : Cardinal.{0}) (α : Ordinal.{0}) : Type 1 :=
  Abstract.A (GFunctor κ θ) α

/-- Transition map `f_α^β : A_β → A_α` for `α ≤ β`. -/
abbrev f {κ θ : Cardinal.{0}} {α β : Ordinal.{0}} (h : α ≤ β) : A κ θ β → A κ θ α :=
  Abstract.f (F := GFunctor κ θ) h

@[simp]
theorem f_id {κ θ : Cardinal.{0}} {α : Ordinal.{0}} (x : A κ θ α) :
    f (κ := κ) (θ := θ) (le_refl α) x = x :=
  Abstract.f_id x

theorem f_comp {κ θ : Cardinal.{0}} {α β γ : Ordinal.{0}} (h₁ : α ≤ β) (h₂ : β ≤ γ)
    (x : A κ θ γ) :
    f (κ := κ) (θ := θ) (h₁.trans h₂) x = f h₁ (f h₂ x) :=
  Abstract.f_comp h₁ h₂ x

/-- Canonical isomorphism `A_0 ≃ PUnit.{2}`. -/
abbrev zeroEquiv (κ θ : Cardinal.{0}) : A κ θ 0 ≃ PUnit.{2} :=
  Abstract.zeroEquiv (GFunctor κ θ)

/-- Canonical isomorphism `A_{α + 1} ≃ G_{κ,θ}(A_α)`. -/
abbrev succEquiv (κ θ : Cardinal.{0}) (α : Ordinal.{0}) :
    A κ θ (Order.succ α) ≃ G κ θ (A κ θ α) :=
  Abstract.succEquiv (GFunctor κ θ) α

theorem succEquiv_f_succ {κ θ : Cardinal.{0}} {α β : Ordinal.{0}} (h : α ≤ β)
    (x : A κ θ (Order.succ β)) :
    succEquiv κ θ α (f (Order.succ_le_succ h) x) = G.map (f h) (succEquiv κ θ β x) :=
  Abstract.succEquiv_f_succ h x

/-- Canonical limit cone equivalence `A_l ≃ lim_{i < l} A_i` for limit ordinals `l`. -/
abbrev limitEquiv (κ θ : Cardinal.{0}) {l : Ordinal.{0}} (hl : Order.IsSuccLimit l) :
    A κ θ l ≃
      { t : (i : l.ToType) → A κ θ i.toOrd.1 //
        ∀ i j (h : i.toOrd.1 ≤ j.toOrd.1), f h (t j) = t i } :=
  Abstract.limitEquiv (GFunctor κ θ) hl

theorem limitEquiv_proj {κ θ : Cardinal.{0}} {l : Ordinal.{0}} (hl : Order.IsSuccLimit l)
    (i : l.ToType) (x : A κ θ l) :
    (limitEquiv κ θ hl x).1 i = f i.toOrd.2.le x :=
  Abstract.limitEquiv_proj (F := GFunctor κ θ) hl i x

/-- Each `A_α` is nonempty provided `0 < κ` (in particular when `κ` is regular). -/
theorem nonempty_A {κ θ : Cardinal.{0}} (hκ : 0 < κ) (α : Ordinal.{0}) :
    Nonempty (A κ θ α) := by
  have h0κ : Cardinal.lift.{1, 0} (0 : Cardinal.{0}) < Cardinal.lift.{1, 0} κ :=
    Cardinal.lift_lt.2 hκ
  have hempty : Cardinal.mk (∅ : Set (A κ θ 0)) < Cardinal.lift.{1, 0} κ := by
    simpa using h0κ
  have hsucc0 : Order.succ (0 : Ordinal.{0}) = 1 := by simp
  have : Nonempty (A κ θ 1) :=
    ⟨cast (congrArg (A κ θ) hsucc0) ((succEquiv κ θ 0).symm (.inl ⟨∅, hempty⟩))⟩
  exact Abstract.nonempty_of_nonempty_one (F := GFunctor κ θ) α

end PublicAPI

end TerminalSeq
