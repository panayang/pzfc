import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
  Real-valued parts of notes/16.  Unlike the files one directory up, this file
  uses Mathlib and therefore classical logic: these results live in the
  classical corner of the coordinate system.

  1. The W-axis is continuous: `h log(e^{x/h} + e^{y/h}) → max x y` as `h → 0⁺`.
  2. With real `+`, refinement and normalisation leave exactly one weight.
  3. With truncated `+` on `[0,1]`: a whole family of weights — saturated
     above, exact halving below, one free parameter in between.
  4. Symmetry forces the denominators, all dividing `|G|`: an invariant point
     weight is `1/|orbit| = |Stab|/|G|`; counting orbits with weight `1/|Stab|`
     gives `|X|/|G|`.
  5. Infinite branching: no uniform countably additive probability on `ℕ`,
     but the idempotent (possibility) weight is unproblematic.
  6. The absorption ladder: `κ² = κ ⟹ 2κ = κ ⟹ κ + 1 = κ` (with Cantor–
     Schröder–Bernstein, a ZF argument).
  7. Regularity is additivity surviving: for a finite measure, `A` is
     null-measurable iff the weight is additive on `{A, Aᶜ}`, i.e. iff the
     additivity defect of `A` vanishes.
-/

open Real Filter Topology

namespace PZFC.Weights

/-! ## 1. The W-axis is continuous -/

theorem lse_lower (x y : ℝ) {h : ℝ} (hh : 0 < h) :
    max x y ≤ h * log (exp (x / h) + exp (y / h)) := by
  have hpos : 0 < exp (x / h) + exp (y / h) := by positivity
  have key : max x y / h ≤ log (exp (x / h) + exp (y / h)) := by
    rw [le_log_iff_exp_le hpos]
    rcases le_total x y with hxy | hxy
    · rw [max_eq_right hxy]
      linarith [exp_pos (x / h)]
    · rw [max_eq_left hxy]
      linarith [exp_pos (y / h)]
  calc max x y ≤ log (exp (x / h) + exp (y / h)) * h := (div_le_iff₀ hh).mp key
    _ = h * log (exp (x / h) + exp (y / h)) := mul_comm _ _

theorem lse_upper (x y : ℝ) {h : ℝ} (hh : 0 < h) :
    h * log (exp (x / h) + exp (y / h)) ≤ max x y + h * log 2 := by
  have hne : h ≠ 0 := ne_of_gt hh
  have hpos : 0 < exp (x / h) + exp (y / h) := by positivity
  have h1 : exp (x / h) ≤ exp (max x y / h) :=
    exp_le_exp.mpr (div_le_div_of_nonneg_right (le_max_left x y) hh.le)
  have h2 : exp (y / h) ≤ exp (max x y / h) :=
    exp_le_exp.mpr (div_le_div_of_nonneg_right (le_max_right x y) hh.le)
  have hle : exp (x / h) + exp (y / h) ≤ 2 * exp (max x y / h) := by linarith
  have hlog : log (exp (x / h) + exp (y / h)) ≤ log 2 + max x y / h := by
    calc log (exp (x / h) + exp (y / h)) ≤ log (2 * exp (max x y / h)) :=
          log_le_log hpos hle
      _ = log 2 + max x y / h := by
          rw [log_mul (by norm_num) (exp_pos _).ne', log_exp]
  calc h * log (exp (x / h) + exp (y / h)) ≤ h * (log 2 + max x y / h) :=
        mul_le_mul_of_nonneg_left hlog hh.le
    _ = max x y + h * log 2 := by
        rw [mul_add, mul_div_assoc', mul_div_cancel_left₀ _ hne]
        ring

/-- The additive end of the W-axis is joined continuously to the idempotent
    end: the log-sum-exp family degenerates to `max`. -/
theorem lse_tendsto_max (x y : ℝ) :
    Tendsto (fun h => h * log (exp (x / h) + exp (y / h))) (𝓝[>] 0) (𝓝 (max x y)) := by
  have hup : Tendsto (fun h : ℝ => max x y + h * log 2) (𝓝[>] 0) (𝓝 (max x y)) := by
    have h0 : Tendsto (fun h : ℝ => max x y + h * log 2) (𝓝 0) (𝓝 (max x y + 0 * log 2)) :=
      tendsto_const_nhds.add (tendsto_id.mul_const _)
    rw [zero_mul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact lse_lower x y hh
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact lse_upper x y hh

/-! ## 2. Real addition: exactly one weight -/

theorem additive_unique (u : ℕ → ℝ) (h0 : u 0 = 1)
    (hc : ∀ n, u n = u (n + 1) + u (n + 1)) : ∀ n, u n = (1 / 2) ^ n := by
  intro n
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have := hc n
    rw [pow_succ]
    linarith

/-! ## 3. Truncated addition on `[0,1]`: a family, not a point -/

section Truncated

variable (u : ℕ → ℝ) (hc : ∀ n, u n = min 1 (u (n + 1) + u (n + 1)))
include hc

theorem trunc_le_one (n : ℕ) : u n ≤ 1 := by
  rw [hc n]
  exact min_le_left _ _

/-- Below saturation the weight halves exactly. -/
theorem trunc_below (n : ℕ) (hn : u n < 1) : u (n + 1) = u n / 2 := by
  rcases min_cases 1 (u (n + 1) + u (n + 1)) with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [hc n, h1] at hn
    exact absurd hn (lt_irrefl 1)
  · have h := hc n
    rw [h1] at h
    linarith

/-- At saturation the next weight is only bounded below by one half. -/
theorem trunc_at_one (n : ℕ) (hn : u n = 1) : 1 / 2 ≤ u (n + 1) := by
  rcases min_cases 1 (u (n + 1) + u (n + 1)) with ⟨_, h2⟩ | ⟨h1, h2⟩
  · linarith
  · have h := hc n
    rw [h1] at h
    linarith

/-- Once below saturation, the profile is exact halving forever. -/
theorem trunc_halving (n : ℕ) (hn : u n < 1) (hnn : 0 ≤ u n) :
    ∀ k, u (n + k) = u n / 2 ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : u (n + k) < 1 := by
      rw [ih]
      calc u n / 2 ^ k ≤ u n := div_le_self hnn (one_le_pow₀ (by norm_num))
        _ < 1 := hn
    rw [← add_assoc, trunc_below u hc (n + k) hk, ih, pow_succ, div_div]

end Truncated

/-- One member of the family for each `v ∈ [1/2, 1]`: saturated at depth 0,
    weight `v` at depth 1, exact halving afterwards. -/
noncomputable def famV (v : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => v / 2 ^ n

theorem famV_solves (v : ℝ) (hv : 1 / 2 ≤ v) (hv1 : v ≤ 1) :
    ∀ n, famV v n = min 1 (famV v (n + 1) + famV v (n + 1)) := by
  intro n
  cases n with
  | zero =>
    show (1 : ℝ) = min 1 (v / 2 ^ 0 + v / 2 ^ 0)
    rw [pow_zero, div_one, min_eq_left (by linarith)]
  | succ n =>
    show v / 2 ^ n = min 1 (v / 2 ^ (n + 1) + v / 2 ^ (n + 1))
    have hsum : v / 2 ^ (n + 1) + v / 2 ^ (n + 1) = v / 2 ^ n := by ring
    have hle : v / 2 ^ n ≤ 1 :=
      (div_le_self (by linarith) (one_le_pow₀ (by norm_num))).trans hv1
    rw [hsum, min_eq_right hle]

/-- The family is genuinely a family: its members differ. -/
theorem famV_not_unique : famV (1 / 2) 1 ≠ famV 1 1 := by
  show (1 / 2 : ℝ) / 2 ^ 0 ≠ 1 / 2 ^ 0
  norm_num

/-! ## 4. The denominators divide the order of the symmetry -/

open MulAction

/-- An invariant weight on an orbit gives each point `|Stab|/|G|`. -/
theorem point_weight (G X : Type*) [Group G] [MulAction G X] [Fintype G] (x : X)
    [Fintype (orbit G x)] [Fintype (stabilizer G x)] :
    (1 : ℚ) / Fintype.card (orbit G x) =
      Fintype.card (stabilizer G x) / Fintype.card G := by
  have h := card_orbit_mul_card_stabilizer_eq_card_group G x
  have : Nonempty (orbit G x) := ⟨⟨x, mem_orbit_self x⟩⟩
  have : Nonempty (stabilizer G x) := ⟨1⟩
  have hO : (Fintype.card (orbit G x) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (stabilizer G x) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hGq : (Fintype.card G : ℚ) =
      Fintype.card (orbit G x) * Fintype.card (stabilizer G x) := by
    exact_mod_cast h.symm
  rw [hGq, div_eq_div_iff hO (mul_ne_zero hO hS)]
  ring

open Classical in
/-- Mass formula: counting orbits, each with weight `1/|Stab|`, gives `|X|/|G|`.
    Counting up to symmetry is fractional, and the fractions are forced. -/
theorem mass_formula (G X : Type*) [Group G] [MulAction G X] [Fintype G] [Fintype X] :
    (∑ ω : Quotient (orbitRel G X), (1 : ℚ) / Fintype.card (stabilizer G ω.out)) =
      Fintype.card X / Fintype.card G := by
  have : Nonempty G := ⟨1⟩
  have hG : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hclass := card_eq_sum_card_group_div_card_stabilizer G X
  have hdvd : ∀ ω : Quotient (orbitRel G X),
      Fintype.card (stabilizer G ω.out) ∣ Fintype.card G := fun ω =>
    Dvd.intro_left _ (card_orbit_mul_card_stabilizer_eq_card_group G ω.out)
  have hcast : (Fintype.card X : ℚ) = ∑ ω : Quotient (orbitRel G X),
      (Fintype.card G : ℚ) / Fintype.card (stabilizer G ω.out) := by
    rw [hclass, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    have : Nonempty (stabilizer G ω.out) := ⟨1⟩
    rw [Nat.cast_div (hdvd ω) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  rw [hcast, eq_div_iff hG, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  ring

/-! ## 5. Infinite branching -/

open scoped ENNReal in
/-- On `ℕ` there is no uniform countably additive probability: equal weights
    sum to `0` or to `∞`, never to `1`. -/
theorem no_uniform_probability_nat : ¬ ∃ c : ℝ≥0∞, (∑' _ : ℕ, c) = 1 := by
  rintro ⟨c, hc⟩
  by_cases h0 : c = 0
  · subst h0
    simp at hc
  · rw [ENNReal.tsum_const_eq_top_of_ne_zero h0] at hc
    exact ENNReal.top_ne_one hc

open scoped ENNReal in
/-- With the idempotent `⨆`, the uniform weight is unproblematic: every natural
    number is "possible", and the whole is still `1`. -/
theorem uniform_possibility_nat : (⨆ _ : ℕ, (1 : ℝ≥0∞)) = 1 := iSup_const

/-! ## 6. The absorption ladder -/

/-- If a nonempty `A` absorbs its own double, it absorbs a point. -/
theorem absorb_double_absorb_point (A : Type*) (a₀ : A) (e : A ⊕ A ≃ A) :
    ∃ h : A ⊕ Unit → A, Function.Bijective h := by
  let f : A ⊕ Unit → A := fun s => e (Sum.elim Sum.inl (fun _ => Sum.inr a₀) s)
  have hf : Function.Injective f := by
    intro s t hst
    have h := e.injective hst
    rcases s with s | s <;> rcases t with t | t <;> simp_all
  exact Function.Embedding.schroeder_bernstein hf Sum.inl_injective

/-- If `A` (with two distinct points) absorbs its own square, it absorbs its
    double. -/
theorem absorb_square_absorb_double (A : Type*) (b₀ b₁ : A) (hb : b₀ ≠ b₁)
    (e : A × A ≃ A) : ∃ h : A ⊕ A → A, Function.Bijective h := by
  let f : A ⊕ A → A := fun s => e (Sum.elim (fun a => (a, b₀)) (fun a => (a, b₁)) s)
  have hf : Function.Injective f := by
    intro s t hst
    have h := e.injective hst
    rcases s with s | s <;> rcases t with t | t <;> simp_all
  exact Function.Embedding.schroeder_bernstein hf Sum.inl_injective

/-! ## 7. Regularity is additivity surviving -/

open MeasureTheory Set in
theorem nullMeasurable_iff_additive {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (A : Set α) :
    NullMeasurableSet A μ ↔ μ A + μ Aᶜ = μ univ := by
  refine ⟨measure_add_measure_compl₀, fun h => ?_⟩
  set H := toMeasurable μ A with hH
  have hAH : A ⊆ H := subset_toMeasurable μ A
  have hHm : MeasurableSet H := measurableSet_toMeasurable μ A
  have hμH : μ H = μ A := measure_toMeasurable A
  have hc : μ Aᶜ = μ (H \ A) + μ Hᶜ := by
    have hsplit := measure_inter_add_sdiff (μ := μ) Aᶜ hHm
    have e1 : Aᶜ ∩ H = H \ A := by
      ext x
      simp [and_comm]
    have e2 : Aᶜ \ H = Hᶜ := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_compl_iff]
      exact ⟨fun hx => hx.2, fun hx => ⟨fun hA => hx (hAH hA), hx⟩⟩
    rw [e1, e2] at hsplit
    exact hsplit.symm
  have htot : μ H + μ Hᶜ = μ univ := measure_add_measure_compl hHm
  have key : (μ A + μ Hᶜ) + μ (H \ A) = (μ A + μ Hᶜ) + 0 := by
    calc (μ A + μ Hᶜ) + μ (H \ A) = μ A + μ Aᶜ := by rw [hc]; ring
      _ = μ univ := h
      _ = μ H + μ Hᶜ := htot.symm
      _ = (μ A + μ Hᶜ) + 0 := by rw [hμH, add_zero]
  have hfin : μ A + μ Hᶜ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top μ A, measure_ne_top μ _⟩
  have hnull : μ (H \ A) = 0 := (ENNReal.add_right_inj hfin).mp key
  have hae : A =ᵐ[μ] H := by
    rw [ae_eq_set]
    refine ⟨?_, hnull⟩
    rw [Set.sdiff_eq_empty.mpr hAH, measure_empty]
  exact hHm.nullMeasurableSet.congr hae.symm

open MeasureTheory Set in
/-- The additivity defect of `A` (truncated subtraction in `ℝ≥0∞`). -/
noncomputable def defect {α : Type*} [MeasurableSpace α] (μ : Measure α) (A : Set α) :
    ENNReal :=
  μ A + μ Aᶜ - μ univ

open MeasureTheory Set in
theorem defect_eq_zero_iff {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (A : Set α) : defect μ A = 0 ↔ NullMeasurableSet A μ := by
  rw [nullMeasurable_iff_additive, defect, tsub_eq_zero_iff_le]
  exact ⟨fun h => le_antisymm h (measure_univ_le_add_compl A), fun h => h.le⟩

end PZFC.Weights
