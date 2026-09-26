/-
  The fate of a local set's measure (notes/67).

  Recording a new real can change the size of the sets of the old world.  Two kinds of
  recording are dual: a Cohen real (generic for category) makes every old set of reals null;
  a random real (generic for measure) keeps the outer measure of every old set, and makes the
  old reals meagre.  Genericity itself belongs to the metatheory; this file proves the two
  facts about the real line that carry the argument.

  §1  the line splits into a null set and a meagre set (the Liouville numbers and the rest).
      For every old point `x`, the shifts `t` with `x + t` in the null part are residual;
      for every shift `t`, the points `y` with `y + t` in the null part form a null set.
      So a shift generic for category moves every old point into a null set.  Dually, for
      every old point the shifts landing in the meagre part have full measure, and for each
      shift the points landing there form a meagre set
  §2  the Fubini step behind preservation: if every vertical section of a measurable set is
      null, then a set of positive outer measure contains a point whose horizontal section is
      null; and the exact form: if the vertical sections over `p` have measure at most `δ`,
      a set of outer measure above `δ` contains a point whose horizontal section misses a
      positive part of `p`
-/
import Mathlib.NumberTheory.Transcendental.Liouville.Measure
import Mathlib.NumberTheory.Transcendental.Liouville.Residual
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace PZFC.Fate

open MeasureTheory Filter Set
open scoped ENNReal

/-! ## 1. A null set whose complement is meagre -/

/-- The Liouville numbers. -/
def S : Set ℝ := {x | Liouville x}

theorem S_null : volume S = 0 := volume_setOfPred_liouville

theorem S_residual : S ∈ residual ℝ := eventually_residual_liouville

/-- **The line is a null set together with a meagre set.** -/
theorem null_meagre_split : volume S = 0 ∧ IsMeagre Sᶜ := by
  refine ⟨S_null, ?_⟩
  rw [IsMeagre, compl_compl]
  exact S_residual

theorem preimage_residual (h : ℝ ≃ₜ ℝ) {s : Set ℝ} (hs : s ∈ residual ℝ) : h ⁻¹' s ∈ residual ℝ := by
  have e := Homeomorph.residual_map_eq h
  rw [← e] at hs
  exact hs

/-- **Cohen side.** For every old point `x`, the shifts `t` that move `x` into the null part are
    residual: a shift generic for category moves every old point there. -/
theorem shifts_into_null_residual (x : ℝ) : {t : ℝ | x + t ∈ S} ∈ residual ℝ :=
  preimage_residual (Homeomorph.addLeft x) S_residual

/-- … and for each shift `t`, the points it moves into the null part form a null set. -/
theorem shifted_null (t : ℝ) : volume {y : ℝ | y + t ∈ S} = 0 := by
  have : {y : ℝ | y + t ∈ S} = (fun y => y + t) ⁻¹' S := rfl
  rw [this, measure_preimage_add_right, S_null]

/-- **Random side.** For every old point `x`, the shifts that move `x` into the meagre part have
    full measure: a shift generic for measure moves every old point there. -/
theorem shifts_into_meagre_conull (x : ℝ) : volume {t : ℝ | x + t ∉ S}ᶜ = 0 := by
  have : {t : ℝ | x + t ∉ S}ᶜ = (fun t => x + t) ⁻¹' S := by
    ext t; simp
  rw [this, measure_preimage_add, S_null]

/-- … and for each shift `t`, the points it moves into the meagre part form a meagre set. -/
theorem shifted_meagre (t : ℝ) : IsMeagre {y : ℝ | y + t ∉ S} := by
  rw [IsMeagre]
  have : {y : ℝ | y + t ∉ S}ᶜ = (Homeomorph.addRight t) ⁻¹' S := by
    ext y; simp
  rw [this]
  exact preimage_residual (Homeomorph.addRight t) S_residual

/-! ## 2. The Fubini step behind preservation -/

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [SFinite μ] [SFinite ν]

/-- If every vertical section of a measurable set is null, almost every horizontal section is
    null. -/
theorem sections_null {E : Set (α × β)} (hE : MeasurableSet E)
    (h : ∀ y, μ {x | (x, y) ∈ E} = 0) : ∀ᵐ x ∂μ, ν {y | (x, y) ∈ E} = 0 := by
  have h0 : μ.prod ν E = 0 := by
    rw [Measure.prod_apply_symm hE]
    simp only [preimage, h]
    exact lintegral_zero
  exact Measure.measure_ae_null_of_prod_null h0

/-- **Positive outer measure survives.**  If every vertical section of a measurable set `E` is
    null, every set of positive outer measure contains a point whose horizontal section is null.
    (A random real `r` avoids that null section, which is coded in the old world; so `E`'s
    section at `r` cannot contain the whole set.) -/
theorem exists_null_section {E : Set (α × β)} (hE : MeasurableSet E)
    (h : ∀ y, μ {x | (x, y) ∈ E} = 0) {A : Set α} (hA : μ A ≠ 0) :
    ∃ x ∈ A, ν {y | (x, y) ∈ E} = 0 := by
  by_contra hne
  push Not at hne
  have hs := sections_null (ν := ν) hE h
  rw [ae_iff] at hs
  exact hA (measure_mono_null (fun x hx => hne x hx) hs)

/-- **Outer measure survives exactly.**  Let the vertical sections of `E` over a set `p` of
    positive finite measure have measure at most `δ`.  Then every set of outer measure above `δ`
    contains a point whose horizontal section misses a part of `p` of positive measure.  (A random
    real in `p` lands in that part with positive probability; so the section of `E` at it cannot
    cover the set, and a cover of measure at most `δ` never appears.) -/
theorem exists_section_misses {E : Set (α × β)} (hE : MeasurableSet E) {p : Set β}
    (hp : MeasurableSet p) (hνp : ν p ≠ 0) (hνp' : ν p ≠ ∞) {δ : ℝ≥0∞}
    (h : ∀ y ∈ p, μ {x | (x, y) ∈ E} ≤ δ) {A : Set α} (hA : δ < μ A) :
    ∃ x ∈ A, ν (p \ {y | (x, y) ∈ E}) ≠ 0 := by
  by_contra hne
  push Not at hne
  -- the points whose horizontal section covers almost all of `p`
  set F : Set (α × β) := (univ ×ˢ p) \ E with hF
  have hFm : MeasurableSet F := (MeasurableSet.univ.prod hp).diff hE
  set T : Set α := {x | ν (Prod.mk x ⁻¹' F) = 0} with hT
  have hTm : MeasurableSet T :=
    measurable_measure_prodMk_left hFm (measurableSet_singleton 0)
  have hsec : ∀ x, Prod.mk x ⁻¹' F = p \ {y | (x, y) ∈ E} := by
    intro x; ext y; simp [hF]
  have hAT : A ⊆ T := by
    intro x hx
    show ν (Prod.mk x ⁻¹' F) = 0
    rw [hsec]; exact hne x hx
  -- the part of `E` over `p`
  set G : Set (α × β) := E ∩ (univ ×ˢ p) with hG
  have hGm : MeasurableSet G := hE.inter (MeasurableSet.univ.prod hp)
  -- counted along vertical sections: at most `δ · ν p`
  have hup : μ.prod ν G ≤ δ * ν p := by
    rw [Measure.prod_apply_symm hGm, ← lintegral_indicator_const hp]
    apply lintegral_mono
    intro y
    by_cases hy : y ∈ p
    · rw [indicator_of_mem hy]
      have : (fun x => (x, y)) ⁻¹' G = {x | (x, y) ∈ E} := by
        ext x; simp [hG, hy]
      beta_reduce
      rw [this]; exact h y hy
    · have : (fun x => (x, y)) ⁻¹' G = ∅ := by
        ext x; simp [hG, hy]
      beta_reduce
      rw [this, measure_empty]; exact zero_le
  -- counted along horizontal sections: at least `ν p · μ T`
  have hdown : ν p * μ T ≤ μ.prod ν G := by
    rw [Measure.prod_apply hGm, ← lintegral_indicator_const hTm]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ T
    · rw [indicator_of_mem hx]
      have hx' : ν (p \ {y | (x, y) ∈ E}) = 0 := by
        have := hx; simp only [hT, mem_ofPred_eq] at this; rwa [hsec] at this
      have hmeas : MeasurableSet {y | (x, y) ∈ E} := measurable_prodMk_left hE
      have hsplit := measure_inter_add_sdiff p hmeas (μ := ν)
      rw [hx', add_zero] at hsplit
      have : Prod.mk x ⁻¹' G = p ∩ {y | (x, y) ∈ E} := by
        ext y; simp [hG, and_comm]
      beta_reduce
      rw [this, hsplit]
    · rw [indicator_of_notMem hx]; exact zero_le
  have hTle : μ T ≤ δ := by
    have := hdown.trans hup
    rw [mul_comm] at this
    exact (ENNReal.mul_le_mul_iff_left hνp hνp').mp this
  exact absurd (hA.trans_le ((measure_mono hAT).trans hTle)) (lt_irrefl _)

end PZFC.Fate
