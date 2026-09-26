/-
  Killing without Cohen reals (notes/70).

  A real is "not split" by a set of natural numbers `m` when, along `m`, it is eventually
  constant.  If a new infinite set `m` is not split by any old real (a Mathias real has this
  property), every old real lies in the set of reals eventually constant along `m`.  This file
  proves that this set is null for any product of coins whose point masses stay below some
  `q < 1`.  So such a recording makes every old set of reals null, although (a known fact about
  Mathias forcing) it adds no Cohen real.
-/
import Mathlib.Probability.ProductMeasure

namespace PZFC.Kill

open MeasureTheory Set Filter
open scoped ENNReal

/-- Along `m`, the 0-1 sequence `x` is eventually constant: `x` does not split `m`. -/
def NotSplit (x : ℕ → Bool) (m : Set ℕ) : Prop := ∃ N b, ∀ k ∈ m, N ≤ k → x k = b

/-- The sequences eventually constant along `m`. -/
def EvConst (m : Set ℕ) : Set (ℕ → Bool) := {x | NotSplit x m}

variable (μ : ℕ → Measure Bool) [∀ i, IsProbabilityMeasure (μ i)]

/-- One piece: constant equal to `b` along `m` from `N` on. -/
theorem piece_null {q : ℝ≥0∞} (hq : q < 1) (hμ : ∀ i b, μ i {b} ≤ q) {m : Set ℕ}
    (hm : m.Infinite) (N : ℕ) (b : Bool) :
    Measure.infinitePi μ {x | ∀ k ∈ m, N ≤ k → x k = b} = 0 := by
  have hinf : (m \ Iio N).Infinite := hm.sdiff (finite_Iio N)
  have hle : ∀ n : ℕ, Measure.infinitePi μ {x | ∀ k ∈ m, N ≤ k → x k = b} ≤ q ^ n := by
    intro n
    obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq n
    have hsub : {x : ℕ → Bool | ∀ k ∈ m, N ≤ k → x k = b} ⊆ Set.pi (s : Set ℕ) (fun _ => {b}) := by
      intro x hx k hk
      have hk' := hs hk
      simp only [Set.mem_sdiff, mem_Iio, not_lt] at hk'
      exact hx k hk'.1 hk'.2
    calc Measure.infinitePi μ {x | ∀ k ∈ m, N ≤ k → x k = b}
        ≤ Measure.infinitePi μ (Set.pi (s : Set ℕ) (fun _ => {b})) := measure_mono hsub
      _ = ∏ i ∈ s, μ i {b} := Measure.infinitePi_pi μ (fun i _ => measurableSet_singleton b)
      _ ≤ ∏ _i ∈ s, q := Finset.prod_le_prod' (fun i _ => hμ i b)
      _ = q ^ n := by rw [Finset.prod_const, hcard]
  have h0 := ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) hle
  exact le_antisymm h0 zero_le

/-- **The sequences eventually constant along an infinite set form a null set.** -/
theorem evConst_null {q : ℝ≥0∞} (hq : q < 1) (hμ : ∀ i b, μ i {b} ≤ q) {m : Set ℕ}
    (hm : m.Infinite) : Measure.infinitePi μ (EvConst m) = 0 := by
  have : EvConst m = ⋃ N : ℕ, ⋃ b : Bool, {x : ℕ → Bool | ∀ k ∈ m, N ≤ k → x k = b} := by
    ext x; simp [EvConst, NotSplit]
  rw [this, measure_iUnion_null_iff]
  intro N
  rw [measure_iUnion_null_iff]
  intro b
  exact piece_null μ hq hμ hm N b

/-- **An unsplit set kills every set it is not split by.**  If no member of `A` splits the infinite
    set `m`, then `A` is null. -/
theorem unsplit_kills {q : ℝ≥0∞} (hq : q < 1) (hμ : ∀ i b, μ i {b} ≤ q) {m : Set ℕ}
    (hm : m.Infinite) (A : Set (ℕ → Bool)) (hA : ∀ x ∈ A, NotSplit x m) :
    Measure.infinitePi μ A = 0 :=
  measure_mono_null (fun x hx => hA x hx) (evConst_null μ hq hμ hm)

end PZFC.Kill
