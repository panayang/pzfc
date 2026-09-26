/-
  The finite parts of the rigidity proofs (notes/94, 97, 98).

  §1  Three-block sandwich (notes/97, Lemma 6): if the first block sends a fixed proportion of
      every row into a set S, the last block receives a fixed proportion of every column from a
      set V, and the middle block is bounded above everywhere and below on S × V, then the product
      is squeezed between two multiples of (row sum) × (column sum).
  §2  Squeezed matrices have bounded cross-ratios (hence bounded Birkhoff diameter).
  §3  Corner formula (notes/94, Theorem 1; notes/98, Lemma 11): for a log-supermodular (TP₂)
      array, every ordered cross-ratio is bounded by the cross-ratio of the four corners.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace PZFC.Sandwich

open Finset

/-! ## §1 Three-block sandwich -/

section Sandwich

variable {ι κ ρ υ : Type*} [Fintype κ] [Fintype ρ]

/-- The product `A Q C` of three nonnegative kernels, written out. -/
def triple (A : ι → κ → ℝ) (Q : κ → ρ → ℝ) (C : ρ → υ → ℝ) (d : ι) (u : υ) : ℝ :=
  ∑ s, ∑ v, A d s * Q s v * C v u

/-- Upper half of the sandwich: `M(d,u) ≤ β₊ · a(d) · b(u)`. -/
theorem triple_le (A : ι → κ → ℝ) (Q : κ → ρ → ℝ) (C : ρ → υ → ℝ)
    (hA : ∀ d s, 0 ≤ A d s) (hC : ∀ v u, 0 ≤ C v u) {βhi : ℝ} (hQ : ∀ s v, Q s v ≤ βhi)
    (d : ι) (u : υ) :
    triple A Q C d u ≤ βhi * ((∑ s, A d s) * (∑ v, C v u)) := by
  unfold triple
  calc ∑ s, ∑ v, A d s * Q s v * C v u
      ≤ ∑ s, ∑ v, A d s * βhi * C v u := by
        apply sum_le_sum; intro s _
        apply sum_le_sum; intro v _
        have := mul_le_mul_of_nonneg_left (hQ s v) (hA d s)
        exact mul_le_mul_of_nonneg_right this (hC v u)
    _ = βhi * ((∑ s, A d s) * (∑ v, C v u)) := by
        rw [sum_mul_sum, mul_sum]
        apply sum_congr rfl; intro s _
        rw [mul_sum]
        apply sum_congr rfl; intro v _
        ring

/-- Lower half of the sandwich: `ε² β₋ · a(d) · b(u) ≤ M(d,u)`. -/
theorem le_triple (A : ι → κ → ℝ) (Q : κ → ρ → ℝ) (C : ρ → υ → ℝ)
    (hA : ∀ d s, 0 ≤ A d s) (hQ0 : ∀ s v, 0 ≤ Q s v) (hC : ∀ v u, 0 ≤ C v u)
    (S : Finset κ) (V : Finset ρ) {ε βlo : ℝ} (hε : 0 ≤ ε) (hβ : 0 ≤ βlo)
    (hS : ∀ d, ε * ∑ s, A d s ≤ ∑ s ∈ S, A d s)
    (hV : ∀ u, ε * ∑ v, C v u ≤ ∑ v ∈ V, C v u)
    (hQlo : ∀ s ∈ S, ∀ v ∈ V, βlo ≤ Q s v) (d : ι) (u : υ) :
    ε ^ 2 * βlo * ((∑ s, A d s) * (∑ v, C v u)) ≤ triple A Q C d u := by
  have hAS : 0 ≤ ∑ s ∈ S, A d s := sum_nonneg fun s _ => hA d s
  have hCV : 0 ≤ ∑ v ∈ V, C v u := sum_nonneg fun v _ => hC v u
  have hAall : 0 ≤ ∑ s, A d s := sum_nonneg fun s _ => hA d s
  have hCall : 0 ≤ ∑ v, C v u := sum_nonneg fun v _ => hC v u
  -- restrict both sums to `S` and `V`
  have hrestrict : ∑ s ∈ S, ∑ v ∈ V, A d s * Q s v * C v u ≤ triple A Q C d u := by
    unfold triple
    calc ∑ s ∈ S, ∑ v ∈ V, A d s * Q s v * C v u
        ≤ ∑ s ∈ S, ∑ v, A d s * Q s v * C v u := by
          apply sum_le_sum; intro s _
          exact sum_le_sum_of_subset_of_nonneg (subset_univ V)
            (fun v _ _ => mul_nonneg (mul_nonneg (hA d s) (hQ0 s v)) (hC v u))
      _ ≤ ∑ s, ∑ v, A d s * Q s v * C v u :=
          sum_le_sum_of_subset_of_nonneg (subset_univ S)
            (fun s _ _ => sum_nonneg fun v _ => mul_nonneg (mul_nonneg (hA d s) (hQ0 s v)) (hC v u))
  -- replace `Q` by its lower bound on `S × V`
  have hlow : βlo * ((∑ s ∈ S, A d s) * (∑ v ∈ V, C v u))
      ≤ ∑ s ∈ S, ∑ v ∈ V, A d s * Q s v * C v u := by
    rw [sum_mul_sum, mul_sum]
    apply sum_le_sum; intro s hs
    rw [mul_sum]
    apply sum_le_sum; intro v hv
    have := mul_le_mul_of_nonneg_left (hQlo s hs v hv) (hA d s)
    have := mul_le_mul_of_nonneg_right this (hC v u)
    nlinarith [this]
  -- use the proportions `ε`
  have hprop : ε * (∑ s, A d s) * (ε * (∑ v, C v u))
      ≤ (∑ s ∈ S, A d s) * (∑ v ∈ V, C v u) :=
    mul_le_mul (hS d) (hV u) (mul_nonneg hε hCall) hAS
  calc ε ^ 2 * βlo * ((∑ s, A d s) * (∑ v, C v u))
      = βlo * (ε * (∑ s, A d s) * (ε * (∑ v, C v u))) := by ring
    _ ≤ βlo * ((∑ s ∈ S, A d s) * (∑ v ∈ V, C v u)) := mul_le_mul_of_nonneg_left hprop hβ
    _ ≤ _ := hlow.trans hrestrict

end Sandwich

/-! ## §2 Squeezed arrays have bounded cross-ratios -/

/-- If `c·a(d)·b(u) ≤ M(d,u) ≤ C·a(d)·b(u)` with positive `a, b, c`, then every cross-ratio of
`M` is at most `(C/c)²`, written without division. -/
theorem cross_le {ι υ : Type*} (M : ι → υ → ℝ) (a : ι → ℝ) (b : υ → ℝ) {c C : ℝ}
    (hc : 0 < c) (ha : ∀ d, 0 < a d) (hb : ∀ u, 0 < b u)
    (hlo : ∀ d u, c * (a d * b u) ≤ M d u) (hhi : ∀ d u, M d u ≤ C * (a d * b u))
    (d d' : ι) (u u' : υ) :
    c ^ 2 * (M d u * M d' u') ≤ C ^ 2 * (M d' u * M d u') := by
  have hC : 0 ≤ C := by
    have h1 := (hlo d u).trans (hhi d u)
    have hp : 0 < a d * b u := mul_pos (ha d) (hb u)
    nlinarith
  have p1 : 0 ≤ a d * b u := (mul_pos (ha d) (hb u)).le
  have p2 : 0 ≤ a d' * b u' := (mul_pos (ha d') (hb u')).le
  have p3 : 0 ≤ a d' * b u := (mul_pos (ha d') (hb u)).le
  have p4 : 0 ≤ a d * b u' := (mul_pos (ha d) (hb u')).le
  have m1 : 0 ≤ M d u := le_trans (mul_nonneg hc.le p1) (hlo d u)
  have m3 : 0 ≤ M d' u := le_trans (mul_nonneg hc.le p3) (hlo d' u)
  -- upper bound of the numerator, lower bound of the denominator
  have num : M d u * M d' u' ≤ (C * (a d * b u)) * (C * (a d' * b u')) :=
    mul_le_mul (hhi d u) (hhi d' u') (le_trans (mul_nonneg hc.le p2) (hlo d' u'))
      (mul_nonneg hC p1)
  have den : (c * (a d' * b u)) * (c * (a d * b u')) ≤ M d' u * M d u' :=
    mul_le_mul (hlo d' u) (hlo d u') (mul_nonneg hc.le p4) m3
  have key : (C * (a d * b u)) * (C * (a d' * b u'))
      = C ^ 2 * (a d * b u * (a d' * b u')) := by ring
  have key' : (c * (a d' * b u)) * (c * (a d * b u'))
      = c ^ 2 * (a d * b u * (a d' * b u')) := by ring
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  calc c ^ 2 * (M d u * M d' u')
      ≤ c ^ 2 * (C ^ 2 * (a d * b u * (a d' * b u'))) :=
        mul_le_mul_of_nonneg_left (num.trans_eq key) hc2
    _ = C ^ 2 * (c ^ 2 * (a d * b u * (a d' * b u'))) := by ring
    _ ≤ C ^ 2 * (M d' u * M d u') :=
        mul_le_mul_of_nonneg_left (key'.symm.le.trans den) hC2

/-! ## §3 Corner formula for log-supermodular arrays -/

section Corner

variable {ι κ : Type*} [Preorder ι] [Preorder κ]

/-- The log cross-ratio of rows `i, i'` and columns `j, j'` of `f = log M`. -/
def lcr (f : ι → κ → ℝ) (i i' : ι) (j j' : κ) : ℝ := f i j + f i' j' - f i j' - f i' j

/-- `f` is supermodular (`M = exp f` is TP₂): ordered log cross-ratios are nonnegative. -/
def Supermodular (f : ι → κ → ℝ) : Prop :=
  ∀ i i' j j', i ≤ i' → j ≤ j' → 0 ≤ lcr f i i' j j'

omit [Preorder ι] [Preorder κ] in
/-- Log cross-ratios add along rows. -/
theorem lcr_rows (f : ι → κ → ℝ) (a b c : ι) (j j' : κ) :
    lcr f a c j j' = lcr f a b j j' + lcr f b c j j' := by unfold lcr; ring

omit [Preorder ι] [Preorder κ] in
/-- Log cross-ratios add along columns. -/
theorem lcr_cols (f : ι → κ → ℝ) (i i' : ι) (a b c : κ) :
    lcr f i i' a c = lcr f i i' a b + lcr f i i' b c := by unfold lcr; ring

/-- Corner formula: for supermodular `f`, every ordered log cross-ratio inside the box
`[i₀, i₁] × [j₀, j₁]` is at most the log cross-ratio of the four corners. -/
theorem lcr_le_corners {f : ι → κ → ℝ} (hf : Supermodular f)
    {i₀ i i' i₁ : ι} {j₀ j j' j₁ : κ}
    (h1 : i₀ ≤ i) (h2 : i ≤ i') (h3 : i' ≤ i₁) (k1 : j₀ ≤ j) (k2 : j ≤ j') (k3 : j' ≤ j₁) :
    lcr f i i' j j' ≤ lcr f i₀ i₁ j₀ j₁ := by
  -- first widen the rows, then the columns
  have r : lcr f i₀ i₁ j j' = lcr f i₀ i j j' + lcr f i i' j j' + lcr f i' i₁ j j' := by
    rw [lcr_rows f i₀ i i₁, lcr_rows f i i' i₁]; ring
  have rows : lcr f i i' j j' ≤ lcr f i₀ i₁ j j' := by
    have := hf i₀ i j j' h1 k2
    have := hf i' i₁ j j' h3 k2
    linarith
  have c : lcr f i₀ i₁ j₀ j₁ = lcr f i₀ i₁ j₀ j + lcr f i₀ i₁ j j' + lcr f i₀ i₁ j' j₁ := by
    rw [lcr_cols f i₀ i₁ j₀ j j₁, lcr_cols f i₀ i₁ j j' j₁]; ring
  have hrow : i₀ ≤ i₁ := h1.trans (h2.trans h3)
  have := hf i₀ i₁ j₀ j hrow k1
  have := hf i₀ i₁ j' j₁ hrow k3
  linarith

/-- In particular ordered log cross-ratios are bounded by the corner one, and the maximum over
the box is attained at the corners. -/
theorem corner_is_max {f : ι → κ → ℝ} (hf : Supermodular f) {i₀ i₁ : ι} {j₀ j₁ : κ}
    (hi : i₀ ≤ i₁) (hj : j₀ ≤ j₁) :
    0 ≤ lcr f i₀ i₁ j₀ j₁ := hf _ _ _ _ hi hj

end Corner

end PZFC.Sandwich
