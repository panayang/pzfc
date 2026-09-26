/-
  The lower Lipschitz envelope of a window sequence (notes/117, Lemma 3).

  Windows `W j` (j < n) and a slope `C₀ ≥ 0`.  The envelope is the inf-convolution
  `env t = min_{j < n} (W j + C₀ |t - j|)`.  It lies below every window, it is `C₀`-Lipschitz, and
  a set `R` of indices that are all far above the envelope ("no contact") cannot be long: at a
  point `t ∈ R` whose distance to every index outside `R` is at least `D`, one has
  `m + C₀ D < Γ m` when all windows are at least `m` and the windows in `R` are at most `Γ m`.
  Taking `t` in the middle of a run of length `g` gives `D ≥ g/2`, hence `C₀ g < 2 (Γ - 1) m`.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PZFC.Envelope

variable (W : ℕ → ℝ) (C₀ : ℝ) (n : ℕ) (hn : 0 < n)

/-- The lower `C₀`-Lipschitz envelope of `W` on the indices `j < n`. -/
noncomputable def env (t : ℝ) : ℝ :=
  (Finset.range n).inf' ⟨0, Finset.mem_range.2 hn⟩ (fun j => W j + C₀ * |t - j|)

/-- The envelope is below each cone `W j + C₀ |t - j|`, in particular below each window. -/
theorem env_le (t : ℝ) {j : ℕ} (hj : j < n) :
    env W C₀ n hn t ≤ W j + C₀ * |t - j| :=
  Finset.inf'_le _ (Finset.mem_range.2 hj)

theorem env_le_window {j : ℕ} (hj : j < n) : env W C₀ n hn j ≤ W j := by
  simpa using env_le W C₀ n hn (j : ℝ) hj

/-- The minimum is attained. -/
theorem env_attained (t : ℝ) :
    ∃ j, j < n ∧ env W C₀ n hn t = W j + C₀ * |t - j| := by
  obtain ⟨j, hj, h⟩ := Finset.exists_mem_eq_inf' ⟨0, Finset.mem_range.2 hn⟩
    (fun j : ℕ => W j + C₀ * |t - j|)
  exact ⟨j, Finset.mem_range.1 hj, h⟩

/-- The envelope is `C₀`-Lipschitz. -/
theorem env_lip (hC : 0 ≤ C₀) (s t : ℝ) :
    env W C₀ n hn t ≤ env W C₀ n hn s + C₀ * |t - s| := by
  obtain ⟨j, hj, hs⟩ := env_attained W C₀ n hn s
  have h1 := env_le W C₀ n hn t hj
  have h2 : |t - j| ≤ |s - j| + |t - s| := by
    calc |t - j| = |(t - s) + (s - j)| := by congr 1; ring
      _ ≤ |t - s| + |s - j| := abs_add_le _ _
      _ = |s - j| + |t - s| := add_comm _ _
  rw [hs]
  nlinarith [mul_le_mul_of_nonneg_left h2 hC]

/-- A minimizer of the envelope at any point is a contact: if every index of `R` is more than
`δ > 0` above the envelope, no index of `R` attains the envelope anywhere. -/
theorem minimizer_not_in (hC : 0 ≤ C₀) {δ : ℝ} (hδ : 0 < δ) (R : Set ℕ)
    (hR : ∀ j ∈ R, env W C₀ n hn j + δ < W j) (t : ℝ) {j : ℕ}
    (hj : env W C₀ n hn t = W j + C₀ * |t - j|) : j ∉ R := by
  intro hjR
  have hl := env_lip W C₀ n hn hC (j : ℝ) t
  have := hR j hjR
  linarith

/-- **No long non-contact runs.**  All windows are `≥ m`; the windows in the non-contact set `R`
are `≤ Γ m`; `t ∈ R` has distance `≥ D` to every index `< n` outside `R`.  Then
`m + C₀ D < Γ m`. -/
theorem no_contact_bound (hC : 0 ≤ C₀) {δ m Γ D : ℝ} (hδ : 0 < δ) (R : Set ℕ)
    (hR : ∀ j ∈ R, env W C₀ n hn j + δ < W j)
    (hm : ∀ j, j < n → m ≤ W j) (hΓ : ∀ j ∈ R, W j ≤ Γ * m)
    {t : ℕ} (ht : t ∈ R)
    (hD : ∀ j, j < n → j ∉ R → D ≤ |(t : ℝ) - j|) :
    m + C₀ * D < Γ * m := by
  obtain ⟨j, hj, he⟩ := env_attained W C₀ n hn (t : ℝ)
  have hjR := minimizer_not_in W C₀ n hn hC hδ R hR (t : ℝ) he
  have h1 : m + C₀ * D ≤ env W C₀ n hn t := by
    rw [he]
    have := mul_le_mul_of_nonneg_left (hD j hj hjR) hC
    linarith [hm j hj]
  have h2 := hR t ht
  have h3 := hΓ t ht
  linarith

/-- The run form: if `t ∈ R` and all indices within distance `< g/2` of `t` lie in `R`, then
`C₀ g < 2 (Γ - 1) m`. -/
theorem run_bound (hC : 0 ≤ C₀) {δ m Γ g : ℝ} (hδ : 0 < δ) (R : Set ℕ)
    (hR : ∀ j ∈ R, env W C₀ n hn j + δ < W j)
    (hm : ∀ j, j < n → m ≤ W j) (hΓ : ∀ j ∈ R, W j ≤ Γ * m)
    {t : ℕ} (ht : t ∈ R)
    (hrun : ∀ j, j < n → |(t : ℝ) - j| < g / 2 → j ∈ R) :
    C₀ * g < 2 * (Γ - 1) * m := by
  have hD : ∀ j, j < n → j ∉ R → g / 2 ≤ |(t : ℝ) - j| := by
    intro j hj hjR
    by_contra h
    exact hjR (hrun j hj (not_le.1 h))
  have := no_contact_bound W C₀ n hn hC hδ R hR hm hΓ ht hD
  linarith

end PZFC.Envelope
