/-
  Finite parts of the closing rounds (notes/121–124).

  §1  Plateau crossings (notes/124, Theorem D): a kernel squeezed between half of a product-form
      kernel and the kernel itself has bounded cross-ratios.
  §2  The Weyl-chamber corner (notes/123 §3.2): for the walk that advances one of `m` chains, the
      Vandermonde product is an exact harmonic function; written out for m = 4 (m = 3 is
      `Corner.harmonic`).
  §3  Scalar metrics are linear extensions (notes/121 §4.2): a partial order is exactly what all
      its linear extensions have in common (Szpilrajn, Dushnik–Miller), and a single faithful
      scalar exists only for a total order.
  §4  Triggers (notes/121 §3.2): a sequence of rare trigger sets with summable measure catches
      almost every point only finitely often (Borel–Cantelli).
-/
import Sandwich
import Mathlib.Order.Extension.Linear
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace PZFC.Closure

/-! ## §1 Plateau crossings -/

/-- If `c·a·b ≤ q ≤ C·a·b` and `q/2 ≤ M ≤ q`, then every cross-ratio of `M` is at most
`(2C/c)²`. -/
theorem plateau_cross {ι υ : Type*} (M q : ι → υ → ℝ) (a : ι → ℝ) (b : υ → ℝ) {c C : ℝ}
    (hc : 0 < c) (ha : ∀ d, 0 < a d) (hb : ∀ u, 0 < b u)
    (hqlo : ∀ d u, c * (a d * b u) ≤ q d u) (hqhi : ∀ d u, q d u ≤ C * (a d * b u))
    (hMlo : ∀ d u, q d u / 2 ≤ M d u) (hMhi : ∀ d u, M d u ≤ q d u)
    (d d' : ι) (u u' : υ) :
    (c / 2) ^ 2 * (M d u * M d' u') ≤ C ^ 2 * (M d' u * M d u') := by
  refine PZFC.Sandwich.cross_le M a b (by linarith) ha hb (fun d u => ?_) (fun d u => ?_) d d' u u'
  · have := hqlo d u; have := hMlo d u; linarith
  · exact (hMhi d u).trans (hqhi d u)

/-! ## §2 The Weyl-chamber corner -/

/-- The Vandermonde product of four chain positions. -/
def vdm4 (x₁ x₂ x₃ x₄ : ℤ) : ℤ :=
  (x₁ - x₂) * (x₁ - x₃) * (x₁ - x₄) * (x₂ - x₃) * (x₂ - x₄) * (x₃ - x₄)

/-- Advancing each of the four chains once and averaging gives the Vandermonde back: it is an
exact harmonic function of the walk (König–O'Connell–Roch). -/
theorem vdm4_harmonic (x₁ x₂ x₃ x₄ : ℤ) :
    vdm4 (x₁ + 1) x₂ x₃ x₄ + vdm4 x₁ (x₂ + 1) x₃ x₄ + vdm4 x₁ x₂ (x₃ + 1) x₄
      + vdm4 x₁ x₂ x₃ (x₄ + 1) = 4 * vdm4 x₁ x₂ x₃ x₄ := by
  unfold vdm4; ring

/-- The Vandermonde product vanishes on the walls of the Weyl chamber. -/
theorem vdm4_wall (x₁ x₃ x₄ : ℤ) : vdm4 x₁ x₁ x₃ x₄ = 0 := by
  unfold vdm4; ring

/-! ## §3 Scalar metrics are linear extensions -/

section Metrics

variable {α : Type*} [PartialOrder α]

/-- If `a ≰ b`, some linear extension of the order puts `b` strictly below `a`. -/
theorem exists_linear_ext_flip {a b : α} (hab : ¬ a ≤ b) :
    ∃ s : α → α → Prop, IsLinearOrder α s ∧ (∀ x y, x ≤ y → s x y) ∧ s b a ∧ ¬ s a b := by
  -- the order with the extra pair `b < a` added, closed under transitivity
  let r : α → α → Prop := fun x y => x ≤ y ∨ (x ≤ b ∧ a ≤ y)
  have hrefl : ∀ x, r x x := fun x => Or.inl le_rfl
  have htrans : ∀ x y z, r x y → r y z → r x z := by
    rintro x y z (hxy | ⟨hxb, hay⟩) (hyz | ⟨hyb, haz⟩)
    · exact Or.inl (hxy.trans hyz)
    · exact Or.inr ⟨hxy.trans hyb, haz⟩
    · exact Or.inr ⟨hxb, hay.trans hyz⟩
    · exact absurd (hay.trans hyb) hab
  have hanti : ∀ x y, r x y → r y x → x = y := by
    rintro x y (hxy | ⟨hxb, hay⟩) (hyx | ⟨hyb, hax⟩)
    · exact le_antisymm hxy hyx
    · exact absurd ((hax.trans hxy).trans hyb) hab
    · exact absurd ((hay.trans hyx).trans hxb) hab
    · exact absurd (hay.trans hyb) hab
  have : IsPartialOrder α r :=
    { refl := hrefl, trans := htrans, antisymm := hanti }
  obtain ⟨s, hs, hrs⟩ := extend_partialOrder r
  have hba : s b a := hrs b a (Or.inr ⟨le_rfl, le_rfl⟩)
  refine ⟨s, hs, fun x y hxy => hrs x y (Or.inl hxy), hba, fun hsab => ?_⟩
  have hne : a ≠ b := fun h => hab (h ▸ le_rfl)
  exact hne (hs.antisymm a b hsab hba)

/-- **A partial order is what all its linear extensions have in common** (Szpilrajn,
Dushnik–Miller): `a ≤ b` iff every linear extension puts `a` below `b`. -/
theorem le_iff_all_linear_ext (a b : α) :
    a ≤ b ↔ ∀ s : α → α → Prop, IsLinearOrder α s → (∀ x y, x ≤ y → s x y) → s a b := by
  constructor
  · intro hab s _ hext; exact hext a b hab
  · intro h
    by_contra hab
    obtain ⟨s, hs, hext, _, hnot⟩ := exists_linear_ext_flip hab
    exact hnot (h s hs hext)

/-- A single faithful scalar metric forces the order to be total. -/
theorem total_of_faithful_scalar (f : α → ℝ) (hf : ∀ a b, a ≤ b ↔ f a ≤ f b) (a b : α) :
    a ≤ b ∨ b ≤ a := by
  rcases le_total (f a) (f b) with h | h
  · exact Or.inl ((hf a b).2 h)
  · exact Or.inr ((hf b a).2 h)

end Metrics

/-! ## §4 Triggers -/

open MeasureTheory Filter in
/-- Rare triggers (summable measure) catch almost every point only finitely often. -/
theorem trigger_blind {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (T : ℕ → Set Ω)
    (hT : ∑' n, μ (T n) ≠ ⊤) : μ (limsup T atTop) = 0 :=
  measure_limsup_atTop_eq_zero hT

end PZFC.Closure
