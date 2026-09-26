/-
  The Fubini step of the covering obstruction (notes/100, Theorem 2).

  A family of null sets `N_z = {a | (a, z) ∈ E}` indexed by `z`, and a measure `π` on the
  indices: if every `N_z` is `μ`-null, then for `μ`-almost every point `a`, the set of indices
  whose null set covers `a` is `π`-null.  So a code that is typical for `π` covers only a null set
  of old points.
-/
import Mathlib.MeasureTheory.Measure.Prod

namespace PZFC.Window

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (μ : Measure α) (π : Measure β) [SFinite μ] [SFinite π]

/-- If every section `{a | (a, z) ∈ E}` is `μ`-null, then for `μ`-a.e. `a` the section
`{z | (a, z) ∈ E}` is `π`-null. -/
theorem ae_cover_null {E : Set (α × β)} (hE : MeasurableSet E)
    (hN : ∀ z, μ {a | (a, z) ∈ E} = 0) :
    ∀ᵐ a ∂μ, π {z | (a, z) ∈ E} = 0 := by
  -- the product measure of `E` vanishes, computed by integrating over `z`
  have hprod : (μ.prod π) E = 0 := by
    rw [Measure.prod_apply_symm hE]
    have : (fun z => μ ((fun a => (a, z)) ⁻¹' E)) = fun _ => 0 := by
      funext z; exact hN z
    simp [this]
  -- and then over `a`
  have := (Measure.measure_prod_null hE).1 hprod
  filter_upwards [this] with a ha
  exact ha

/-- The set of points covered by a positive `π`-proportion of the null sets is `μ`-null. -/
theorem covered_null {E : Set (α × β)} (hE : MeasurableSet E)
    (hN : ∀ z, μ {a | (a, z) ∈ E} = 0) :
    μ {a | π {z | (a, z) ∈ E} ≠ 0} = 0 := by
  have := ae_cover_null μ π hE hN
  rw [Filter.Eventually, mem_ae_iff] at this
  simpa [Set.compl_ofPred] using this

end PZFC.Window
