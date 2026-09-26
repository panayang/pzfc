/-
  Weights as answers, and the first layer of GLU for weights (notes/31).
  Uses Mathlib (classical logic).

  §1  answers that are weights: the weight with which `b` is a member of the
      value of `x` is the sum of the weights of the children of `x` that land on
      `b`.  Keeping only whether a weight is nonzero is a map of value structures
      (a sum is nonzero exactly when some term is), so the shadow of a weighted
      solution is a sharp solution: existence is the shadow of weight;
  §2  the shadow forgets multiplicity: two children of weight one landing on the
      same member make it weigh two, which the sharp shadow cannot see;
  §3  the first layer of GLU for weights (Kolmogorov, localized): over the
      directed contexts given by finite sets of questions, two finite global
      weights with the same local weights are equal, and independent local
      probability weights glue — the product measure.
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open MeasureTheory ENNReal

namespace PZFC.WeightedGlue

universe u

/-! ## 1. Existence is the shadow of weight -/

/-- A weighted solution: the weight of `b` among the members of `f x` is the sum
    of the weights of the children of `x` that land on `b`. -/
def WSolves {A : Type} {B : Type u} (R : A → A → ℝ≥0∞) (E : B → B → ℝ≥0∞) (f : A → B) : Prop :=
  ∀ x b, E b (f x) = ∑' z : {z : A // f z = b}, R z.1 x

/-- A sharp solution, as `Shapes.Solves`. -/
def Solves {A : Type} {B : Type u} (R : A → A → Prop) (E : B → B → Prop) (f : A → B) : Prop :=
  ∀ x b, E b (f x) ↔ ∃ z, R z x ∧ f z = b

/-- The shadow of a weight: whether it is nonzero. -/
def supp (w : ℝ≥0∞) : Prop := w ≠ 0

/-- The shadow respects "one of the family": a sum is nonzero exactly when some
    term is. -/
theorem supp_tsum {ι : Type} (f : ι → ℝ≥0∞) : supp (∑' i, f i) ↔ ∃ i, supp (f i) := by
  unfold supp
  rw [Ne, ENNReal.tsum_eq_zero, not_forall]

/-- **Existence is the shadow of weight**: the shadow of a weighted solution is a
    sharp solution. -/
theorem wsolves_shadow {A : Type} {B : Type u} {R : A → A → ℝ≥0∞} {E : B → B → ℝ≥0∞}
    {f : A → B} (h : WSolves R E f) :
    Solves (fun z x => supp (R z x)) (fun b a => supp (E b a)) f := by
  intro x b
  show supp (E b (f x)) ↔ ∃ z, supp (R z x) ∧ f z = b
  rw [h x b, supp_tsum]
  constructor
  · rintro ⟨⟨z, hz⟩, hR⟩
    exact ⟨z, hR, hz⟩
  · rintro ⟨z, hR, hz⟩
    exact ⟨⟨z, hz⟩, hR⟩

/-! ## 2. The shadow forgets multiplicity -/

/-- **The shadow forgets multiplicity**: when exactly two children, each of weight
    one, land on the same member, that member weighs two — while the sharp shadow
    only says that it is a member. -/
theorem two_children {A : Type} {B : Type u} {R : A → A → ℝ≥0∞} {E : B → B → ℝ≥0∞}
    {f : A → B} (h : WSolves R E f) {x z₁ z₂ : A} {b : B} (hne : z₁ ≠ z₂) (h₁ : f z₁ = b)
    (h₂ : f z₂ = b) (hR₁ : R z₁ x = 1) (hR₂ : R z₂ x = 1)
    (honly : ∀ z, f z = b → z = z₁ ∨ z = z₂) : E b (f x) = 2 := by
  classical
  have hsub : (∑' z : {z : A // f z = b}, R z.1 x) =
      ∑' z, Set.indicator {z | f z = b} (fun z => R z x) z :=
    tsum_subtype {z | f z = b} (fun z => R z x)
  rw [h x b, hsub, tsum_eq_sum (s := {z₁, z₂})]
  · rw [Finset.sum_pair hne, Set.indicator_of_mem (show z₁ ∈ {z | f z = b} from h₁),
      Set.indicator_of_mem (show z₂ ∈ {z | f z = b} from h₂), hR₁, hR₂]
    exact one_add_one_eq_two
  · intro z hz
    apply Set.indicator_of_notMem
    intro hzb
    rcases honly z hzb with rfl | rfl <;> simp at hz

/-! ## 3. The first layer of GLU for weights: Kolmogorov, localized -/

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- **Global weights are unique**: over the directed contexts given by finite sets
    of questions, two finite global weights with the same local weights are equal. -/
theorem global_weight_unique {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}
    [∀ J, IsFiniteMeasure (P J)] {μ ν : Measure (∀ i, α i)}
    (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P) : μ = ν :=
  hμ.unique hν

/-- **Independent local weights glue**: the product of probability weights is a
    global weight whose restriction to every finite set of questions is the local
    product. -/
theorem independent_weights_glue (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)] :
    IsProjectiveLimit (Measure.infinitePi μ) (fun I : Finset ι => Measure.pi (fun i : I => μ i)) :=
  Measure.isProjectiveLimit_infinitePi μ

end PZFC.WeightedGlue
