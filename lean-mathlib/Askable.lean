/-
  Askable questions, and sources without records (notes/43).

  A source of records is a finite measure μ; the finite readings are a ring
  of sets G that generates the measurable sets (for bit sequences: the
  cylinders, decided by finitely many bits).

  §1  a question is askable when finite readings answer it with arbitrarily
      small error; askable questions are exactly the measurable ones (up to
      a null set) — measurability is not assumed, it is what askable means
  §2  for bit sequences: askable by finitely many bits ⟺ measurable
  §3  every finite part of a source has a record of positive weight;
      a source without atoms has no record: no single outcome answers all of
      its sure questions; for a record (a point source) every question is askable
  §4  records cannot predict a source when the tests are listable: a listable
      family of null tests is escaped by almost every reading; if every record
      is formable, each gives its own null test and no reading escapes them all
  §5  relations can be records when the relata are not: coupling an atomless
      source with itself, the joint source has no record, yet "the two agree"
      is sure; coupled independently, with the same parts, "the two agree"
      is surely false
  §6  fresh samples and local sets (notes/61): in a world whose points form a
      countable set, every local set of points is null for an atomless law, and a
      fresh sample almost surely lies outside the whole world; only a description
      (a measurable set not confined to the world's points) can be hit with
      positive probability
-/
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory Set Filter
open scoped ENNReal symmDiff

namespace PZFC.Asking

/-! ## 1. Askable questions -/

section General

variable {α : Type*} [mα : MeasurableSpace α]

/-- A question `A` is askable about the source `μ` with the finite readings `G`:
    for every `ε > 0`, some finite reading answers it wrongly with weight `< ε`
    (weights of arbitrary sets are outer weights). -/
def Askable (μ : Measure α) (G : Set (Set α)) (A : Set α) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ C ∈ G, μ (C ∆ A) < ε

/-- Measurable questions are askable. -/
theorem askable_of_nullMeasurable (μ : Measure α) [IsFiniteMeasure μ] {G : Set (Set α)}
    (hG : IsSetRing G) (hcover : ∃ D : Set (Set α), D.Countable ∧ D ⊆ G ∧ μ (⋃₀ D)ᶜ = 0)
    (hgen : mα = MeasurableSpace.generateFrom G) {A : Set α}
    (hA : NullMeasurableSet A μ) : Askable μ G A := by
  intro ε hε
  obtain ⟨C, hC, hlt⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing hG hcover hgen
    (measurableSet_toMeasurable μ A) hε
  refine ⟨C, hC, ?_⟩
  have hae : (C ∆ toMeasurable μ A : Set α) =ᵐ[μ] (C ∆ A : Set α) :=
    (EventuallyEq.refl _ C).symmDiff hA.toMeasurable_ae_eq
  rwa [← measure_congr hae]

omit mα in
/-- The Borel–Cantelli step: a question answered by finite readings with summable
    errors differs from the upper limit of those readings only on a null set. -/
theorem symmDiff_limsup_subset {C : ℕ → Set α} {A : Set α} :
    A ∆ limsup C atTop ⊆ limsup (fun n => C n ∆ A) atTop := by
  intro x hx
  rw [mem_limsup_iff_frequently_mem]
  rcases (mem_symmDiff.mp hx) with ⟨hxA, hxB⟩ | ⟨hxB, hxA⟩
  · rw [mem_limsup_iff_frequently_mem, not_frequently] at hxB
    exact (hxB.mono fun n hn => mem_symmDiff.mpr (Or.inr ⟨hxA, hn⟩)).frequently
  · rw [mem_limsup_iff_frequently_mem] at hxB
    exact hxB.mono fun n hn => mem_symmDiff.mpr (Or.inl ⟨hn, hxA⟩)

/-- Askable questions are measurable (up to a null set). -/
theorem nullMeasurable_of_askable (μ : Measure α) {G : Set (Set α)}
    (hGm : ∀ C ∈ G, MeasurableSet C) {A : Set α} (hA : Askable μ G A) :
    NullMeasurableSet A μ := by
  have hpos : ∀ n : ℕ, (0 : ℝ≥0∞) < 2⁻¹ ^ n := fun n =>
    ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) n
  choose C hCG hC using fun n : ℕ => hA (2⁻¹ ^ n) (hpos n)
  have hsum : ∑' n, μ (C n ∆ A) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => (hC n).le)
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (by norm_num)
  have hnull : μ (A ∆ limsup C atTop) = 0 :=
    measure_mono_null symmDiff_limsup_subset (measure_limsup_atTop_eq_zero hsum)
  have hB : MeasurableSet (limsup C atTop) :=
    MeasurableSet.measurableSet_limsup fun n => hGm _ (hCG n)
  refine hB.nullMeasurableSet.congr ?_
  rw [ae_eq_set]
  constructor
  · exact measure_mono_null (fun x hx => mem_symmDiff.mpr (Or.inr hx)) hnull
  · exact measure_mono_null (fun x hx => mem_symmDiff.mpr (Or.inl hx)) hnull

/-- Askable questions are exactly the measurable ones, up to a null set. -/
theorem askable_iff (μ : Measure α) [IsFiniteMeasure μ] {G : Set (Set α)}
    (hG : IsSetRing G) (hcover : ∃ D : Set (Set α), D.Countable ∧ D ⊆ G ∧ μ (⋃₀ D)ᶜ = 0)
    (hgen : mα = MeasurableSpace.generateFrom G) (hGm : ∀ C ∈ G, MeasurableSet C)
    (A : Set α) : Askable μ G A ↔ NullMeasurableSet A μ :=
  ⟨nullMeasurable_of_askable μ hGm, askable_of_nullMeasurable μ hG hcover hgen⟩

end General

/-! ## 2. Bit sequences: askable by finitely many bits -/

/-- For any finite source of bit sequences, a question can be answered with
    arbitrarily small error by finitely many bits exactly when it is measurable. -/
theorem bits_askable_iff (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] (A : Set (ℕ → Bool)) :
    Askable μ (measurableCylinders fun _ : ℕ => Bool) A ↔ NullMeasurableSet A μ := by
  refine askable_iff μ isSetRing_measurableCylinders ⟨{univ}, countable_singleton _, ?_, ?_⟩
    generateFrom_measurableCylinders.symm (fun C hC => ?_) A
  · simpa using univ_mem_measurableCylinders (fun _ : ℕ => Bool)
  · simp
  · rw [← generateFrom_measurableCylinders]
    exact MeasurableSpace.measurableSet_generateFrom hC

/-! ## 3. Records of a source -/

section Records

variable {α : Type*} [MeasurableSpace α]

/-- A record of a source: one outcome that answers every sure question of the
    source correctly (it lies in every set of full weight). -/
def IsRecordOf (μ : Measure α) (x : α) : Prop :=
  ∀ A, MeasurableSet A → μ Aᶜ = 0 → x ∈ A

/-- A source without atoms has no record. -/
theorem no_record [MeasurableSingletonClass α] (μ : Measure α) [NullSingletonClass μ] (x : α) :
    ¬ IsRecordOf μ x := by
  intro h
  exact (h {x}ᶜ (measurableSet_singleton x).compl (by simp)) rfl

/-- Every finite part of a source has an outcome of positive weight. -/
theorem finite_part_has_record [Finite α] [MeasurableSingletonClass α] (μ : Measure α)
    [IsProbabilityMeasure μ] : ∃ x : α, μ {x} ≠ 0 := by
  by_contra h
  push Not at h
  have : μ (⋃ x : α, {x}) = 0 := measure_iUnion_null h
  rw [iUnion_of_singleton, measure_univ] at this
  exact one_ne_zero this

/-- For a record — a point source — every question is measurable. -/
theorem dirac_all_nullMeasurable [MeasurableSingletonClass α] (x : α) (A : Set α) :
    NullMeasurableSet A (Measure.dirac x) := by
  by_cases hx : x ∈ A
  · refine MeasurableSet.univ.nullMeasurableSet.congr ?_
    rw [ae_eq_set]
    constructor
    · rw [Measure.dirac_apply]; simp [hx]
    · rw [Measure.dirac_apply]; simp
  · refine MeasurableSet.empty.nullMeasurableSet.congr ?_
    rw [ae_eq_set]
    constructor
    · rw [Measure.dirac_apply]; simp
    · rw [Measure.dirac_apply]; simp [hx]

end Records

/-- For a record of bits, every question is askable by finitely many bits. -/
theorem record_all_askable (x : ℕ → Bool) (A : Set (ℕ → Bool)) :
    Askable (Measure.dirac x) (measurableCylinders fun _ : ℕ => Bool) A :=
  (bits_askable_iff _ A).mpr (dirac_all_nullMeasurable x A)

/-! ## 4. Listable tests are escaped; formable-everything is not -/

section Predict

variable {α : Type*} [MeasurableSpace α]

/-- A listable family of null tests is escaped by almost every reading, and so by some. -/
theorem listable_tests_escaped (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ → Set α) (hN : ∀ i, μ (N i) = 0) :
    μ (⋃ i, N i) = 0 ∧ ∃ x, ∀ i, x ∉ N i := by
  have h0 : μ (⋃ i, N i) = 0 := measure_iUnion_null hN
  refine ⟨h0, ?_⟩
  by_contra h
  push Not at h
  have hu : (⋃ i, N i) = univ := eq_univ_of_forall fun x => mem_iUnion.mpr (h x)
  rw [hu, measure_univ] at h0
  exact one_ne_zero h0

/-- If every record is formable, each record is its own null test, and every reading
    is caught by one of them. -/
theorem all_records_formable (μ : Measure α) [NullSingletonClass μ] :
    (∀ x : α, μ {x} = 0) ∧ ∀ y : α, ∃ x : α, y ∈ ({x} : Set α) :=
  ⟨fun x => measure_singleton x, fun y => ⟨y, rfl⟩⟩

end Predict

/-! ## 5. Relations can be records when the relata are not -/

section Relations

variable {α : Type*} [MeasurableSpace α]

theorem measurable_dup : Measurable (fun x : α => (x, x)) := measurable_id.prodMk measurable_id

/-- The coupling of a source with itself in which both readings always agree. -/
noncomputable def sameCoupling (μ : Measure α) : Measure (α × α) :=
  μ.map (fun x => (x, x))

/-- Both parts of the agreeing coupling are the source itself. -/
theorem sameCoupling_fst (μ : Measure α) : (sameCoupling μ).map Prod.fst = μ := by
  rw [sameCoupling, Measure.map_map measurable_fst measurable_dup]
  exact Measure.map_id

/-- In the agreeing coupling, "the two readings agree" is sure. -/
theorem sameCoupling_agree_sure (μ : Measure α) (hD : MeasurableSet (Set.diagonal α)) :
    sameCoupling μ (Set.diagonal α)ᶜ = 0 := by
  rw [sameCoupling, Measure.map_apply measurable_dup hD.compl]
  have : (fun x : α => (x, x)) ⁻¹' (Set.diagonal α)ᶜ = ∅ := by
    ext x; simp
  rw [this, measure_empty]

/-- If the source has no atoms, neither has the agreeing coupling: it has no record. -/
theorem sameCoupling_no_atoms [MeasurableSingletonClass α] (μ : Measure α) [NullSingletonClass μ]
    [MeasurableSingletonClass (α × α)] (z : α × α) : sameCoupling μ {z} = 0 := by
  rw [sameCoupling, Measure.map_apply measurable_dup (measurableSet_singleton z)]
  refine measure_mono_null (fun x hx => ?_) (measure_singleton z.1)
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  simp [← hx]

/-- In the independent coupling of an atomless source with itself, "the two readings
    agree" has chance zero: same parts, the opposite sure fact. -/
theorem independent_agree_null [MeasurableSingletonClass α] (μ : Measure α) [SFinite μ]
    [NullSingletonClass μ] (hD : MeasurableSet (Set.diagonal α)) :
    (μ.prod μ) (Set.diagonal α) = 0 := by
  rw [Measure.prod_apply hD]
  have : ∀ x : α, μ (Prod.mk x ⁻¹' Set.diagonal α) = 0 := by
    intro x
    have hx : Prod.mk x ⁻¹' Set.diagonal α = {x} := by
      ext y; simp [Set.mem_diagonal_iff, eq_comm]
    rw [hx, measure_singleton]
  simp [this]

end Relations

/-! ## 6. Fresh samples and local sets -/

section Fresh

variable {α : Type*} [MeasurableSpace α]

/-- In a world whose points form a countable set, every local set of points is null for an
    atomless law. -/
theorem local_set_null (μ : Measure α) [NullSingletonClass μ] {W A : Set α}
    (hW : W.Countable) (hA : A ⊆ W) : μ A = 0 :=
  measure_mono_null hA (hW.measure_zero μ)

/-- **A fresh sample almost surely lies outside the whole world.** -/
theorem fresh_sample_outside (μ : Measure α) [NullSingletonClass μ] {W : Set α}
    (hW : W.Countable) : ∀ᵐ x ∂μ, x ∉ W :=
  measure_eq_zero_iff_ae_notMem.mp (hW.measure_zero μ)

/-- **Only a description can be hit**: a measurable set of positive weight is hit by a fresh
    sample with positive probability, and so it is not confined to the world's points. -/
theorem description_not_local (μ : Measure α) [NullSingletonClass μ] {W B : Set α}
    (hW : W.Countable) (hB : μ B ≠ 0) : ¬ B ⊆ W :=
  fun hsub => hB (local_set_null μ hW hsub)

end Fresh

end PZFC.Asking
