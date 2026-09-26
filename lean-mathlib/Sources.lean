/-
  Sources given point-free (notes/44): T₀ at the finite levels.

  A source of bits is not a measure on a set of points.  It is, for each n,
  a law on the readings of its first n answers, consistent from one level to
  the next.  Infinite answer sequences are not primitive; a record of the
  source is defined, and may not exist.

  §1  sources, readings, the fair coin
  §2  the law of a reading does not depend on the level it is read at
  §3  records are exactly the atoms: an answer sequence answers every
      sufficiently sure reading correctly iff its weights stay above a bound
  §4  every level has an outcome of positive weight; the fair coin has no record
  §5  a source has a record exactly when two independent readings agree on
      every level with a probability bounded away from zero: a record is an
      answer that re-reading reproduces (notes/42 §2), now as a theorem
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic

open scoped ENNReal BigOperators
open Finset

namespace PZFC.Sources

/-! ## 1. Sources -/

/-- A source of bits, point-free: for each `n` a law on the readings of the first
    `n` answers; each reading splits into its two refinements. -/
structure Source where
  p : (n : ℕ) → (Fin n → Bool) → ℝ≥0∞
  total : ∀ n, ∑ w, p n w = 1
  refine : ∀ n (w : Fin n → Bool), p n w = p (n + 1) (Fin.snoc w false) + p (n + 1) (Fin.snoc w true)

/-- The fair coin: every reading of length `n` has weight `2⁻¹ ^ n`. -/
noncomputable def coin : Source where
  p n _ := 2⁻¹ ^ n
  total n := by
    rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, ← mul_pow, Nat.cast_ofNat,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  refine n _ := by
    rw [pow_succ, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

/-! ## 2. The law of a reading does not depend on the level -/

/-- A reading of the first `n` answers, read again at level `n + 1`, has the same law. -/
theorem lift_law (s : Source) (n : ℕ) (a : Finset (Fin n → Bool)) :
    (∑ w' : Fin (n + 1) → Bool, if Fin.init w' ∈ a then s.p (n + 1) w' else 0)
      = ∑ w ∈ a, s.p n w := by
  have h := Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool))
    (fun q => (fun w' : Fin (n + 1) → Bool => if Fin.init w' ∈ a then s.p (n + 1) w' else 0)
      ((Fin.snocEquiv (fun _ => Bool)) q))
    (fun w' => if Fin.init w' ∈ a then s.p (n + 1) w' else 0) (fun _ => rfl)
  rw [← h, Fintype.sum_prod_type, Finset.sum_comm]
  have hw : ∀ w : Fin n → Bool,
      (∑ b : Bool, (fun w' : Fin (n + 1) → Bool => if Fin.init w' ∈ a then s.p (n + 1) w' else 0)
        ((Fin.snocEquiv (fun _ => Bool)) (b, w))) = if w ∈ a then s.p n w else 0 := by
    intro w
    have e : ∀ b : Bool, (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)) (b, w) = Fin.snoc w b :=
      fun _ => rfl
    simp only [e, Fin.init_snoc, Fintype.sum_bool]
    by_cases hwa : w ∈ a
    · simp only [hwa, if_true]
      rw [s.refine n w, add_comm]
    · simp [hwa]
  rw [Finset.sum_congr rfl (fun w _ => hw w), ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.univ_inter]

/-! ## 3. Records are the atoms -/

/-- The first `n` answers of an answer sequence. -/
def pre (x : ℕ → Bool) (n : ℕ) : Fin n → Bool := fun i => x i

/-- `x` is a record of `s`: it answers "yes" to every sufficiently sure reading. -/
def IsRecord (s : Source) (x : ℕ → Bool) : Prop :=
  ∃ δ > 0, ∀ n (a : Finset (Fin n → Bool)), 1 < (∑ w ∈ a, s.p n w) + δ → pre x n ∈ a

/-- An answer sequence is a record exactly when its weights stay above a positive bound. -/
theorem isRecord_iff (s : Source) (x : ℕ → Bool) :
    IsRecord s x ↔ ∃ c > 0, ∀ n, c ≤ s.p n (pre x n) := by
  constructor
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun n => ?_⟩
    by_contra hlt
    push Not at hlt
    have hsplit : (∑ w ∈ univ.erase (pre x n), s.p n w) + s.p n (pre x n) = 1 := by
      rw [sum_erase_add _ _ (mem_univ _), s.total n]
    have hfin : (∑ w ∈ univ.erase (pre x n), s.p n w) ≠ ∞ := by
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      rw [← hsplit]; exact le_self_add
    have hmem := h n (univ.erase (pre x n)) (by
      calc (1 : ℝ≥0∞) = (∑ w ∈ univ.erase (pre x n), s.p n w) + s.p n (pre x n) := hsplit.symm
        _ < (∑ w ∈ univ.erase (pre x n), s.p n w) + δ := ENNReal.add_lt_add_left hfin hlt)
    exact (Finset.notMem_erase _ _) hmem
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, fun n a ha => ?_⟩
    by_contra hna
    have hle : (∑ w ∈ a, s.p n w) + s.p n (pre x n) ≤ 1 := by
      rw [add_comm, ← sum_insert hna, ← s.total n]
      exact Finset.sum_le_sum_of_subset (subset_univ _)
    exact absurd (lt_of_lt_of_le ha (le_trans (add_le_add le_rfl (h n)) hle)) (lt_irrefl _)

/-! ## 4. Finite levels have records; the fair coin has none -/

/-- At every level some reading has positive weight. -/
theorem level_has_atom (s : Source) (n : ℕ) : ∃ w, s.p n w ≠ 0 := by
  by_contra h
  push Not at h
  have := s.total n
  rw [sum_eq_zero (fun w _ => h w)] at this
  exact zero_ne_one this

/-- The fair coin has no record: no answer sequence answers all its sure readings. -/
theorem coin_no_record (x : ℕ → Bool) : ¬ IsRecord coin x := by
  rw [isRecord_iff]
  rintro ⟨c, hc, h⟩
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt hc.ne'
  exact absurd (h n) (not_le.mpr hn)

/-! ## 5. A record is an answer that re-reading reproduces -/

/-- The chance that two independent readings agree on the first `n` answers. -/
noncomputable def agree (s : Source) (n : ℕ) : ℝ≥0∞ := ∑ w, s.p n w ^ 2

theorem pre_succ (y : ℕ → Bool) (m : ℕ) : pre y (m + 1) = Fin.snoc (pre y m) (y m) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [pre]
  · simp [pre]

/-- Along one answer sequence, the weights of its prefixes can only decrease. -/
theorem pre_step (s : Source) (y : ℕ → Bool) (m : ℕ) :
    s.p (m + 1) (pre y (m + 1)) ≤ s.p m (pre y m) := by
  rw [pre_succ, s.refine m (pre y m)]
  cases y m
  · exact le_self_add
  · exact le_add_self

theorem pre_mono (s : Source) (y : ℕ → Bool) {n m : ℕ} (h : n ≤ m) :
    s.p m (pre y m) ≤ s.p n (pre y n) := by
  induction m, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact le_trans (pre_step s y m) ih

/-- A finite string, extended by `false`. -/
def extend {n : ℕ} (w : Fin n → Bool) : ℕ → Bool := fun i => if h : i < n then w ⟨i, h⟩ else false

theorem pre_extend {n : ℕ} (w : Fin n → Bool) : pre (extend w) n = w := by
  funext i; simp [pre, extend, i.isLt]

/-- If the chance of agreeing stays above `L`, every level has a reading of weight at least `L`. -/
theorem heavy_of_agree (s : Source) {L : ℝ≥0∞} (n : ℕ) (h : L ≤ agree s n) :
    ∃ w, L ≤ s.p n w := by
  obtain ⟨w₀, -, hmax⟩ := Finset.exists_max_image univ (s.p n) univ_nonempty
  refine ⟨w₀, le_trans h ?_⟩
  calc agree s n = ∑ w, s.p n w * s.p n w := by simp [agree, sq]
    _ ≤ ∑ w, s.p n w * s.p n w₀ := sum_le_sum fun w _ => mul_le_mul' le_rfl (hmax w (mem_univ _))
    _ = s.p n w₀ := by rw [← sum_mul, s.total n, one_mul]

/-- A string with heavy extensions at every deeper level. -/
def Good (s : Source) (L : ℝ≥0∞) {n : ℕ} (w : Fin n → Bool) : Prop :=
  ∀ m, n ≤ m → ∃ y : ℕ → Bool, pre y n = w ∧ L ≤ s.p m (pre y m)

theorem good_root (s : Source) {L : ℝ≥0∞} (h : ∀ n, L ≤ agree s n) :
    Good s L (Fin.elim0 : Fin 0 → Bool) := by
  intro m _
  obtain ⟨w, hw⟩ := heavy_of_agree s m (h m)
  exact ⟨extend w, funext fun i => i.elim0, by rw [pre_extend]; exact hw⟩

theorem good_child (s : Source) {L : ℝ≥0∞} {n : ℕ} {w : Fin n → Bool} (hw : Good s L w) :
    ∃ b, Good s L (Fin.snoc w b : Fin (n + 1) → Bool) := by
  by_contra hno
  push Not at hno
  have bad : ∀ b, ∃ m, n + 1 ≤ m ∧ ∀ y : ℕ → Bool, pre y (n + 1) = Fin.snoc w b →
      s.p m (pre y m) < L := by
    intro b
    have := hno b
    unfold Good at this
    push Not at this
    exact this
  obtain ⟨m₀, hm₀, h₀⟩ := bad false
  obtain ⟨m₁, hm₁, h₁⟩ := bad true
  obtain ⟨y, hyn, hy⟩ := hw (max m₀ m₁) (le_trans (Nat.le_succ n) (le_trans hm₀ (le_max_left _ _)))
  have hyn1 : pre y (n + 1) = Fin.snoc w (y n) := by rw [pre_succ, hyn]
  cases hb : y n
  · rw [hb] at hyn1
    exact absurd (lt_of_le_of_lt (pre_mono s y (le_max_left m₀ m₁)) (h₀ y hyn1)) (not_lt.mpr hy)
  · rw [hb] at hyn1
    exact absurd (lt_of_le_of_lt (pre_mono s y (le_max_right m₀ m₁)) (h₁ y hyn1)) (not_lt.mpr hy)

/-- Good strings of every length, each extending the last. -/
structure GoodStr (s : Source) (L : ℝ≥0∞) (n : ℕ) where
  w : Fin n → Bool
  good : Good s L w

noncomputable def GoodStr.step {s : Source} {L : ℝ≥0∞} {n : ℕ} (g : GoodStr s L n) :
    GoodStr s L (n + 1) :=
  ⟨Fin.snoc g.w (Classical.choose (good_child s g.good)),
    Classical.choose_spec (good_child s g.good)⟩

noncomputable def chain (s : Source) (L : ℝ≥0∞) (h0 : Good s L (Fin.elim0 : Fin 0 → Bool)) :
    (n : ℕ) → GoodStr s L n
  | 0 => ⟨Fin.elim0, h0⟩
  | n + 1 => (chain s L h0 n).step

/-- The branch through the good strings. -/
noncomputable def branch (s : Source) (L : ℝ≥0∞) (h0 : Good s L (Fin.elim0 : Fin 0 → Bool))
    (k : ℕ) : Bool :=
  (chain s L h0 (k + 1)).w (Fin.last k)

theorem chain_coherent (s : Source) (L : ℝ≥0∞) (h0 : Good s L (Fin.elim0 : Fin 0 → Bool)) :
    ∀ n (i : ℕ) (hi : i < n), (chain s L h0 n).w ⟨i, hi⟩ = branch s L h0 i := by
  intro n
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro i hi
    show (Fin.snoc (chain s L h0 n).w _ : Fin (n + 1) → Bool) ⟨i, hi⟩ = branch s L h0 i
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · have : (⟨i, hi⟩ : Fin (n + 1)) = Fin.castSucc ⟨i, hlt⟩ := rfl
      rw [this, Fin.snoc_castSucc, ih i hlt]
    · rfl

theorem pre_branch (s : Source) (L : ℝ≥0∞) (h0 : Good s L (Fin.elim0 : Fin 0 → Bool)) (n : ℕ) :
    pre (branch s L h0) n = (chain s L h0 n).w := by
  funext i
  exact (chain_coherent s L h0 n i.1 i.2).symm

/-- **A source has a record exactly when re-reading reproduces its whole answer with
    positive chance**: two independent readings agree on every level with a chance
    bounded away from zero. -/
theorem record_iff_repeat (s : Source) :
    (∃ x, IsRecord s x) ↔ ∃ L > 0, ∀ n, L ≤ agree s n := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨c, hc, hcx⟩ := (isRecord_iff s x).mp hx
    refine ⟨c ^ 2, ENNReal.pow_pos hc 2, fun n => ?_⟩
    calc c ^ 2 ≤ s.p n (pre x n) ^ 2 := pow_le_pow_left' (hcx n) 2
      _ ≤ agree s n :=
        single_le_sum (f := fun w => s.p n w ^ 2) (fun _ _ => zero_le) (mem_univ _)
  · rintro ⟨L, hL, h⟩
    have h0 := good_root s h
    refine ⟨branch s L h0, (isRecord_iff s _).mpr ⟨L, hL, fun n => ?_⟩⟩
    rw [pre_branch]
    obtain ⟨y, hyn, hy⟩ := (chain s L h0 n).good n le_rfl
    rw [← hyn]; exact hy

end PZFC.Sources
