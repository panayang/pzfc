/-
  What a node can observe, and breaking symmetry with coins (notes/39).

  §1  sets versus counts: two nodes — one holding a member once, the other holding
      the same member twice — are one object for sharp answers, so every algorithm
      that observes only which states occur keeps them alike; an algorithm that
      observes weights tells them apart in one round;
  §2  coins: among the ways n anonymous nodes can each flip a coin, exactly 2 keep
      them all alike and exactly n single out one node — so a randomized algorithm
      breaks the symmetry that no deterministic one can (`Local.no_leader`), with
      positive probability in every round.
-/

import Local
import WeightedKind

open scoped ENNReal

namespace PZFC.Observe

open PZFC.Values PZFC.Local PZFC.WeightedKind

/-! ## 1. Sets versus counts -/

/-- **Observing sets, `a1` and `a2` are never told apart**: in the sharp shadow of
    `mult` they are one object. -/
theorem sets_cannot_count (A : Alg sharp) (k : Nat) :
    run A (mult.map supp) k .a1 = run A (mult.map supp) k .a2 :=
  run_object A (G := mult.map supp) (H := mult.map supp) (x := .a1) (y := .a2)
    shadow_forgets.2 k

/-- A counting algorithm: after one round, each node holds the total weight of its
    members. -/
noncomputable abbrev count : Alg weights := ⟨ℝ≥0∞, 0, fun _ obs => obs 0⟩

theorem count_a1 : run count mult 1 .a1 = 1 := by
  show ∑' z : {z : Three // (0 : ℝ≥0∞) = 0}, mult.R z.1 .a1 = 1
  rw [tsum_eq_single (⟨.e, rfl⟩ : {z : Three // (0 : ℝ≥0∞) = 0})]
  · rfl
  · rintro ⟨z, hz⟩ hne
    cases z with
    | e => exact absurd rfl hne
    | a1 => rfl
    | a2 => rfl

theorem count_a2 : run count mult 1 .a2 = 2 := by
  show ∑' z : {z : Three // (0 : ℝ≥0∞) = 0}, mult.R z.1 .a2 = 2
  rw [tsum_eq_single (⟨.e, rfl⟩ : {z : Three // (0 : ℝ≥0∞) = 0})]
  · rfl
  · rintro ⟨z, hz⟩ hne
    cases z with
    | e => exact absurd rfl hne
    | a1 => rfl
    | a2 => rfl

/-- **Observing weights, counting tells them apart.** -/
theorem weights_can_count : run count mult 1 .a1 ≠ run count mult 1 .a2 := by
  rw [count_a1, count_a2]
  exact ENNReal.one_lt_two.ne

/-! ## 2. Breaking symmetry with coins -/

/-- Of the `2 ^ n` ways `n` nodes can each flip a coin, exactly 2 keep them alike. -/
theorem alike_count (n : Nat) (hn : 0 < n) :
    Fintype.card {f : Fin n → Bool // ∀ i j, f i = f j} = 2 := by
  have e : {f : Fin n → Bool // ∀ i j, f i = f j} ≃ Bool :=
    { toFun := fun f => f.1 ⟨0, hn⟩
      invFun := fun b => ⟨fun _ => b, fun _ _ => rfl⟩
      left_inv := fun f => Subtype.ext (funext fun i => f.2 ⟨0, hn⟩ i)
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_bool]

open Classical in
/-- Of the `2 ^ n` ways, exactly `n` single out one node — the one whose coin shows
    heads. -/
theorem single_count (n : Nat) :
    Fintype.card {f : Fin n → Bool // ∃! i, f i = true} = n := by
  let g : Fin n → {f : Fin n → Bool // ∃! i, f i = true} :=
    fun i => ⟨fun j => decide (j = i), ⟨i, by simp, fun j h => by simpa using h⟩⟩
  have hinj : Function.Injective g := by
    intro i i' h
    have := congrArg (fun f => f.1 i) h
    simpa [g] using this
  have hsurj : Function.Surjective g := by
    rintro ⟨f, i, hi, huniq⟩
    refine ⟨i, Subtype.ext (funext fun j => ?_)⟩
    show decide (j = i) = f j
    by_cases hj : j = i
    · subst hj
      simp [hi]
    · simp only [hj, decide_false]
      cases hfj : f j with
      | false => rfl
      | true => exact absurd (huniq j hfj) hj
  rw [← Fintype.card_of_bijective ⟨hinj, hsurj⟩, Fintype.card_fin]

/-- With at least two nodes, the coins leave them alike in fewer than all cases. -/
theorem alike_rare (n : Nat) (hn : 2 ≤ n) : 2 < 2 ^ n :=
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

open Classical in
/-- **Coins break the symmetry that no deterministic algorithm can.** For `n ≥ 2`
    anonymous nodes: of the `2 ^ n` equally likely coin flips, only 2 keep all nodes
    alike, and `n` single out exactly one node. -/
theorem coins_break_symmetry (n : Nat) (hn : 2 ≤ n) :
    Fintype.card (Fin n → Bool) = 2 ^ n ∧
    Fintype.card {f : Fin n → Bool // ∀ i j, f i = f j} = 2 ∧ 2 < 2 ^ n ∧
    Fintype.card {f : Fin n → Bool // ∃! i, f i = true} = n := by
  refine ⟨by simp, alike_count n (by omega), alike_rare n hn, single_count n⟩

end PZFC.Observe
