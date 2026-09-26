/-
  Probabilistic processes as objects (notes/40).

  A Markov chain is a system with weights: the weight of `z` as a member of `x` is
  the probability of moving from `x` to `z`.  The object of a state is its behaviour
  as a process.

  §1  without observation, every process is one object: if every state moves on with
      total probability 1, all states of all such chains are the same object;
  §2  stopping as the observation: where the outgoing weights may sum to less than 1,
      the missing weight is the probability of stopping.  The probability of stopping
      within k steps is computed by a local algorithm, so it is a property of the
      object, and lumping keeps it;
  §3  the random leader: under the cyclic symmetry of n + 1 nodes, a random node is a
      global object and no node is; every global probability over the nodes gives
      each node 1/(n + 1) — the uniform distribution is forced by the symmetry.
-/

import Local
import Symmetric
import WeightedKind
import Mathlib.Algebra.BigOperators.Fin

open scoped ENNReal

namespace PZFC.Processes

open PZFC.Values PZFC.Local PZFC.WeightedKind PZFC.Symmetric

/-! ## 1. Without observation, every process is one object -/

/-- The total probability with which `x` moves on. -/
noncomputable def outWeight (G : Sys weights) (x : G.N) : ℝ≥0∞ := ∑' z, G.R z x

/-- A chain in which every state moves on with total probability 1. -/
def Stochastic (G : Sys weights) : Prop := ∀ x, outWeight G x = 1

/-- The single state that moves to itself with probability 1. -/
noncomputable def loop1 : Sys weights := ⟨Unit, fun _ _ => 1⟩

theorem stochastic_solves {G : Sys weights} (hG : Stochastic G) :
    Solves G loop1 (fun _ => ()) := by
  intro x b
  show (1 : ℝ≥0∞) = ∑' z : {z : G.N // () = b}, G.R z.1 x
  exact (hG x).symm.trans
    ((Equiv.subtypeUnivEquiv (fun _ => rfl) : {z : G.N // () = b} ≃ G.N).tsum_eq
      (fun z => G.R z x)).symm

/-- **Without observation, every process is one object**: all states of all chains that
    move on with total probability 1 are the same object — the single state looping
    with probability 1. -/
theorem stochastic_same {G H : Sys weights} (hG : Stochastic G) (hH : Stochastic H)
    (x : G.N) (y : H.N) : dec G x = dec H y :=
  (dec_image (stochastic_solves hG) x).trans (dec_image (stochastic_solves hH) y).symm

/-! ## 2. Stopping as the observation -/

/-- The probability of stopping within `k` steps from `x`: stop now with the missing
    weight, or move to `z` and stop within `k - 1` steps from there. -/
noncomputable def stopWithin (G : Sys weights) : Nat → G.N → ℝ≥0∞
  | 0, _ => 0
  | k + 1, x => (1 - ∑' z, G.R z x) + ∑' z, G.R z x * stopWithin G k z

/-- A family of local algorithms: stop now with the missing weight, or move on and apply
    `F` to what the next state holds.  With `F = id` it computes stopping probabilities. -/
noncomputable abbrev momentAlg (F : ℝ≥0∞ → ℝ≥0∞) : Alg weights where
  S := ℝ≥0∞
  init := 0
  step _ obs := (1 - ∑' s, obs s) + ∑' s, obs s * F s

/-- One round of `momentAlg F`, written out over the states. -/
theorem run_moment (F : ℝ≥0∞ → ℝ≥0∞) (G : Sys weights) (k : Nat) (x : G.N) :
    run (momentAlg F) G (k + 1) x =
      (1 - ∑' z, G.R z x) + ∑' z, G.R z x * F (run (momentAlg F) G k z) := by
  have h1 : ∑' s, observe G (run (momentAlg F) G k) x s = ∑' z, G.R z x :=
    ENNReal.tsum_fiberwise (fun z => G.R z x) (run (momentAlg F) G k)
  have h2 : ∑' s, observe G (run (momentAlg F) G k) x s * F s =
      ∑' z, G.R z x * F (run (momentAlg F) G k z) := by
    calc ∑' s, observe G (run (momentAlg F) G k) x s * F s
        = ∑' s, ∑' z : run (momentAlg F) G k ⁻¹' {s},
            G.R z x * F (run (momentAlg F) G k z) := by
          refine tsum_congr (fun s => ?_)
          show (∑' z : {z // run (momentAlg F) G k z = s}, G.R z.1 x) * F s = _
          rw [← ENNReal.tsum_mul_right]
          refine tsum_congr (fun z => ?_)
          rw [(show run (momentAlg F) G k z.1 = s from z.2)]
      _ = ∑' z, G.R z x * F (run (momentAlg F) G k z) :=
          ENNReal.tsum_fiberwise (fun z => G.R z x * F (run (momentAlg F) G k z))
            (run (momentAlg F) G k)
  show (1 - ∑' s, observe G (run (momentAlg F) G k) x s) +
      ∑' s, observe G (run (momentAlg F) G k) x s * F s =
    (1 - ∑' z, G.R z x) + ∑' z, G.R z x * F (run (momentAlg F) G k z)
  rw [h1, h2]

/-- The local algorithm computing the stopping probabilities. -/
noncomputable abbrev stopAlg : Alg weights := momentAlg id

/-- The local algorithm computes the stopping probabilities. -/
theorem run_stop (G : Sys weights) : ∀ k x, run stopAlg G k x = stopWithin G k x
  | 0, _ => rfl
  | k + 1, x => by
    rw [run_moment]
    show (1 - ∑' z, G.R z x) + ∑' z, G.R z x * run stopAlg G k z =
      (1 - ∑' z, G.R z x) + ∑' z, G.R z x * stopWithin G k z
    congr 1
    exact tsum_congr (fun z => by rw [run_stop G k z])

/-- **Stopping probabilities are properties of the object**: states that are the same
    object stop within `k` steps with the same probability. -/
theorem stop_object {G H : Sys weights} {x : G.N} {y : H.N} (h : dec G x = dec H y)
    (k : Nat) : stopWithin G k x = stopWithin H k y := by
  rw [← run_stop, ← run_stop]
  exact run_object stopAlg h k

/-- **Lumping keeps stopping probabilities**: a solution — a lumping of states — does
    not change the probability of stopping within `k` steps. -/
theorem stop_lump {G K : Sys weights} {f : G.N → K.N} (hf : Solves G K f) (k : Nat)
    (x : G.N) : stopWithin K k (f x) = stopWithin G k x := by
  rw [← run_stop, ← run_stop]
  exact run_solves stopAlg hf k x

/-! ## 3. The random leader -/

/-- The cyclic group of order `n + 1`. -/
abbrev cyc (n : Nat) : PZFC.Kinds.Grp where
  G := Fin (n + 1)
  mul := (· + ·)
  one := 0
  inv := fun a => -a
  mul_assoc := add_assoc
  one_mul := zero_add
  mul_one := add_zero
  inv_mul := neg_add_cancel
  mul_inv := add_neg_cancel

/-- The names of the nodes, rotated by the symmetry. -/
abbrev nodeNames (n : Nat) : GLab (cyc n) where
  L := Fin (n + 1)
  lact g i := g + i
  lact_one := zero_add
  lact_mul g h i := add_assoc g h i

/-- The nodes (`some i`) and a random node (`none`); each node weighs `w` in it. -/
noncomputable def ringSys (n : Nat) (w : ℝ≥0∞) : GSys weights (cyc n) (nodeNames n) where
  N := Option (Fin (n + 1))
  R z x := match z, x with
    | some _, none => w
    | _, _ => 0
  act g x := x.map (fun i => g + i)
  act_one x := by
    cases x with
    | none => rfl
    | some i => exact congrArg some (zero_add i)
  act_mul g h x := by
    cases x with
    | none => rfl
    | some i => exact congrArg some (add_assoc g h i)
  R_act g z x := by cases z <;> cases x <;> rfl
  lab x := x
  lab_act g x := by cases x <;> rfl

/-- A random node: each node weighs `1 / (n + 1)`. -/
noncomputable def randomNode (n : Nat) : UG weights (cyc n) (nodeNames n) :=
  gdec (ringSys n (1 / (n + 1))) none

/-- A node. -/
noncomputable def node (n : Nat) (i : Fin (n + 1)) : UG weights (cyc n) (nodeNames n) :=
  gdec (ringSys n (1 / (n + 1))) (some i)

theorem randomNode_global (n : Nat) (g : Fin (n + 1)) : UG.act g (randomNode n) = randomNode n :=
  rfl

theorem rotate_node (n : Nat) (g i : Fin (n + 1)) : UG.act g (node n i) = node n (g + i) := rfl

theorem node_ne {n : Nat} {i j : Fin (n + 1)} (h : i ≠ j) : node n i ≠ node n j := by
  intro e
  have := congrArg UG.lab e
  change some i = some j at this
  exact h (Option.some.inj this)

/-- Each node weighs `1 / (n + 1)` in the random node. -/
theorem node_weight (n : Nat) (i : Fin (n + 1)) :
    UG.E (node n i) (randomNode n) = 1 / (n + 1) := by
  show ∑' z : {z // gdec (ringSys n (1 / (n + 1))) z = node n i},
      (ringSys n (1 / (n + 1))).R z.1 none = 1 / (n + 1)
  rw [tsum_eq_single (⟨some i, rfl⟩ : {z // gdec (ringSys n (1 / (n + 1))) z = node n i})]
  · rfl
  · rintro ⟨z, hz⟩ hne
    exfalso
    have hl := congrArg UG.lab hz
    change z = some i at hl
    subst hl
    exact hne rfl

theorem succ_ne_zero_cast (n : Nat) : ((n : ℝ≥0∞) + 1) ≠ 0 := by simp

theorem succ_ne_top_cast (n : Nat) : ((n : ℝ≥0∞) + 1) ≠ ⊤ := by simp

/-- The weights add up to 1: the random node is a probability. -/
theorem random_total (n : Nat) : ∑ i : Fin (n + 1), UG.E (node n i) (randomNode n) = 1 := by
  simp only [node_weight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  exact ENNReal.mul_div_cancel (succ_ne_zero_cast n) (succ_ne_top_cast n)

/-- Whatever weighs something in the random node is a node. -/
theorem member_is_node (n : Nat) (y : UG weights (cyc n) (nodeNames n))
    (hy : UG.E y (randomNode n) ≠ 0) : ∃ i, node n i = y := by
  have h : ¬ ∀ z : {z // gdec (ringSys n (1 / (n + 1))) z = y},
      (ringSys n (1 / (n + 1))).R z.1 none = 0 :=
    fun h => hy (ENNReal.tsum_eq_zero.2 h)
  push Not at h
  obtain ⟨⟨z, hz⟩, hR⟩ := h
  cases z with
  | none => exact absurd rfl hR
  | some i => exact ⟨i, hz⟩

/-- **No node can be chosen**: with at least two nodes, nothing that weighs in the random
    node is fixed by the symmetry. -/
theorem no_choice (n : Nat) (hn : 1 ≤ n) :
    ¬ ∃ y, (∀ g, UG.act g y = y) ∧ UG.E y (randomNode n) ≠ 0 := by
  rintro ⟨y, hfix, hy⟩
  obtain ⟨i, rfl⟩ := member_is_node n y hy
  have h10 : (1 : Fin (n + 1)) ≠ 0 := by
    rw [Ne, Fin.one_eq_zero_iff]
    omega
  have h1 : (1 : Fin (n + 1)) + i ≠ i := by
    intro h
    apply h10
    have := congrArg (fun a => a - i) h
    simpa using this
  exact node_ne h1 ((rotate_node n 1 i).symm.trans (hfix 1))

/-- **The uniform weight is forced by the symmetry**: a global object weighing the nodes
    with total 1 weighs each `1 / (n + 1)`. -/
theorem forced_uniform (n : Nat) (r : UG weights (cyc n) (nodeNames n))
    (hr : ∀ g, UG.act g r = r) (h1 : ∑ i : Fin (n + 1), UG.E (node n i) r = 1)
    (i : Fin (n + 1)) : UG.E (node n i) r = 1 / (n + 1) := by
  have hsym : ∀ j, UG.E (node n j) r = UG.E (node n 0) r := by
    intro j
    have := UG.E_act j (node n 0) r
    rw [hr j, rotate_node, add_zero] at this
    exact this
  rw [Finset.sum_congr rfl (fun j _ => hsym j), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h1
  push_cast at h1
  rw [hsym i, ENNReal.eq_div_iff (succ_ne_zero_cast n) (succ_ne_top_cast n)]
  exact h1

/-- **The random leader.** Under the cyclic symmetry of `n + 1 ≥ 2` nodes:
    - no node can be chosen;
    - a random node is a global object, each node weighing `1 / (n + 1)`, total 1;
    - any global object weighing the nodes with total 1 is this uniform one. -/
theorem random_leader (n : Nat) (hn : 1 ≤ n) :
    (¬ ∃ y, (∀ g, UG.act g y = y) ∧ UG.E y (randomNode n) ≠ 0) ∧
    (∀ g, UG.act g (randomNode n) = randomNode n) ∧
    (∀ i, UG.E (node n i) (randomNode n) = 1 / (n + 1)) ∧
    ∑ i : Fin (n + 1), UG.E (node n i) (randomNode n) = 1 ∧
    ∀ r, (∀ g, UG.act g r = r) → ∑ i : Fin (n + 1), UG.E (node n i) r = 1 →
      ∀ i, UG.E (node n i) r = 1 / (n + 1) :=
  ⟨no_choice n hn, randomNode_global n, node_weight n, random_total n, forced_uniform n⟩

/-! ## 4. The object remembers when the randomness is resolved -/

/-- Five states: `0` moves to `1` or to `2`, with probability 1/2 each; `1` stops;
    `2` loops forever; `3` moves to `4`; `4` stops with probability 1/2 and otherwise
    moves to `2`. -/
noncomputable abbrev branching : Sys weights where
  N := Fin 5
  R z x :=
    if x = 0 ∧ (z = 1 ∨ z = 2) then 1 / 2
    else if x = 2 ∧ z = 2 then 1
    else if x = 3 ∧ z = 4 then 1
    else if x = 4 ∧ z = 2 then 1 / 2
    else 0

theorem sum5 (f : Fin 5 → ℝ≥0∞) : ∑' z, f z = f 0 + f 1 + f 2 + f 3 + f 4 := by
  rw [tsum_fintype, Fin.sum_univ_five]

theorem stop_2 : ∀ k, stopWithin branching k 2 = 0
  | 0 => rfl
  | k + 1 => by
    simp only [stopWithin, sum5]
    simp [stop_2 k]

theorem stop_1 (k : Nat) : stopWithin branching (k + 1) 1 = 1 := by
  simp only [stopWithin, sum5]
  simp

theorem stop_4 (k : Nat) : stopWithin branching (k + 1) 4 = 1 / 2 := by
  simp only [stopWithin, sum5]
  simp [stop_2 k]

theorem stop_0 (k : Nat) : stopWithin branching (k + 1) 0 = 1 / 2 * stopWithin branching k 1 := by
  simp only [stopWithin, sum5]
  simp [stop_2 k, ENNReal.inv_two_add_inv_two]

theorem stop_3 (k : Nat) : stopWithin branching (k + 1) 3 = stopWithin branching k 4 := by
  simp only [stopWithin, sum5]
  simp

/-- States `0` and `3` stop within every number of steps with the same probability:
    never within one step, with probability 1/2 within two or more. -/
theorem same_law : ∀ k, stopWithin branching k 0 = stopWithin branching k 3
  | 0 => rfl
  | 1 => by
    rw [stop_0, stop_3]
    simp [stopWithin]
  | k + 2 => by
    rw [stop_0, stop_3, stop_1, stop_4]
    simp

/-- A local algorithm that squares what the next state holds. -/
noncomputable abbrev squareAlg : Alg weights := momentAlg (fun s => s * s)

theorem square_one (z : Fin 5) :
    run squareAlg branching 1 z = 1 - ∑' z', branching.R z' z := by
  rw [run_moment]
  simp [run]

theorem square_0 : run squareAlg branching 2 0 = 1 / 2 := by
  rw [run_moment]
  simp only [square_one, sum5]
  simp [ENNReal.inv_two_add_inv_two]

theorem square_3 : run squareAlg branching 2 3 = 1 / 2 * (1 / 2) := by
  rw [run_moment]
  simp only [square_one, sum5]
  simp [ENNReal.inv_two_add_inv_two, ENNReal.one_sub_inv_two]

/-- **Same law of stopping, different objects.**  States `0` and `3` stop within every
    number of steps with the same probability, yet they are different objects: `0`
    has decided its fate after one step, `3` only after two, and a local algorithm
    that squares the next state's stopping probability tells them apart. -/
theorem law_not_object :
    (∀ k, stopWithin branching k 0 = stopWithin branching k 3) ∧
      dec branching 0 ≠ dec branching 3 := by
  refine ⟨same_law, fun h => ?_⟩
  have := run_object squareAlg h 2
  rw [square_0, square_3] at this
  have h2 : (1 / 2 : ℝ≥0∞) ≠ 0 := by simp
  have h2' : (1 / 2 : ℝ≥0∞) ≠ ⊤ := by simp
  have : (1 : ℝ≥0∞) = 1 / 2 := by
    have e := congrArg (fun a => a / (1 / 2)) this
    simp only [ENNReal.div_self h2 h2'] at e
    rwa [ENNReal.mul_div_cancel_right h2 h2'] at e
  have e := congrArg (·⁻¹) this
  simp at e

end PZFC.Processes
