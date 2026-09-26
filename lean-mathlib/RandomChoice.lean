/-
  Random choice without choice (notes/38).

  Russell's socks with weights.  The symmetry swaps two socks and their names.
  - No sock can be chosen: no member of the pair is fixed by the symmetry.
  - Yet a random sock exists as an object, fixed by the symmetry: each sock is its
    member with weight 1/2, total 1.
  - The weight 1/2 is forced: any object fixed by the symmetry that weighs the two
    socks with total 1 weighs each 1/2.
  The construction is `Symmetric` (mathlib-free) at the weights of `WeightedKind`.
-/

import Symmetric
import WeightedKind

open scoped ENNReal

namespace PZFC.RandomChoice

open PZFC.Values PZFC.Symmetric
open PZFC.Kinds (z2)
open PZFC.WeightedKind (weights)

/-- The names of the two socks, swapped by the symmetry. -/
def sockNames : GLab z2 where
  L := Bool
  lact g b := xor g b
  lact_one b := by cases b <;> rfl
  lact_mul g h b := by cases g <;> cases h <;> cases b <;> rfl

/-- The pair (`none`) and the two socks (`some b`); each sock is a member of the pair
    with weight `w`.  The symmetry swaps the socks and their names. -/
noncomputable def pairSys (w : ℝ≥0∞) : GSys weights z2 sockNames where
  N := Option Bool
  R z x := match z, x with
    | some _, none => w
    | _, _ => 0
  act g x := x.map (xor g)
  act_one x := by
    cases x with
    | none => rfl
    | some b => cases b <;> rfl
  act_mul g h x := by
    cases x with
    | none => rfl
    | some b => cases g <;> cases h <;> cases b <;> rfl
  R_act g z x := by cases z <;> cases x <;> rfl
  lab x := x
  lab_act g x := by cases x <;> rfl

/-- A random sock: the pair, each sock weighing 1/2. -/
noncomputable def randomSock : UG weights z2 sockNames := gdec (pairSys (1 / 2)) none

/-- A sock. -/
noncomputable def sock (b : Bool) : UG weights z2 sockNames := gdec (pairSys (1 / 2)) (some b)

/-- The random sock is fixed by the symmetry: a global object. -/
theorem randomSock_global (g : Bool) : UG.act g randomSock = randomSock := rfl

/-- The symmetry swaps the socks. -/
theorem swap_sock (b : Bool) : UG.act true (sock b) = sock (!b) := by
  cases b <;> rfl

/-- The two socks are different objects: their names differ. -/
theorem sock_ne (b : Bool) : sock (!b) ≠ sock b := by
  intro h
  have := congrArg UG.lab h
  change some (!b) = some b at this
  cases b <;> exact Bool.noConfusion (Option.some.inj this)

/-- Each sock weighs 1/2 in the random sock. -/
theorem sock_weight (b : Bool) : UG.E (sock b) randomSock = 1 / 2 := by
  show ∑' z : {z // gdec (pairSys (1 / 2)) z = sock b}, (pairSys (1 / 2)).R z.1 none = 1 / 2
  rw [tsum_eq_single (⟨some b, rfl⟩ : {z // gdec (pairSys (1 / 2)) z = sock b})]
  · rfl
  · rintro ⟨z, hz⟩ hne
    exfalso
    have hl := congrArg UG.lab hz
    change z = some b at hl
    subst hl
    exact hne rfl

/-- The weights add up to 1: the random sock is a probability. -/
theorem random_total : UG.E (sock true) randomSock + UG.E (sock false) randomSock = 1 := by
  rw [sock_weight, sock_weight]
  exact ENNReal.add_halves 1

/-- Whatever weighs something in the random sock is a sock. -/
theorem member_is_sock (y : UG weights z2 sockNames) (hy : UG.E y randomSock ≠ 0) :
    ∃ b, sock b = y := by
  have h : ¬ ∀ z : {z // gdec (pairSys (1 / 2)) z = y}, (pairSys (1 / 2)).R z.1 none = 0 :=
    fun h => hy (ENNReal.tsum_eq_zero.2 h)
  push Not at h
  obtain ⟨⟨z, hz⟩, hR⟩ := h
  cases z with
  | none => exact absurd rfl hR
  | some b => exact ⟨b, hz⟩

/-- **No sock can be chosen**: nothing that weighs in the random sock is fixed by the
    symmetry. -/
theorem no_choice : ¬ ∃ y, (∀ g, UG.act g y = y) ∧ UG.E y randomSock ≠ 0 := by
  rintro ⟨y, hfix, hy⟩
  obtain ⟨b, rfl⟩ := member_is_sock y hy
  exact sock_ne b ((swap_sock b).symm.trans (hfix true))

/-- **The weight 1/2 is forced by the symmetry**: an object fixed by the symmetry that
    weighs the two socks with total 1 weighs each 1/2. -/
theorem forced_half (r : UG weights z2 sockNames) (hr : ∀ g, UG.act g r = r)
    (h1 : UG.E (sock true) r + UG.E (sock false) r = 1) (b : Bool) :
    UG.E (sock b) r = 1 / 2 := by
  have hsym : UG.E (sock false) r = UG.E (sock true) r := by
    have := UG.E_act true (sock true) r
    rw [hr true] at this
    exact this
  have hw : UG.E (sock true) r = 1 / 2 := by
    rw [hsym] at h1
    rw [ENNReal.eq_div_iff two_ne_zero ENNReal.ofNat_ne_top, two_mul]
    exact h1
  cases b
  · rw [hsym]
    exact hw
  · exact hw

/-- **Random choice without choice.**  Over the symmetry swapping two socks:
    - no sock can be chosen;
    - the random sock is a global object;
    - each sock weighs 1/2 in it, total 1;
    - any global object weighing the two socks with total 1 weighs each 1/2. -/
theorem random_choice_without_choice :
    (¬ ∃ y, (∀ g, UG.act g y = y) ∧ UG.E y randomSock ≠ 0) ∧
    (∀ g, UG.act g randomSock = randomSock) ∧
    (∀ b, UG.E (sock b) randomSock = 1 / 2) ∧
    UG.E (sock true) randomSock + UG.E (sock false) randomSock = 1 ∧
    ∀ r, (∀ g, UG.act g r = r) → UG.E (sock true) r + UG.E (sock false) r = 1 →
      ∀ b, UG.E (sock b) r = 1 / 2 :=
  ⟨no_choice, randomSock_global, sock_weight, random_total, forced_half⟩

end PZFC.RandomChoice
