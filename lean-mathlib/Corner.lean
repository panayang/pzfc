/-
  The 60° corner of the three-chain path synchronisation is exactly solvable (notes/116,
  Proposition 2).

  The differences `(D¹, D²)` move by `(1,0)`, `(-1,1)`, `(0,-1)`, each with probability 1/3.
  The cubic `h(x, y) = x y (x + y)` vanishes on both sides of the corner `x, y > 0`, is positive
  inside, and is an exact harmonic function of the step: the mean of `h` over the three moves is
  `h` itself, at every lattice point.  Hence `h` of the walk, sampled after any number of steps,
  is an exact martingale, and escape probabilities from the corner follow from optional stopping
  with no error term.  The opposite 60° corner uses `h(-x, -y)`.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Logic.Function.Iterate

namespace PZFC.Corner

/-- The harmonic cubic of the 60° corner. -/
def h (x y : ℤ) : ℤ := x * y * (x + y)

/-- Exact harmonicity: the three moves average to the current value. -/
theorem harmonic (x y : ℤ) :
    h (x + 1) y + h (x - 1) (y + 1) + h x (y - 1) = 3 * h x y := by
  unfold h; ring

/-- `h` vanishes on both sides of the corner. -/
theorem zero_on_sides (x y : ℤ) : h x 0 = 0 ∧ h 0 y = 0 := by
  unfold h; constructor <;> ring

/-- `h` is positive inside the corner. -/
theorem pos_inside {x y : ℤ} (hx : 0 < x) (hy : 0 < y) : 0 < h x y := by
  unfold h; positivity

/-- The opposite 60° corner (`x, y < 0`): `h(-x, -y)` is harmonic for the same moves. -/
theorem harmonic_opposite (x y : ℤ) :
    h (-(x + 1)) (-y) + h (-(x - 1)) (-(y + 1)) + h (-x) (-(y - 1)) = 3 * h (-x) (-y) := by
  unfold h; ring

/-- The `k`-step form: if `f` is harmonic for one step then so is its average over any number
of steps.  Stated for the one-step averaging operator `P`. -/
def P (f : ℤ → ℤ → ℤ) (x y : ℤ) : ℤ := f (x + 1) y + f (x - 1) (y + 1) + f x (y - 1)

theorem iterate_harmonic (k : ℕ) (x y : ℤ) :
    (P^[k] h) x y = 3 ^ k * h x y := by
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show (P^[k] h) (x + 1) y + (P^[k] h) (x - 1) (y + 1) + (P^[k] h) x (y - 1) = _
    rw [ih, ih, ih, pow_succ]
    have := harmonic x y
    linear_combination (3 ^ k) * this

end PZFC.Corner
