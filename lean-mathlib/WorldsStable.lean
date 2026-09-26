/-
  Stabilization levels of sentences in the multiverse of worlds (notes/122 §3, 123 §1.4).

  The extension relation of a `Worlds.Multiverse` is a preorder, so the stabilization theory of
  `Stabilize` applies to the truth value of any sentence along extensions.
  * M4 puts every core sentence at level 0: its truth never changes (`core_level_zero`).
  * A sentence that can be forced both ways from every extension is a switch: it can change any
    number of times (`switch_all_levels`), so it has no limit value.
-/
import Worlds
import Stabilize

namespace PZFC.WorldsStable

open PZFC.Worlds PZFC.Stabilize

variable (M : Multiverse)

/-- The worlds of `M`, ordered by extension. -/
def W := M.World

instance : Preorder (W M) where
  le := M.ext
  le_refl := M.ext_refl
  le_trans := fun _ _ _ => M.ext_trans

/-- The truth value of a sentence in a world, as a Boolean. -/
noncomputable def truth (φ : M.Sent) (v : W M) : Bool := by
  classical exact decide (M.sat v φ)

theorem truth_true (φ : M.Sent) (v : W M) : truth M φ v = true ↔ M.sat v φ := by
  classical
  unfold truth
  simp

theorem truth_eq_iff (φ : M.Sent) (u v : W M) :
    truth M φ u = truth M φ v ↔ (M.sat u φ ↔ M.sat v φ) := by
  classical
  unfold truth
  by_cases hu : M.sat u φ <;> by_cases hv : M.sat v φ <;> simp [hu, hv]

/-- **M4 puts core sentences at level 0**: from a world where the parameters exist, the truth
of a core sentence cannot change even once. -/
theorem core_level_zero {φ : M.Sent} (hc : M.core φ) {w : W M} (ha : M.avail φ w) :
    ¬ Alt (truth M φ) 1 w := by
  rintro ⟨v, hwv, hne, _⟩
  exact hne ((truth_eq_iff M φ v w).2 (M.m4 hc hwv ha).symm)

/-- **Switches**: if from every extension of `w` the sentence can be made true and can be made
false, then from every extension it can change any number of times. -/
theorem switch_all_levels {φ : M.Sent} {w : W M}
    (h : ∀ v : W M, w ≤ v → (∃ u : W M, v ≤ u ∧ M.sat u φ) ∧ (∃ u : W M, v ≤ u ∧ ¬ M.sat u φ)) :
    ∀ n (v : W M), w ≤ v → Alt (truth M φ) n v := by
  intro n
  induction n with
  | zero => intro v _; trivial
  | succ n ih =>
      intro v hwv
      obtain ⟨⟨u₁, hvu₁, h₁⟩, ⟨u₂, hvu₂, h₂⟩⟩ := h v hwv
      by_cases hv : M.sat v φ
      · refine ⟨u₂, hvu₂, ?_, ih u₂ (le_trans hwv hvu₂)⟩
        intro heq
        exact h₂ (((truth_eq_iff M φ u₂ v).1 heq).2 hv)
      · refine ⟨u₁, hvu₁, ?_, ih u₁ (le_trans hwv hvu₁)⟩
        intro heq
        exact hv (((truth_eq_iff M φ u₁ v).1 heq).1 h₁)

end PZFC.WorldsStable
