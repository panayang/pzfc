/-
  Computation as stabilization along recording (notes/122).

  A recording system is a preorder `W` of stages ("w ≤ v": v adds records to w).  A question is a
  Boolean-valued `P : W → Bool`.  `Alt P k w` says that from `w` there is a chain of extensions
  along which the answer changes `k` times.

  * A persistent answer (a "button": once true, true in every extension) changes at most once,
    and a Boolean combination of `n` persistent answers changes at most `n` times
    (`alt_le_unpushed`, `no_alt_of_combination`).
  * Under the modal axiom .2 for `P` (what can be made permanently so remains always possible),
    the eventual value is unique (`unique_limit`), and a question that changes at most finitely
    often is determined by its eventual value and the parity of the number of changes still
    possible (`parity_representation`).  The sets "at most j more changes" are persistent.

  This is the Ershov hierarchy (n-c.e. = Boolean combinations of c.e.) for branching, confluent
  recording systems: linear time is not needed, confluence (.2) is.
-/
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace PZFC.Stabilize

variable {W : Type*} [Preorder W]

/-- From `w` there is a chain of extensions along which `P` changes `k` times. -/
def Alt (P : W → Bool) : ℕ → W → Prop
  | 0, _ => True
  | k + 1, w => ∃ v, w ≤ v ∧ P v ≠ P w ∧ Alt P k v

theorem alt_succ_imp (P : W → Bool) : ∀ k w, Alt P (k + 1) w → Alt P k w
  | 0, _, _ => trivial
  | k + 1, _, ⟨v, hwv, hne, h⟩ => ⟨v, hwv, hne, alt_succ_imp P k v h⟩

/-- Changes still possible from a later stage are possible from an earlier one. -/
theorem alt_down (P : W → Bool) : ∀ k {w v : W}, w ≤ v → Alt P k v → Alt P k w
  | 0, _, _, _, _ => trivial
  | k + 1, w, v, hwv, ⟨u, hvu, hne, h⟩ => by
      by_cases hvw : P v = P w
      · exact ⟨u, le_trans hwv hvu, by rw [← hvw]; exact hne, h⟩
      · exact alt_succ_imp P (k + 1) w ⟨v, hwv, hvw, ⟨u, hvu, hne, h⟩⟩

/-- A set of stages is persistent if it is closed under extension. -/
def Persistent (S : Set W) : Prop := ∀ w v, w ≤ v → w ∈ S → v ∈ S

/-- "At most `k - 1` more changes" is persistent: the sets of the difference hierarchy. -/
theorem persistent_bounded (P : W → Bool) (k : ℕ) : Persistent {w | ¬ Alt P k w} :=
  fun _ _ hwv hw hv => hw (alt_down P k hwv hv)

/-! ### Boolean combinations of buttons change boundedly often -/

section Combination

variable {n : ℕ} (U : Fin n → W → Bool)

/-- The number of buttons not yet pushed at `w`. -/
noncomputable def unpushed (w : W) : ℕ :=
  (Finset.univ.filter (fun i => U i w = false)).card

/-- If the answer is determined by `n` persistent answers, every change of the answer pushes a
button, so the number of possible changes is at most the number of unpushed buttons. -/
theorem alt_le_unpushed (P : W → Bool)
    (hU : ∀ i w v, w ≤ v → U i w = true → U i v = true)
    (hdet : ∀ w v, (∀ i, U i w = U i v) → P w = P v) :
    ∀ k w, Alt P k w → k ≤ unpushed U w
  | 0, _, _ => Nat.zero_le _
  | k + 1, w, ⟨v, hwv, hne, h⟩ => by
      have ih := alt_le_unpushed P hU hdet k v h
      -- some button differs between `w` and `v`
      have hdiff : ∃ i, U i w ≠ U i v := by
        by_contra hno
        exact hne (hdet w v (fun i => by by_contra hi; exact hno ⟨i, hi⟩)).symm
      obtain ⟨i, hi⟩ := hdiff
      have hiw : U i w = false := by
        cases h1 : U i w
        · rfl
        · exact absurd (hU i w v hwv h1) (by rw [← h1]; exact fun h2 => hi h2.symm)
      have hiv : U i v = true := by
        cases h2 : U i v
        · exact absurd (hiw.trans h2.symm) hi
        · rfl
      have hsub : Finset.univ.filter (fun j => U j v = false) ⊂
          Finset.univ.filter (fun j => U j w = false) := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨?_, ?_⟩
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          cases h3 : U j w
          · rfl
          · rw [hU j w v hwv h3] at hj; exact absurd hj (by decide)
        · intro heq
          have : i ∈ Finset.univ.filter (fun j => U j w = false) := by simp [hiw]
          rw [← heq] at this
          simp [hiv] at this
      have := Finset.card_lt_card hsub
      unfold unpushed at ih ⊢
      omega

/-- A Boolean combination of `n` buttons changes at most `n` times. -/
theorem no_alt_of_combination (P : W → Bool)
    (hU : ∀ i w v, w ≤ v → U i w = true → U i v = true)
    (hdet : ∀ w v, (∀ i, U i w = U i v) → P w = P v) (w : W) :
    ¬ Alt P (n + 1) w := by
  intro h
  have h1 := alt_le_unpushed U P hU hdet (n + 1) w h
  have h2 : unpushed U w ≤ n := by
    unfold unpushed
    exact (Finset.card_filter_le _ _).trans (by simp)
  omega

end Combination

/-! ### Under .2 the limit is unique and the answer is a parity -/

/-- Necessity and possibility along extensions. -/
def Box (Q : W → Prop) (w : W) : Prop := ∀ v, w ≤ v → Q v
def Dia (Q : W → Prop) (w : W) : Prop := ∃ v, w ≤ v ∧ Q v

/-- .2 for `Q` gives a unique eventual value: `Q` and `¬Q` cannot both be made permanent. -/
theorem unique_limit (Q : W → Prop) (h2 : ∀ w, Dia (Box Q) w → Box (Dia Q) w) (w : W)
    (hyes : Dia (Box Q) w) (hno : Dia (Box fun x => ¬ Q x) w) : False := by
  obtain ⟨v, hwv, hv⟩ := hno
  obtain ⟨u, hvu, hu⟩ := h2 w hyes v hwv
  exact hv u hvu hu

/-- A stage from which the answer never changes again. -/
def Stable (P : W → Bool) (s : W) : Prop := ∀ u, s ≤ u → P u = P s

/-- If at most `k` changes are possible from `w`, some extension of `w` is stable. -/
theorem exists_stable (P : W → Bool) : ∀ k (w : W), ¬ Alt P (k + 1) w → ∃ s, w ≤ s ∧ Stable P s
  | 0, w, h => ⟨w, le_refl w, fun u hwu => by
      by_contra hne
      exact h ⟨u, hwu, hne, trivial⟩⟩
  | k + 1, w, h => by
      by_cases hk : Alt P (k + 1) w
      · obtain ⟨v, hwv, hne, hv⟩ := hk
        have hv' : ¬ Alt P (k + 1) v := fun hv1 => h ⟨v, hwv, hne, hv1⟩
        obtain ⟨s, hvs, hs⟩ := exists_stable P k v hv'
        exact ⟨s, le_trans hwv hvs, hs⟩
      · exact exists_stable P k w hk

/-- Flip a Boolean `k` times. -/
def par (e : Bool) : ℕ → Bool
  | 0 => e
  | k + 1 => !(par e k)

/-- **Stabilization theorem.**  Suppose the answer changes at most `N` times from `w₀`, and .2
holds for "the answer is `b`" for both values `b`.  Then there is an eventual value `e`, and at
every later stage `w` from which exactly `k` more changes are possible, the answer is `e` flipped
`k` times.  (So the answer is a Boolean combination of the persistent sets
`{w | ¬ Alt P j w}`, `j ≤ N`.) -/
theorem parity_representation (P : W → Bool)
    (h2 : ∀ b : Bool, ∀ w, Dia (Box fun x => P x = b) w → Box (Dia fun x => P x = b) w)
    (w₀ : W) (N : ℕ) (hN : ¬ Alt P (N + 1) w₀) :
    ∃ e : Bool, ∀ k w, w₀ ≤ w → Alt P k w → ¬ Alt P (k + 1) w → P w = par e k := by
  obtain ⟨s₀, hs₀, hstab₀⟩ := exists_stable P N w₀ hN
  refine ⟨P s₀, ?_⟩
  -- every stable stage above `w₀` has the eventual value `P s₀`
  have hval : ∀ s, w₀ ≤ s → Stable P s → P s = P s₀ := by
    intro s hs hstab
    have hbox : Dia (Box fun x => P x = P s₀) w₀ := ⟨s₀, hs₀, fun u hu => hstab₀ u hu⟩
    obtain ⟨u, hsu, hu⟩ := h2 (P s₀) w₀ hbox s hs
    rw [← hstab u hsu]; exact hu
  intro k
  induction k with
  | zero =>
      intro w hw _ h1
      have hstab : Stable P w := fun u hwu => by
        by_contra hne
        exact h1 ⟨u, hwu, hne, trivial⟩
      exact hval w hw hstab
  | succ k ih =>
      intro w hw hk hk1
      obtain ⟨v, hwv, hne, hv⟩ := hk
      have hv1 : ¬ Alt P (k + 1) v := fun h => hk1 ⟨v, hwv, hne, h⟩
      have hpv := ih v (le_trans hw hwv) hv hv1
      show P w = !(par (P s₀) k)
      rw [← hpv]
      cases hPw : P w <;> cases hPv : P v <;> simp_all

/-! ### Without .2: finite change is still a Boolean combination of persistent sets -/

/-- The layer representation (no .2 needed).  Let `Y P k` be the upward closure of the stages
where exactly `k` more changes are possible and the answer is `true`.  It is persistent, and at
every stage where exactly `k` more changes are possible, the answer is `true` iff the stage lies
in `Y P k`.  Hence a question with at most `N` changes is a Boolean combination of the `2N + 2`
persistent sets `{w | ¬ Alt P j w}` and `Y P k`; what .2 adds is the uniqueness of the limit and
the tight count `N` (`parity_representation`). -/
def Y (P : W → Bool) (k : ℕ) : Set W :=
  {w | ∃ u, u ≤ w ∧ Alt P k u ∧ ¬ Alt P (k + 1) u ∧ P u = true}

theorem persistent_Y (P : W → Bool) (k : ℕ) : Persistent (Y P k) :=
  fun _ _ hwv ⟨u, huw, h1, h2, h3⟩ => ⟨u, le_trans huw hwv, h1, h2, h3⟩

theorem layer_rep (P : W → Bool) (k : ℕ) (w : W) (hk : Alt P k w) (hk1 : ¬ Alt P (k + 1) w) :
    P w = true ↔ w ∈ Y P k := by
  constructor
  · intro hw
    exact ⟨w, le_refl w, hk, hk1, hw⟩
  · rintro ⟨u, huw, hu, hu1, hPu⟩
    by_contra hPw
    -- the answer changes between `u` and `w`, so `u` has one more possible change
    exact hu1 ⟨w, huw, by rw [hPu]; exact hPw, hk⟩

end PZFC.Stabilize
