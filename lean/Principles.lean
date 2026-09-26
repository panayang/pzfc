/-
  Derivations from the principles of notes/11.  Mathlib-free.

  P1  discernibility is relative to the admissible questions
  P2  counting can exceed discerning
  P3  every single act of asking involves finite information
  P4  questions can themselves be asked about        (see Invariants.lean)
-/

namespace PZFC.Principles

/-! ## P3 — finitude -/

/-- An infinite record of yes/no answers. -/
abbrev Record := Nat → Bool

/-- `α` and `β` agree on the first `N` answers. -/
def Agree (N : Nat) (α β : Record) : Prop := ∀ n, n < N → α n = β n

/-- A test is finitely determined if its verdict on any record is already
    fixed by some finite prefix of that record. -/
def FinitelyDetermined (f : Record → Bool) : Prop :=
  ∀ α, ∃ N, ∀ β, Agree N α β → f β = f α

/-- No finitely determined test decides "every answer is no".  One `true`
    refutes the universal claim; no finite amount of `false` verifies it. -/
theorem no_finite_zero_test :
    ¬ ∃ f : Record → Bool, FinitelyDetermined f ∧
        ∀ α, f α = true ↔ ∀ n, α n = false := by
  rintro ⟨f, hfin, hspec⟩
  let zero : Record := fun _ => false
  have hz : f zero = true := (hspec zero).mpr (fun _ => rfl)
  obtain ⟨N, hN⟩ := hfin zero
  let β : Record := fun n => if n < N then false else true
  have hagree : Agree N zero β := by
    intro n hn
    show false = (if n < N then false else true)
    rw [if_pos hn]
  have hβ : f β = true := (hN β hagree).trans hz
  have hall : β N = false := (hspec β).mp hβ N
  have hN' : β N = true := by
    show (if N < N then false else true) = true
    rw [if_neg (Nat.lt_irrefl N)]
  rw [hN'] at hall
  exact absurd hall (by decide)

/-- Nor can a finite act decide whether two records are equal. -/
theorem no_finite_equality_test :
    ¬ ∃ E : Record → Record → Bool,
        (∀ γ, FinitelyDetermined (fun α => E α γ)) ∧
        ∀ α β, E α β = true ↔ ∀ n, α n = β n := by
  rintro ⟨E, hfin, hspec⟩
  apply no_finite_zero_test
  exact ⟨fun α => E α (fun _ => false), hfin _, fun α => hspec α (fun _ => false)⟩

/-- Apartness, by contrast, is finitely witnessed: once two records are seen
    to differ at `n`, every pair agreeing with them through `n` still differs.
    Distinctness is primary; equality is derived. -/
theorem apartness_is_open (α β : Record) (n : Nat) (h : α n ≠ β n) :
    ∀ α' β', Agree (n + 1) α α' → Agree (n + 1) β β' → α' n ≠ β' n := by
  intro α' β' ha hb heq
  apply h
  rw [ha n (Nat.lt_succ_self n), hb n (Nat.lt_succ_self n)]
  exact heq

/-! ## Classical logic as the layer of irrefutability -/

/-- Every instance of excluded middle is irrefutable.  Classical truth sits on
    top of verification as "cannot be refuted". -/
theorem lem_irrefutable (p : Prop) : ¬¬(p ∨ ¬p) :=
  fun h => h (Or.inr (fun hp => h (Or.inl hp)))

/-- The irrefutability layer is stable. -/
theorem triple_neg (p : Prop) : ¬¬¬p → ¬p :=
  fun h hp => h (fun hn => hn hp)

/-- The zero test, which no finite act decides, is nonetheless classically
    true in the sense that having an answer is irrefutable. -/
theorem zero_test_irrefutable (α : Record) :
    ¬¬((∀ n, α n = false) ∨ ¬(∀ n, α n = false)) :=
  lem_irrefutable _

/-! ## P1 + P2 — the gap between counting and discerning -/

/-- Indifference: if no admissible question can tell any point from any other
    (a transitive family of undetectable transformations), every weight those
    questions can define is constant. -/
theorem indifference {G X W : Type} (act : G → X → X)
    (transitive : ∀ x y, ∃ g, act g x = y)
    (w : X → W) (invariant : ∀ g x, w (act g x) = w x) :
    ∀ x y, w x = w y := by
  intro x y
  obtain ⟨g, hg⟩ := transitive x y
  rw [← hg, invariant]

/-- Nothing can be singled out: an admissible selection would be a point fixed
    by every undetectable transformation, and there is none. -/
theorem no_selection {G X : Type} (act : G → X → X)
    (moves : ∀ x, ∃ g, act g x ≠ x) :
    ¬ ∃ c : X, ∀ g, act g c = c := by
  rintro ⟨c, hc⟩
  obtain ⟨g, hg⟩ := moves c
  exact hg (hc g)

/-- The gap.  `transitive` says there is one discernibility class; `moves`
    says it has more than one member.  Under exactly these two hypotheses the
    weights are forced to be uniform *and* nothing can be selected: intrinsic
    probability and the failure of choice are one symmetry, read twice. -/
theorem gap {G X W : Type} (act : G → X → X)
    (transitive : ∀ x y, ∃ g, act g x = y)
    (moves : ∀ x, ∃ g, act g x ≠ x) (w : X → W)
    (invariant : ∀ g x, w (act g x) = w x) :
    (∀ x y, w x = w y) ∧ ¬ ∃ c : X, ∀ g, act g c = c :=
  ⟨indifference act transitive w invariant, no_selection act moves⟩

/-- Gap closed: when every transformation fixes every point, invariance puts no
    constraint on any weight — probability must be supplied from outside, as
    in Kolmogorov's `(Ω, F, P)` over a universe with choice. -/
theorem gap_closed {G X W : Type} (act : G → X → X)
    (trivial_action : ∀ g x, act g x = x) (w : X → W) :
    ∀ g x, w (act g x) = w x := by
  intro g x
  rw [trivial_action]

end PZFC.Principles
