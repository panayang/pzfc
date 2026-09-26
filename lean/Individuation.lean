/-
  Individuation, and one theorem for all circumstances (notes/49).  Mathlib-free.

  §1  three coins, read twice (weights out of 8): kept (tossed once, reading
      shows it), fresh (every reading tosses anew), pushed (reading pushes the
      coin towards true).  Randomness, repeatability and disturbance in law come
      apart: kept is random and repeatable; fresh is random, not repeatable, and
      undisturbed in law; pushed is disturbed in law
  §2  individuating the question by its circumstance (who asks, after what
      history) turns every behavior into one with a record model: the classical
      way of making every answer a record
  §3  one theorem for all circumstances: two objects have the same facts through
      their views exactly when they have the same views; for askers: whose view
      it is, is not a fact
-/
import Circumstances

namespace PZFC.Indiv

open PZFC.Circ

/-! ## 1. Three coins, read twice -/

/-- A two-reading experiment, with weights out of 8: the pairs of answers when reading
    twice, and the answer when first waiting and then reading. -/
structure TwoReads where
  rr : Bool → Bool → Nat
  wr : Bool → Nat

/-- Kept: the coin is tossed once; reading shows it. -/
def kept : TwoReads := ⟨fun a b => if a = b then 4 else 0, fun _ => 4⟩

/-- Fresh: every reading tosses the coin anew. -/
def fresh : TwoReads := ⟨fun _ _ => 2, fun _ => 4⟩

/-- Pushed: reading pushes the coin towards `true`. -/
def pushed : TwoReads := ⟨fun _ b => if b then 3 else 1, fun _ => 4⟩

/-- Repeatable: two readings never disagree. -/
def Repeatable2 (e : TwoReads) : Prop := ∀ a b, a ≠ b → e.rr a b = 0

/-- Undisturbed in law: the second reading has the same law whether the first
    reading was made or not. -/
def UndisturbedLaw (e : TwoReads) : Prop := ∀ b, e.rr true b + e.rr false b = e.wr b

/-- Random: each answer of the first reading has positive weight, none has all of it. -/
def Random2 (e : TwoReads) : Prop :=
  ∀ a, 0 < e.rr a true + e.rr a false ∧ e.rr a true + e.rr a false < 8

theorem kept_repeatable : Repeatable2 kept := by
  intro a b h; cases a <;> cases b <;> simp_all [kept]

theorem kept_undisturbed : UndisturbedLaw kept := by
  intro b; cases b <;> rfl

theorem kept_random : Random2 kept := by
  intro a; cases a <;> decide

theorem fresh_not_repeatable : ¬ Repeatable2 fresh := by
  intro h; exact absurd (h true false (by decide)) (by decide)

theorem fresh_undisturbed : UndisturbedLaw fresh := by
  intro b; cases b <;> rfl

theorem fresh_random : Random2 fresh := by
  intro a; cases a <;> decide

theorem pushed_disturbed : ¬ UndisturbedLaw pushed := by
  intro h; exact absurd (h true) (by decide)

theorem pushed_random : Random2 pushed := by
  intro a; cases a <;> decide

/-! ## 2. Individuation: the classical way to make every answer a record -/

/-- Individuate the question by its whole circumstance: after what history, who asks. -/
def individuate {K Q A : Type} (b : Beh K Q A) : Beh Unit (List (K × Q) × K × Q) A :=
  fun _ _ c => b c.1 c.2.1 c.2.2

/-- **Every behavior, individuated, has a record model**: once the circumstance is part of
    the question, every answer is read off one table. -/
theorem individuate_record {K Q A : Type} (b : Beh K Q A) : HasRecordModel (individuate b) :=
  ⟨fun c => b c.1 c.2.1 c.2.2, fun _ _ _ => rfl⟩

/-- Without individuation, the same table exists exactly when the behavior is public and
    undisturbed (`Circ.record_iff`); individuation is needed exactly when it is not. -/
theorem individuation_needed {K Q A : Type} (k₀ : K) (b : Beh K Q A) :
    ¬ HasRecordModel b ↔ ¬ (Public b ∧ Undisturbed b) :=
  not_congr (record_iff k₀ b)

/-! ## 3. One theorem for all circumstances -/

/-- A fact through views: a property of what the object does in every circumstance. -/
def ViewFact {B C V : Type} (view : B → C → V) (P : V → Prop) (b : B) : Prop := ∀ c, P (view b c)

/-- **Same facts through views, exactly when the same views.** -/
theorem sameViewFacts_iff {B C V : Type} (view : B → C → V) (b b' : B) :
    (∀ P, ViewFact view P b ↔ ViewFact view P b') ↔
      ∀ v, (∃ c, view b c = v) ↔ (∃ c, view b' c = v) := by
  constructor
  · intro hs v
    constructor
    · rintro ⟨c, rfl⟩
      exact ((hs (fun v => ∃ c, view b' c = v)).mpr (fun c' => ⟨c', rfl⟩)) c
    · rintro ⟨c, rfl⟩
      exact ((hs (fun v => ∃ c, view b c = v)).mp (fun c' => ⟨c', rfl⟩)) c
  · intro hv P
    constructor
    · intro hP c
      obtain ⟨c₀, e⟩ := (hv (view b' c)).mpr ⟨c, rfl⟩
      rw [← e]; exact hP c₀
    · intro hP c
      obtain ⟨c₀, e⟩ := (hv (view b c)).mp ⟨c, rfl⟩
      rw [← e]; exact hP c₀

/-- The history instance: invariant facts are facts through residuals (`Circ.sameFacts_iff`). -/
theorem invFact_is_viewFact {K Q A : Type} (P : Beh K Q A → Prop) (b : Beh K Q A) :
    InvFact P b ↔ ViewFact residual P b := Iff.rfl

/-- What asker `k` sees. -/
def askerView {K Q A : Type} (b : Beh K Q A) (k : K) : List (K × Q) → Q → A :=
  fun h q => b h k q

/-- The two askers' names, swapped. -/
def swapB : Beh Bool Unit Bool := fun _ k _ => !k

/-- **Whose view it is, is not a fact**: with names and with names swapped, the askers see
    the same two views, and the behaviors differ. -/
theorem name_swap_same_views :
    (∀ P, ViewFact askerView P nameB ↔ ViewFact askerView P swapB) ∧ nameB ≠ swapB := by
  refine ⟨(sameViewFacts_iff askerView nameB swapB).mpr fun v => ?_, fun e => ?_⟩
  · constructor
    · rintro ⟨k, rfl⟩
      refine ⟨!k, ?_⟩
      funext h q; cases k <;> rfl
    · rintro ⟨k, rfl⟩
      refine ⟨!k, ?_⟩
      funext h q; cases k <;> rfl
  · exact absurd (congrFun (congrFun (congrFun e []) true) ()) (by decide)

end PZFC.Indiv
