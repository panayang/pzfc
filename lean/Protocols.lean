/-
  Time as the order of asking (notes/62).  Mathlib-free.

  A history is the sequence of questions asked so far.  Classical probability
  treats information as a single line.  Here the order of asking is part of the
  data, and we ask when it matters.

  §1  two questions commute in the future when asking them in either order leaves
      the behavior the same afterwards
  §2  order-free futures: what the behavior can still do depends only on which
      questions were asked, not in which order, exactly when every two questions
      commute in the future.  Time is then the order of multisets of questions
      (a partial order), not a line
  §3  the two kinds of order-dependence come apart: in the marking memory the future
      does not depend on the order but the recorded answers do; in the memory
      whose reading updates it, the future itself depends on the order
  §4  a mixture of records, each read afresh, is order-free: the weight of a history
      depends only on which (question, answer) pairs occur, not their order.  So a
      behavior whose record of answers depends on the order is not a hidden record
      read by fresh samples
  §5  the Pólya urn (weights out of 6 for two draws): drawing changes the urn, yet the
      history weights are order-free and the second draw has the same law as a
      draw after waiting — its dependence on the past is information, not disturbance
  §6  partial commutation (notes/63): if the askings declared independent commute in
      the future, the future is the same for any two histories that differ by swapping
      adjacent independent askings (traces); time is then a partial order of events
  §7  the order spectrum: what the behavior can become after the same askings in
      different orders; it lies inside the residuals, so hiding the order-dependence
      needs at least as many hidden states as the spectrum has members
-/
import Circumstances

namespace PZFC.Proto

open PZFC.Circ

variable {K Q A : Type}

/-! ## 1. Commuting in the future -/

/-- Asking `e` then `e'`, or `e'` then `e`, leaves the same behavior afterwards. -/
def FutureCommute (b : Beh K Q A) (e e' : K × Q) : Prop :=
  ∀ h, residual b (h ++ [e, e']) = residual b (h ++ [e', e])

/-- Every two askings commute in the future. -/
def AllFutureCommute (b : Beh K Q A) : Prop := ∀ e e', FutureCommute b e e'

theorem allFutureCommute_residual (b : Beh K Q A) (hb : AllFutureCommute b)
    (h₀ : List (K × Q)) : AllFutureCommute (residual b h₀) := by
  intro e e' h
  rw [residual_residual, residual_residual, ← List.append_assoc, ← List.append_assoc]
  exact hb e e' (h₀ ++ h)

/-! ## 2. Order-free futures -/

/-- **If every two askings commute in the future, the future depends only on which
    questions were asked, not on the order.** -/
theorem perm_residual (b : Beh K Q A) (hb : AllFutureCommute b) {l₁ l₂ : List (K × Q)}
    (hp : l₁.Perm l₂) : residual b l₁ = residual b l₂ := by
  induction hp generalizing b with
  | nil => rfl
  | cons x _ ih =>
    show residual b ([x] ++ _) = residual b ([x] ++ _)
    rw [← residual_residual, ← residual_residual]
    exact ih (residual b [x]) (allFutureCommute_residual b hb [x])
  | swap x y l =>
    show residual b ([y, x] ++ l) = residual b ([x, y] ++ l)
    rw [← residual_residual, ← residual_residual]
    have := hb y x []
    simp only [List.nil_append] at this
    rw [this]
  | trans _ _ ih₁ ih₂ => exact (ih₁ b hb).trans (ih₂ b hb)

/-- **Conversely**, if the future never depends on the order, every two askings commute. -/
theorem allFutureCommute_of_perm (b : Beh K Q A)
    (hp : ∀ l₁ l₂ : List (K × Q), l₁.Perm l₂ → residual b l₁ = residual b l₂) :
    AllFutureCommute b := by
  intro e e' h
  exact hp _ _ (List.Perm.append_left h (List.Perm.swap e' e []))

/-- The two together: order-free futures exactly when askings commute in the future. -/
theorem orderFree_iff (b : Beh K Q A) :
    (∀ l₁ l₂ : List (K × Q), l₁.Perm l₂ → residual b l₁ = residual b l₂) ↔
      AllFutureCommute b :=
  ⟨allFutureCommute_of_perm b, fun hb _ _ hp => perm_residual b hb hp⟩

/-- An undisturbed behavior commutes in the future. -/
theorem undisturbed_futureCommute (b : Beh K Q A) (hu : Undisturbed b) :
    AllFutureCommute b := by
  intro e e' h
  rw [(undisturbed_iff_one_residual b).mp hu, (undisturbed_iff_one_residual b).mp hu]

/-! ## 3. The two kinds of order-dependence -/

/-- In the marking memory, the future does not depend on the order of marking and
    checking: either way it ends marked. -/
theorem mark_future_commutes :
    residual markB [((), true), ((), false)] = residual markB [((), false), ((), true)] := by
  rw [residual_markB, residual_markB]; simp

/-- But the recorded answers do depend on the order: checking before marking records
    "not marked", checking after records "marked". -/
theorem mark_record_depends :
    markB [] () true ≠ markB [((), false)] () true := by decide

/-- In the memory whose reading updates it, the future itself depends on the order:
    after storing 0 and 1, reading 0 then storing 2 keeps 0; storing 2 then reading 0
    does not. -/
theorem lru_future_depends :
    residual lruB [st 0, st 1, rd 0, st 2] ≠ residual lruB [st 0, st 1, st 2, rd 0] := by
  intro e
  have h1 := congrFun (congrFun (congrFun e []) ()) (true, 0)
  simp only [residual, List.append_nil] at h1
  have hp := lru_read_protects []
  have hn : lruB ([st 0, st 1, st 2] ++ [rd 0]) () (true, 0) = false := by decide
  simp only [List.nil_append] at hp
  simp only [List.cons_append, List.nil_append] at hn
  rw [hp] at h1
  rw [← h1] at hn
  exact absurd hn (by decide)

/-! ## 4. A mixture of records, read afresh, is order-free -/

/-- A mixture of records: a list of records (repetitions give weights); the weight of a
    history is the number of records consistent with every answer in it. -/
def mixWeight {R : Type} [DecidableEq A] (rs : List R) (rec : R → Q → A)
    (hist : List (Q × A)) : Nat :=
  (rs.filter (fun r => hist.all (fun p => decide (rec r p.1 = p.2)))).length

theorem all_perm {α : Type} (f : α → Bool) {l₁ l₂ : List α} (hp : l₁.Perm l₂) :
    l₁.all f = l₂.all f := by
  cases h1 : l₁.all f <;> cases h2 : l₂.all f <;> try rfl
  · rw [List.all_eq_false] at h1
    rw [List.all_eq_true] at h2
    obtain ⟨x, hx, hfx⟩ := h1
    exact absurd (h2 x (hp.mem_iff.mp hx)) (by simp [hfx])
  · rw [List.all_eq_true] at h1
    rw [List.all_eq_false] at h2
    obtain ⟨x, hx, hfx⟩ := h2
    exact absurd (h1 x (hp.mem_iff.mpr hx)) (by simp [hfx])

/-- **A mixture of records read afresh is order-free.** -/
theorem mixWeight_perm {R : Type} [DecidableEq A] (rs : List R) (rec : R → Q → A)
    {h₁ h₂ : List (Q × A)} (hp : h₁.Perm h₂) : mixWeight rs rec h₁ = mixWeight rs rec h₂ := by
  unfold mixWeight
  congr 1
  apply List.filter_congr
  intro r _
  exact all_perm _ hp

/-! ## 5. The Pólya urn: dependence on the past that is information -/

/-- Two draws from an urn that starts with one red and one black ball, each drawn ball
    returned with another of its colour: weights out of 6 (`true` = red). -/
def polya2 : Bool → Bool → Nat
  | true, true => 2
  | true, false => 1
  | false, true => 1
  | false, false => 2

/-- The order of the colours does not matter. -/
theorem polya_order_free : polya2 true false = polya2 false true := rfl

/-- Drawing changes the urn: after a red, a second red is twice as likely as a black. -/
theorem polya_changes : polya2 true true = 2 * polya2 true false := rfl

/-- Yet averaged over the first draw, the second draw is red with weight 3 of 6, as it
    would be after waiting: the dependence on the past is information, not disturbance. -/
theorem polya_undisturbed_in_law :
    polya2 true true + polya2 false true = 3 ∧ polya2 true false + polya2 false false = 3 := by
  decide

/-! ## 6. Partial commutation: traces -/

/-- One step of trace equivalence: swap two adjacent askings declared independent. -/
def TraceStep (I : K × Q → K × Q → Prop) (l₁ l₂ : List (K × Q)) : Prop :=
  ∃ h t e e', I e e' ∧ l₁ = h ++ e :: e' :: t ∧ l₂ = h ++ e' :: e :: t

/-- Trace equivalence: the reflexive-transitive closure of such swaps. -/
inductive TraceEq (I : K × Q → K × Q → Prop) : List (K × Q) → List (K × Q) → Prop
  | refl (l) : TraceEq I l l
  | step {l₁ l₂ l₃} : TraceStep I l₁ l₂ → TraceEq I l₂ l₃ → TraceEq I l₁ l₃

/-- **If the askings declared independent commute in the future, histories in the same trace
    leave the same future.** -/
theorem trace_residual (b : Beh K Q A) (I : K × Q → K × Q → Prop)
    (hI : ∀ e e', I e e' → FutureCommute b e e') {l₁ l₂ : List (K × Q)}
    (ht : TraceEq I l₁ l₂) : residual b l₁ = residual b l₂ := by
  induction ht with
  | refl => rfl
  | step hs _ ih =>
    obtain ⟨h, t, e, e', hie, rfl, rfl⟩ := hs
    rw [← ih]
    rw [show h ++ e :: e' :: t = (h ++ [e, e']) ++ t by simp,
      show h ++ e' :: e :: t = (h ++ [e', e]) ++ t by simp,
      ← residual_residual b (h ++ [e, e']) t, ← residual_residual b (h ++ [e', e]) t,
      hI e e' hie h]

/-! ## 7. The order spectrum -/

/-- What the behavior can become after the history `h` followed by the askings `l` in some
    order. -/
def InSpectrum (b : Beh K Q A) (h l : List (K × Q)) (r : Beh K Q A) : Prop :=
  ∃ l', l'.Perm l ∧ residual b (h ++ l') = r

/-- The spectrum lies inside the residuals: every order leads to something the behavior can
    become.  So hiding the order-dependence needs at least as many hidden states as the
    spectrum has members (`Circ.residual_realized`). -/
theorem spectrum_residual (b : Beh K Q A) (h l : List (K × Q)) (r : Beh K Q A)
    (hr : InSpectrum b h l r) : IsResidual b r := by
  obtain ⟨l', -, rfl⟩ := hr
  exact ⟨h ++ l', rfl⟩

/-- **The spectrum has one member exactly when the order does not matter**: under future
    commutation, every order leads to the same behavior. -/
theorem spectrum_single (b : Beh K Q A) (hb : AllFutureCommute b) (h l : List (K × Q))
    (r r' : Beh K Q A) (hr : InSpectrum b h l r) (hr' : InSpectrum b h l r') : r = r' := by
  obtain ⟨l₁, hp₁, rfl⟩ := hr
  obtain ⟨l₂, hp₂, rfl⟩ := hr'
  exact perm_residual b hb (List.Perm.append_left h (hp₁.trans hp₂.symm))

/-- The memory whose reading updates it has two members in its spectrum for reading 0 and
    storing 2, after storing 0 and 1. -/
theorem lru_spectrum_two :
    InSpectrum lruB [st 0, st 1] [rd 0, st 2] (residual lruB [st 0, st 1, rd 0, st 2]) ∧
    InSpectrum lruB [st 0, st 1] [rd 0, st 2] (residual lruB [st 0, st 1, st 2, rd 0]) ∧
    residual lruB [st 0, st 1, rd 0, st 2] ≠ residual lruB [st 0, st 1, st 2, rd 0] :=
  ⟨⟨[rd 0, st 2], List.Perm.refl _, rfl⟩,
   ⟨[st 2, rd 0], List.Perm.swap _ _ _, rfl⟩,
   lru_future_depends⟩

end PZFC.Proto
