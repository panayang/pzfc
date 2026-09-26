/-
  The order spectrum, quantitatively (notes/66).  Mathlib-free.

  The spectrum of a list of askings `l` after a history `h` is the set of behaviors reached by
  asking `l` in some order (`Proto.InSpectrum`).

  §1  when askings of different classes commute in the future, the future depends on the order
      only through the order within each class.  Exactly: the spectrum is the image of the
      tuples of within-class orders; every such tuple is realized by some order of `l`
  §2  the bound is attained: the behavior that answers each asking with the stream of its class
      so far separates all tuples of within-class orders
  §3  a model needs a distinct state for each member of the spectrum
  §4  coarse-graining the answers: commuting survives and the spectrum can only shrink, so an
      order-insensitive summary does not show that the behavior is order-insensitive
-/
import Protocols
import Exchange

namespace PZFC.Spec

open PZFC.Circ PZFC.Proto PZFC.Exch

variable {K Q A C : Type} [DecidableEq C]

/-! ## 1. Only the order within each class matters -/

/-- Askings of different classes commute in the future. -/
def ClassCommute (cls : K × Q → C) (b : Beh K Q A) : Prop :=
  ∀ e e', cls e ≠ cls e' → FutureCommute b e e'

omit [DecidableEq C] in
theorem teq_traceEq (cls : K × Q → C) {l₁ l₂ : List (K × Q)} (h : TEq cls l₁ l₂) :
    TraceEq (fun e e' => cls e ≠ cls e') l₁ l₂ := by
  induction h with
  | refl => exact TraceEq.refl _
  | step hs _ ih => exact TraceEq.step hs ih

/-- **Under commuting classes, the future depends on the askings only through their class
    streams.** -/
theorem residual_streams (cls : K × Q → C) (b : Beh K Q A) (hb : ClassCommute cls b)
    (h : List (K × Q)) {l₁ l₂ : List (K × Q)} (hp : ∀ c, proj cls c l₁ = proj cls c l₂) :
    residual b (h ++ l₁) = residual b (h ++ l₂) := by
  have ht : TEq cls (h ++ l₁) (h ++ l₂) := by
    rw [teq_iff_proj]
    intro c
    rw [proj_append, proj_append, hp c]
  exact trace_residual b _ hb (teq_traceEq cls ht)

variable [DecidableEq K] [DecidableEq Q]

/-- Two words whose class streams are rearrangements of each other are rearrangements of each
    other. -/
theorem perm_of_streams (cls : K × Q → C) (w w' : List (K × Q))
    (h : ∀ c, (proj cls c w).Perm (proj cls c w')) : w.Perm w' := by
  rw [List.perm_iff_count]
  intro a
  have hc := (List.perm_iff_count.mp (h (cls a))) a
  simp only [proj] at hc
  rwa [List.count_filter (by simp), List.count_filter (by simp)] at hc

/-- **Every tuple of within-class orders is realized** by some order of `l`: read the reordered
    streams along the schedule of `l`. -/
theorem realize_streams (cls : K × Q → C) (l : List (K × Q)) (p : C → List (K × Q))
    (hp : ∀ c, (p c).Perm (proj cls c l)) :
    (weave (l.map cls) p).Perm l ∧ ∀ c, proj cls c (weave (l.map cls) p) = p c := by
  have hl : ∀ c, (p c).length = occ c (l.map cls) := fun c => (hp c).length_eq.trans (length_proj c l)
  have hcls : ∀ c, ∀ x ∈ p c, cls x = c := by
    intro c x hx
    have hx' := (hp c).mem_iff.mp hx
    simp only [proj, List.mem_filter, decide_eq_true_eq] at hx'
    exact hx'.2
  obtain ⟨-, h2⟩ := weave_spec (l.map cls) p hl hcls
  refine ⟨perm_of_streams cls _ _ (fun c => ?_), h2⟩
  rw [h2 c]; exact hp c

/-- **The spectrum is the image of the tuples of within-class orders.**  Under commuting classes,
    a behavior is in the spectrum of `l` after `h` exactly when it is reached by reordering each
    class of `l` separately.  So the spectrum has at most as many members as there are ways to
    order each class of `l`, multiplied over the classes. -/
theorem spectrum_iff (cls : K × Q → C) (b : Beh K Q A) (hb : ClassCommute cls b)
    (h l : List (K × Q)) (r : Beh K Q A) :
    InSpectrum b h l r ↔ ∃ p : C → List (K × Q), (∀ c, (p c).Perm (proj cls c l)) ∧
      residual b (h ++ weave (l.map cls) p) = r := by
  constructor
  · rintro ⟨l', hl', rfl⟩
    refine ⟨fun c => proj cls c l', fun c => hl'.filter _, ?_⟩
    have hp : ∀ c, (proj cls c l').Perm (proj cls c l) := fun c => hl'.filter _
    obtain ⟨-, h2⟩ := realize_streams cls l (fun c => proj cls c l') hp
    exact residual_streams cls b hb h h2
  · rintro ⟨p, hp, rfl⟩
    exact ⟨_, (realize_streams cls l p hp).1, rfl⟩

omit [DecidableEq K] [DecidableEq Q] in
/-- In particular, if no class occurs twice in `l`, the order does not matter at all. -/
theorem spectrum_single_of_distinct (cls : K × Q → C) (b : Beh K Q A) (hb : ClassCommute cls b)
    (h l : List (K × Q)) (hl : ∀ c, (proj cls c l).length ≤ 1) (r r' : Beh K Q A)
    (hr : InSpectrum b h l r) (hr' : InSpectrum b h l r') : r = r' := by
  obtain ⟨l₁, hp₁, rfl⟩ := hr
  obtain ⟨l₂, hp₂, rfl⟩ := hr'
  apply residual_streams cls b hb h
  intro c
  have e₁ : (proj cls c l₁).Perm (proj cls c l) := hp₁.filter _
  have e₂ : (proj cls c l₂).Perm (proj cls c l) := hp₂.filter _
  have hc := hl c
  generalize proj cls c l = m at e₁ e₂ hc
  match m, hc with
  | [], _ => rw [List.perm_nil.mp e₁, List.perm_nil.mp e₂]
  | [x], _ => rw [List.perm_singleton.mp e₁, List.perm_singleton.mp e₂]

/-! ## 2. The bound is attained -/

omit [DecidableEq K] [DecidableEq Q] in
/-- The class-history behavior: each asking is answered with the stream of its class so far. -/
def classHist (cls : K × Q → C) : Beh K Q (List (K × Q)) := fun h k q => proj cls (cls (k, q)) h

omit [DecidableEq K] [DecidableEq Q] in
theorem classHist_commute (cls : K × Q → C) : ClassCommute cls (classHist cls) := by
  intro e e' hne h
  funext h' k q
  simp only [residual, classHist, List.append_assoc, List.cons_append, List.nil_append]
  rw [proj_append, proj_append]
  congr 1
  by_cases h1 : cls e = cls (k, q) <;> by_cases h2 : cls e' = cls (k, q)
  · exact absurd (h1.trans h2.symm) hne
  · rw [← h1, proj_cons_self, proj_cons_of_ne (fun h => h2 (h.trans h1)), proj_cons_of_ne
      (fun h => h2 (h.trans h1)), proj_cons_self]
  · rw [← h2, proj_cons_of_ne (fun h => h1 (h.trans h2)), proj_cons_self, proj_cons_self,
      proj_cons_of_ne (fun h => h1 (h.trans h2))]
  · rw [proj_cons_of_ne h1, proj_cons_of_ne h2, proj_cons_of_ne h2, proj_cons_of_ne h1]

omit [DecidableEq K] [DecidableEq Q] in
/-- **The class-history behavior separates the streams**: its future determines the stream of
    every class that some asking belongs to.  So for it, different tuples of within-class orders
    give different members of the spectrum, and the bound of §1 is attained. -/
theorem classHist_separates (cls : K × Q → C) (h₁ h₂ : List (K × Q))
    (he : residual (classHist cls) h₁ = residual (classHist cls) h₂) (e : K × Q) :
    proj cls (cls e) h₁ = proj cls (cls e) h₂ := by
  have := congrFun (congrFun (congrFun he []) e.1) e.2
  simpa [residual, classHist] using this

/-! ## 3. Each member of the spectrum needs its own state -/

omit [DecidableEq C] [DecidableEq K] [DecidableEq Q] in
/-- **A model reaches different states for different members of the spectrum.**  So a model needs
    at least as many states as the spectrum has members: this is the cost of hiding the
    order-dependence. -/
theorem spectrum_states (M : Model K Q A) (b : Beh K Q A) (hM : M.Realizes b)
    (h₁ h₂ : List (K × Q)) (hne : residual b h₁ ≠ residual b h₂) : M.run h₁ ≠ M.run h₂ := by
  intro hs
  apply hne
  rw [← residual_realized M b hM h₁, ← residual_realized M b hM h₂, hs]

/-! ## 4. Coarse-graining the answers -/

omit [DecidableEq C] [DecidableEq K] [DecidableEq Q] in
/-- Coarse-graining commutes with taking residuals. -/
theorem residual_coarse {A' : Type} (f : A → A') (b : Beh K Q A) (h : List (K × Q)) :
    residual (fun h k q => f (b h k q)) h = fun h' k q => f (residual b h h' k q) := rfl

omit [DecidableEq C] [DecidableEq K] [DecidableEq Q] in
/-- Commuting survives coarse-graining. -/
theorem futureCommute_coarse {A' : Type} (f : A → A') (b : Beh K Q A) (e e' : K × Q)
    (hb : FutureCommute b e e') : FutureCommute (fun h k q => f (b h k q)) e e' := by
  intro h
  rw [residual_coarse, residual_coarse, hb h]

omit [DecidableEq C] [DecidableEq K] [DecidableEq Q] in
/-- **The spectrum can only shrink under coarse-graining**: every member of the coarse spectrum is
    the coarse-graining of a member of the fine one. -/
theorem spectrum_coarse {A' : Type} (f : A → A') (b : Beh K Q A) (h l : List (K × Q))
    (r : Beh K Q A) (hr : InSpectrum b h l r) :
    InSpectrum (fun h k q => f (b h k q)) h l (fun h' k q => f (r h' k q)) := by
  obtain ⟨l', hl', rfl⟩ := hr
  exact ⟨l', hl', residual_coarse f b _⟩

omit [DecidableEq C] [DecidableEq K] [DecidableEq Q] in
/-- An order-insensitive summary of an order-sensitive behavior: the memory whose reading updates
    it depends on the order (`lru_future_depends`), yet a summary that forgets the answers
    commutes everywhere. -/
theorem coarse_hides_order :
    ¬ AllFutureCommute lruB ∧ AllFutureCommute (fun h k q => (fun _ => ()) (lruB h k q)) := by
  refine ⟨fun hb => lru_future_depends ?_, fun e e' h => rfl⟩
  exact perm_residual lruB hb (List.Perm.append_left [st 0, st 1] (List.Perm.swap (st 2) (rd 0) []))

end PZFC.Spec
