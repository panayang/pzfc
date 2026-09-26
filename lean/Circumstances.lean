/-
  The circumstances of asking (notes/47).  Mathlib-free.

  A deterministic behavior gives, after a history of (asker, question) events,
  the answer that an asker gets to a question.  Randomness is left to the
  mathlib part; here the circumstances "who asks" and "what was asked before"
  are isolated.

  §1  behaviors; public, undisturbed; a record model exists exactly when
      the behavior is both
  §2  hiding: every behavior has a hidden-state model (the state is the history);
      a behavior is undisturbed exactly when some model never moves its state
  §3  the price of hiding a disturbance: every model realizes every residual
      behavior by some state, so it needs at least as many states as there are
      residuals; the residual model needs exactly those; undisturbed exactly
      when there is one residual
  §4  the failures are independent: a behavior that is disturbed but public and
      repeatable (asking one question changes the answer to another), and a
      relative behavior that is undisturbed; the flipped memory is disturbed and
      not repeatable, and needs at least two hidden states (one hidden bit)
  §5  tasks are facts; a prediction is a task that fixes every answer; the
      relation "consecutive answers differ" is a task that is not a prediction
  §6  facts see the structure, not the position (notes/48): two behaviors have
      the same invariant facts exactly when they have the same residuals; for an
      undisturbed behavior the facts fix everything; the two flipped memories
      share all facts and differ; the marking memory, whose disturbance cannot
      be undone, is fixed by its facts; in general the position is a fact exactly
      when no other residual can still do the same things
  §7  a memory whose reading updates it: two slots, most recently used first;
      storing then reading finds the item, at every history; reading an item
      protects it from the next eviction, so reading changes what a later reading
      finds; reading the same item again gives the same answer; what a single
      reading shows depends on the history
  §8  evaluation that can be redone at any time (notes/53): an evaluation that gives
      the same result whenever it is made sees a behavior only through everything
      it can become; it cannot tell the marking memory before marking from after;
      the facts themselves change with time exactly when some possibility closes
      off, and stay the same in a recurrent behavior
-/

namespace PZFC.Circ

/-- A behavior: after a history of (asker, question) events, the answer that
    asker `k` gets to question `q`. -/
abbrev Beh (K Q A : Type) : Type := List (K × Q) → K → Q → A

variable {K Q A : Type}

/-! ## 1. Public, undisturbed, record -/

/-- Public: every asker gets the same answer. -/
def Public (b : Beh K Q A) : Prop := ∀ h k k' q, b h k q = b h k' q

/-- Undisturbed: what was asked before does not matter. -/
def Undisturbed (b : Beh K Q A) : Prop := ∀ h h' k q, b h k q = b h' k q

/-- A record model: one assignment of answers, read by everyone at any time. -/
def HasRecordModel (b : Beh K Q A) : Prop := ∃ r : Q → A, ∀ h k q, b h k q = r q

/-- A behavior has a record model exactly when it is public and undisturbed. -/
theorem record_iff (k₀ : K) (b : Beh K Q A) :
    HasRecordModel b ↔ Public b ∧ Undisturbed b := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨fun h k k' q => by rw [hr, hr], fun h h' k q => by rw [hr, hr]⟩
  · rintro ⟨hp, hu⟩
    exact ⟨fun q => b [] k₀ q, fun h k q => by rw [hu h [] k q, hp [] k k₀ q]⟩

/-! ## 2. Hiding: a hidden-state model always exists -/

/-- A hidden-state model: states, a start, how an asked question moves the state,
    and the answer read off the state. -/
structure Model (K Q A : Type) where
  S : Type
  start : S
  move : S → K × Q → S
  out : S → K → Q → A

/-- The state after a history, from a given state. -/
def Model.runFrom (M : Model K Q A) (s : M.S) (h : List (K × Q)) : M.S := h.foldl M.move s

/-- The state after a history. -/
def Model.run (M : Model K Q A) (h : List (K × Q)) : M.S := M.runFrom M.start h

/-- The model gives the behavior. -/
def Model.Realizes (M : Model K Q A) (b : Beh K Q A) : Prop :=
  ∀ h k q, M.out (M.run h) k q = b h k q

/-- The model whose state is the whole history. -/
def historyModel (b : Beh K Q A) : Model K Q A where
  S := List (K × Q)
  start := []
  move s e := s ++ [e]
  out := b

theorem foldl_snoc (s h : List (K × Q)) : h.foldl (fun s e => s ++ [e]) s = s ++ h := by
  induction h generalizing s with
  | nil => simp
  | cons e h ih => simp [List.foldl, ih]

/-- **Every behavior has a hidden-state model**: hiding the history in the state. -/
theorem historyModel_realizes (b : Beh K Q A) : (historyModel b).Realizes b := by
  intro h k q
  show b (h.foldl (fun s e => s ++ [e]) []) k q = b h k q
  rw [foldl_snoc]; rfl

/-- A model that never moves its state. -/
def Model.Static (M : Model K Q A) : Prop := ∀ s e, M.move s e = s

theorem Model.runFrom_static (M : Model K Q A) (hM : M.Static) (s : M.S) (h : List (K × Q)) :
    M.runFrom s h = s := by
  induction h generalizing s with
  | nil => rfl
  | cons e h ih =>
    show h.foldl M.move (M.move s e) = s
    rw [hM s e]; exact ih s

/-- A behavior is undisturbed exactly when some model realizes it without ever moving. -/
theorem undisturbed_iff_static (b : Beh K Q A) :
    Undisturbed b ↔ ∃ M : Model K Q A, M.Realizes b ∧ M.Static := by
  constructor
  · intro hu
    refine ⟨⟨Unit, (), fun _ _ => (), fun _ k q => b [] k q⟩, fun h k q => ?_, fun _ _ => rfl⟩
    exact (hu h [] k q).symm
  · rintro ⟨M, hM, hs⟩ h h' k q
    rw [← hM h k q, ← hM h' k q]
    show M.out (M.runFrom M.start h) k q = M.out (M.runFrom M.start h') k q
    rw [M.runFrom_static hs, M.runFrom_static hs]

/-! ## 3. The price of hiding a disturbance -/

/-- What the behavior still does after a history: its residual. -/
def residual (b : Beh K Q A) (h : List (K × Q)) : Beh K Q A := fun h' k q => b (h ++ h') k q

/-- What a model does from a state. -/
def Model.stateBeh (M : Model K Q A) (s : M.S) : Beh K Q A := fun h' k q => M.out (M.runFrom s h') k q

theorem Model.runFrom_append (M : Model K Q A) (s : M.S) (h h' : List (K × Q)) :
    M.runFrom s (h ++ h') = M.runFrom (M.runFrom s h) h' := by
  simp [Model.runFrom, List.foldl_append]

/-- **Every residual is some state's behavior**: a model needs at least as many
    states as the behavior has residuals. -/
theorem residual_realized (M : Model K Q A) (b : Beh K Q A) (hM : M.Realizes b)
    (h : List (K × Q)) : M.stateBeh (M.run h) = residual b h := by
  funext h' k q
  show M.out (M.runFrom (M.runFrom M.start h) h') k q = b (h ++ h') k q
  rw [← M.runFrom_append]; exact hM (h ++ h') k q

/-- The residual model: its states are behaviors; it needs no more states than residuals. -/
def residualModel (b : Beh K Q A) : Model K Q A where
  S := Beh K Q A
  start := b
  move r e := fun h' k q => r (e :: h') k q
  out r k q := r [] k q

theorem residualModel_run (b : Beh K Q A) (h : List (K × Q)) :
    (residualModel b).run h = residual b h := by
  suffices ∀ r : Beh K Q A, (residualModel b).runFrom r h = fun h' k q => r (h ++ h') k q by
    exact this b
  induction h with
  | nil => intro r; rfl
  | cons e h ih =>
    intro r
    exact ih (fun h' k q => r (e :: h') k q)

theorem residualModel_realizes (b : Beh K Q A) : (residualModel b).Realizes b := by
  intro h k q
  show (residualModel b).run h [] k q = b h k q
  rw [residualModel_run]; simp [residual]

/-- Undisturbed exactly when there is one residual: the behavior itself. -/
theorem undisturbed_iff_one_residual (b : Beh K Q A) :
    Undisturbed b ↔ ∀ h, residual b h = b := by
  constructor
  · intro hu h; funext h' k q; exact hu (h ++ h') h' k q
  · intro hr h h' k q
    have e1 := congrFun (congrFun (congrFun (hr h) []) k) q
    have e2 := congrFun (congrFun (congrFun (hr h') []) k) q
    simp only [residual, List.append_nil] at e1 e2
    rw [e1, e2]

/-! ## 4. The failures are independent -/

/-- The flipped memory: one asker, one question; the answer flips with every reading. -/
def flipB : Beh Unit Unit Bool := fun h _ _ => decide (h.length % 2 = 1)

theorem flipB_public : Public flipB := fun _ _ _ _ => rfl

theorem flipB_disturbed : ¬ Undisturbed flipB := by
  intro hu
  have := hu [((), ())] [] () ()
  exact absurd this (by decide)

/-- Hiding the flip needs at least two hidden states: one hidden bit. -/
theorem flipB_two_states (M : Model Unit Unit Bool) (hM : M.Realizes flipB) :
    M.run [] ≠ M.run [((), ())] := by
  intro heq
  have e := congrArg (fun s => M.stateBeh s [] () ()) heq
  simp only [residual_realized M flipB hM] at e
  exact absurd e (by decide)

/-- Repeatable: asking the same question again, right away, gives the same answer. -/
def Repeatable (b : Beh K Q A) : Prop := ∀ h k q, b (h ++ [(k, q)]) k q = b h k q

theorem flipB_not_repeatable : ¬ Repeatable flipB := by
  intro hr
  exact absurd (hr [] () ()) (by decide)

/-- Asking the first question marks the memory; the second question asks whether it
    was marked.  Disturbed, yet each question asked again gives the same answer. -/
def markB : Beh Unit Bool Bool := fun h _ q => if q then decide (((), false) ∈ h) else false

theorem markB_public : Public markB := fun _ _ _ _ => rfl

theorem markB_disturbed : ¬ Undisturbed markB := by
  intro hu
  exact absurd (hu [((), false)] [] () true) (by decide)

theorem markB_repeatable : Repeatable markB := by
  intro h k q
  cases q
  · rfl
  · show decide (((), false) ∈ h ++ [(k, true)]) = decide (((), false) ∈ h)
    simp

/-- A relative behavior: each of two askers gets its own name, at any time. -/
def nameB : Beh Bool Unit Bool := fun _ k _ => k

theorem nameB_undisturbed : Undisturbed nameB := fun _ _ _ _ => rfl

theorem nameB_repeatable : Repeatable nameB := fun _ _ _ => rfl

theorem nameB_relative : ¬ Public nameB := by
  intro hp
  exact absurd (hp [] true false ()) (by decide)

/-- Yet "the two askers get different answers" holds at every history: a public fact
    about relative answers. -/
theorem nameB_relation (h : List (Bool × Unit)) : nameB h true () ≠ nameB h false () := by
  show true ≠ false
  decide

/-! ## 5. Tasks are facts; predictions are special tasks -/

/-- A task: a property of behaviors. -/
def Task (K Q A : Type) : Type := Beh K Q A → Prop

/-- A prediction: a task that fixes every answer. -/
def IsPrediction (T : Task K Q A) : Prop := ∀ b b', T b → T b' → b = b'

/-- "Consecutive answers differ", at every history. -/
def flipTask : Task Unit Unit Bool :=
  fun b => ∀ h, b (h ++ [((), ())]) () () ≠ b h () ()

/-- The flipped memory, started the other way. -/
def flipB' : Beh Unit Unit Bool := fun h _ _ => decide (h.length % 2 = 0)

theorem flipB_task : flipTask flipB := by
  intro h
  show decide ((h ++ [((), ())]).length % 2 = 1) ≠ decide (h.length % 2 = 1)
  rw [List.length_append, List.length_singleton]
  rcases Nat.mod_two_eq_zero_or_one h.length with e | e
  · have e' : (h.length + 1) % 2 = 1 := by omega
    simp [e, e']
  · have e' : (h.length + 1) % 2 = 0 := by omega
    simp [e, e']

theorem flipB'_task : flipTask flipB' := by
  intro h
  show decide ((h ++ [((), ())]).length % 2 = 0) ≠ decide (h.length % 2 = 0)
  rw [List.length_append, List.length_singleton]
  rcases Nat.mod_two_eq_zero_or_one h.length with e | e
  · have e' : (h.length + 1) % 2 = 1 := by omega
    simp [e, e']
  · have e' : (h.length + 1) % 2 = 0 := by omega
    simp [e, e']

/-- **The relational task is not a prediction**: it holds for two different behaviors. -/
theorem flipTask_not_prediction : ¬ IsPrediction flipTask := by
  intro hp
  have := congrFun (congrFun (congrFun (hp flipB flipB' flipB_task flipB'_task) []) ()) ()
  exact absurd this (by decide)

/-- Fixing every answer is a prediction. -/
theorem exact_is_prediction (b₀ : Beh K Q A) : IsPrediction (fun b => b = b₀) := by
  intro b b' h h'; rw [h, h']

/-! ## 6. Facts see the structure, not the position -/

/-- `r` is something the behavior can still do, after some history. -/
def IsResidual (b r : Beh K Q A) : Prop := ∃ h, residual b h = r

/-- An invariant fact of `b`: a property of what it can still do, after every history. -/
def InvFact (P : Beh K Q A → Prop) (b : Beh K Q A) : Prop := ∀ h, P (residual b h)

/-- Two behaviors with the same invariant facts. -/
def SameFacts (b b' : Beh K Q A) : Prop := ∀ P : Beh K Q A → Prop, InvFact P b ↔ InvFact P b'

theorem residual_nil (b : Beh K Q A) : residual b [] = b := by
  funext h' k q; simp [residual]

/-- **The invariant facts are exactly the residuals**: two behaviors have the same
    invariant facts iff they can still do the same things. -/
theorem sameFacts_iff (b b' : Beh K Q A) :
    SameFacts b b' ↔ ∀ r, IsResidual b r ↔ IsResidual b' r := by
  constructor
  · intro hs r
    constructor
    · rintro ⟨h, rfl⟩
      exact ((hs (IsResidual b')).mpr (fun h' => ⟨h', rfl⟩)) h
    · rintro ⟨h, rfl⟩
      exact ((hs (IsResidual b)).mp (fun h' => ⟨h', rfl⟩)) h
  · intro hr P
    constructor
    · intro hP h
      obtain ⟨h₀, e⟩ := (hr (residual b' h)).mpr ⟨h, rfl⟩
      rw [← e]; exact hP h₀
    · intro hP h
      obtain ⟨h₀, e⟩ := (hr (residual b h)).mp ⟨h, rfl⟩
      rw [← e]; exact hP h₀

/-- **For an undisturbed behavior, the facts fix everything**: structure and position
    coincide. -/
theorem undisturbed_facts_determine (b b' : Beh K Q A) (hu : Undisturbed b)
    (hs : SameFacts b b') : b' = b := by
  obtain ⟨h, e⟩ := ((sameFacts_iff b b').mp hs b').mpr ⟨[], residual_nil b'⟩
  rw [← e]; exact (undisturbed_iff_one_residual b).mp hu h

theorem residual_flipB (h : List (Unit × Unit)) :
    residual flipB h = if h.length % 2 = 0 then flipB else flipB' := by
  rcases Nat.mod_two_eq_zero_or_one h.length with e | e
  · rw [if_pos e]
    funext h' k q
    show decide ((h ++ h').length % 2 = 1) = decide (h'.length % 2 = 1)
    rw [List.length_append]
    rcases Nat.mod_two_eq_zero_or_one h'.length with e' | e' <;> simp [Nat.add_mod, e, e']
  · rw [if_neg (by omega)]
    funext h' k q
    show decide ((h ++ h').length % 2 = 1) = decide (h'.length % 2 = 0)
    rw [List.length_append]
    rcases Nat.mod_two_eq_zero_or_one h'.length with e' | e' <;> simp [Nat.add_mod, e, e']

theorem residual_flipB' (h : List (Unit × Unit)) :
    residual flipB' h = if h.length % 2 = 0 then flipB' else flipB := by
  rcases Nat.mod_two_eq_zero_or_one h.length with e | e
  · rw [if_pos e]
    funext h' k q
    show decide ((h ++ h').length % 2 = 0) = decide (h'.length % 2 = 0)
    rw [List.length_append]
    rcases Nat.mod_two_eq_zero_or_one h'.length with e' | e' <;> simp [Nat.add_mod, e, e']
  · rw [if_neg (by omega)]
    funext h' k q
    show decide ((h ++ h').length % 2 = 0) = decide (h'.length % 2 = 1)
    rw [List.length_append]
    rcases Nat.mod_two_eq_zero_or_one h'.length with e' | e' <;> simp [Nat.add_mod, e, e']

theorem isResidual_flip (b : Beh Unit Unit Bool) (hb : b = flipB ∨ b = flipB')
    (r : Beh Unit Unit Bool) : IsResidual b r ↔ r = flipB ∨ r = flipB' := by
  constructor
  · rintro ⟨h, rfl⟩
    rcases hb with rfl | rfl
    · rw [residual_flipB]; split <;> simp
    · rw [residual_flipB']; split <;> simp
  · rintro (rfl | rfl) <;> rcases hb with rfl | rfl
    · exact ⟨[], by rw [residual_nil]⟩
    · exact ⟨[((), ())], by rw [residual_flipB']; rfl⟩
    · exact ⟨[((), ())], by rw [residual_flipB]; rfl⟩
    · exact ⟨[], by rw [residual_nil]⟩

/-- **The two flipped memories share all their invariant facts, and differ**: the facts
    see the structure (the two phases), not the position (which phase is now). -/
theorem flip_facts_not_position : SameFacts flipB flipB' ∧ flipB ≠ flipB' := by
  refine ⟨(sameFacts_iff _ _).mpr fun r => ?_, fun e => ?_⟩
  · rw [isResidual_flip flipB (Or.inl rfl), isResidual_flip flipB' (Or.inr rfl)]
  · exact absurd (congrFun (congrFun (congrFun e []) ()) ()) (by decide)

theorem residual_residual (b : Beh K Q A) (h h' : List (K × Q)) :
    residual (residual b h) h' = residual b (h ++ h') := by
  funext h'' k q; simp [residual, List.append_assoc]

/-- The position is a fact: every behavior with the same invariant facts is this one. -/
def PositionIsFact (b : Beh K Q A) : Prop := ∀ b', SameFacts b b' → b' = b

/-- **The general criterion**: the position is a fact exactly when no other residual can
    still do the same things as the behavior itself. -/
theorem positionIsFact_iff (b : Beh K Q A) :
    PositionIsFact b ↔ ∀ r, IsResidual b r → (∀ r', IsResidual r r' ↔ IsResidual b r') → r = b := by
  constructor
  · intro hp r _ hsame
    exact hp r ((sameFacts_iff b r).mpr fun r' => (hsame r').symm)
  · intro hc b' hs
    have hr := (sameFacts_iff b b').mp hs
    obtain ⟨h, e⟩ := (hr b').mpr ⟨[], residual_nil b'⟩
    exact hc b' ⟨h, e⟩ fun r' => (hr r').symm

/-- The marked memory: the mark is there, whatever is asked. -/
def markedB : Beh Unit Bool Bool := fun _ _ q => q

theorem markedB_undisturbed : Undisturbed markedB := fun _ _ _ _ => rfl

theorem residual_markB (h : List (Unit × Bool)) :
    residual markB h = if ((), false) ∈ h then markedB else markB := by
  by_cases hm : ((), false) ∈ h
  · rw [if_pos hm]
    funext h' k q
    cases q
    · rfl
    · show decide (((), false) ∈ h ++ h') = true
      simp [hm]
  · rw [if_neg hm]
    funext h' k q
    cases q
    · rfl
    · show decide (((), false) ∈ h ++ h') = decide (((), false) ∈ h')
      simp [hm]

theorem markB_ne_markedB : markB ≠ markedB := by
  intro e
  exact absurd (congrFun (congrFun (congrFun e []) ()) true) (by decide)

/-- **The marking memory is fixed by its facts**: its disturbance cannot be undone, so
    where it starts is itself a fact. -/
theorem markB_facts_determine (b' : Beh Unit Bool Bool) (hs : SameFacts markB b') :
    b' = markB := by
  have hr := (sameFacts_iff markB b').mp hs
  obtain ⟨h, e⟩ := (hr b').mpr ⟨[], residual_nil b'⟩
  rw [residual_markB] at e
  split at e
  · -- b' is the marked memory; then markB would be a residual of it
    subst e
    obtain ⟨h₂, e₂⟩ := (hr markB).mp ⟨[], residual_nil markB⟩
    rw [(undisturbed_iff_one_residual markedB).mp markedB_undisturbed h₂] at e₂
    exact absurd e₂.symm markB_ne_markedB
  · exact e.symm

/-! ## 7. A memory whose reading updates it -/

/-- Three items. -/
abbrev Item := Fin 3

/-- Two slots, most recently used first: storing puts the item in front. -/
def lruStore (x : Item) (s : List Item) : List Item := (x :: s.erase x).take 2

/-- Reading finds the item or not; if found, it moves to the front. -/
def lruRead (x : Item) (s : List Item) : List Item :=
  if x ∈ s then (x :: s.erase x).take 2 else s

/-- A question: store an item (`false`) or read it (`true`). -/
def lruMove (s : List Item) (e : Unit × (Bool × Item)) : List Item :=
  if e.2.1 then lruRead e.2.2 s else lruStore e.2.2 s

def lruModel : Model Unit (Bool × Item) Bool where
  S := List Item
  start := []
  move := lruMove
  out s _ q := if q.1 then decide (q.2 ∈ s) else true

/-- The memory as a behavior. -/
def lruB : Beh Unit (Bool × Item) Bool := fun h k q => lruModel.out (lruModel.run h) k q

/-- The memory's contents after a history. -/
def lruRun (h : List (Unit × (Bool × Item))) : List Item := h.foldl lruMove []

theorem lruB_eq (h : List (Unit × (Bool × Item))) (q : Bool × Item) :
    lruB h () q = if q.1 then decide (q.2 ∈ lruRun h) else true := rfl

theorem lru_run_append (h h' : List (Unit × (Bool × Item))) :
    lruRun (h ++ h') = h'.foldl lruMove (lruRun h) := by
  simp [lruRun, List.foldl_append]

/-- After storing two different items, the memory holds exactly them, whatever came before. -/
theorem lru_two (s : List Item) {x y : Item} (hxy : x ≠ y) :
    lruStore y (lruStore x s) = [y, x] := by
  have hb : (x == y) = false := by simp [hxy]
  simp [lruStore, hb]

def st (x : Item) : Unit × (Bool × Item) := ((), (false, x))
def rd (x : Item) : Unit × (Bool × Item) := ((), (true, x))

/-- **Storing then reading finds the item**, after every history. -/
theorem lru_store_read (h : List (Unit × (Bool × Item))) (x : Item) :
    lruB (h ++ [st x]) () (true, x) = true := by
  rw [lruB_eq]
  show decide (x ∈ lruRun (h ++ [st x])) = true
  rw [lru_run_append]
  simp [lruMove, st, lruStore]

/-- **Reading protects**: store 0, store 1, read 0, store 2 — then 0 is still there,
    after every history. -/
theorem lru_read_protects (h : List (Unit × (Bool × Item))) :
    lruB (h ++ [st 0, st 1, rd 0, st 2]) () (true, 0) = true := by
  rw [lruB_eq]
  show decide ((0 : Item) ∈ lruRun (h ++ [st 0, st 1, rd 0, st 2])) = true
  rw [lru_run_append]
  show decide ((0 : Item) ∈ lruMove (lruMove (lruStore 1 (lruStore 0 (lruRun h))) (rd 0))
    (st 2)) = true
  rw [lru_two _ (by decide)]
  decide

/-- Without the reading, 0 is gone: **reading changes what a later reading finds**. -/
theorem lru_no_read_evicts (h : List (Unit × (Bool × Item))) :
    lruB (h ++ [st 0, st 1, st 2]) () (true, 0) = false := by
  rw [lruB_eq]
  show decide ((0 : Item) ∈ lruRun (h ++ [st 0, st 1, st 2])) = false
  rw [lru_run_append]
  show decide ((0 : Item) ∈ lruStore 2 (lruStore 1 (lruStore 0 (lruRun h)))) = false
  rw [lru_two _ (by decide)]
  decide

/-- Reading the same item again gives the same answer. -/
theorem lru_read_repeatable (h : List (Unit × (Bool × Item))) (x : Item) :
    lruB (h ++ [rd x]) () (true, x) = lruB h () (true, x) := by
  rw [lruB_eq, lruB_eq]
  show decide (x ∈ lruRun (h ++ [rd x])) = decide (x ∈ lruRun h)
  rw [lru_run_append]
  show decide (x ∈ lruRead x (lruRun h)) = decide (x ∈ lruRun h)
  unfold lruRead
  split
  · rename_i hx; simp [hx]
  · rfl

/-- What a single reading shows depends on the history before it. -/
theorem lru_snapshot_depends :
    lruB [st 0] () (true, 0) = true ∧ lruB [st 0, st 1, st 2] () (true, 0) = false := by
  decide

/-- The memory is disturbed: histories differing by one reading give different answers. -/
theorem lru_disturbed : ¬ Undisturbed lruB := by
  intro hu
  have e := hu [st 0, st 1, rd 0, st 2] [st 0, st 1, st 2] () (true, 0)
  rw [show [st 0, st 1, rd 0, st 2] = [] ++ [st 0, st 1, rd 0, st 2] from rfl,
    show [st 0, st 1, st 2] = [] ++ [st 0, st 1, st 2] from rfl,
    lru_read_protects, lru_no_read_evicts] at e
  exact absurd e (by decide)

/-! ## 8. Evaluation that can be redone at any time -/

/-- An evaluation that gives the same result whenever it is made: after any history. -/
def TimeInvariant {X : Type} (E : Beh K Q A → X) : Prop := ∀ b h, E (residual b h) = E b

/-- A time-invariant evaluation gives a behavior the same value as everything it can become. -/
theorem timeInvariant_residual {X : Type} (E : Beh K Q A → X) (hE : TimeInvariant E)
    (b r : Beh K Q A) (hr : IsResidual b r) : E r = E b := by
  obtain ⟨h, rfl⟩ := hr; exact hE b h

/-- **A time-invariant evaluation cannot tell the marking memory from what it becomes**:
    before marking and after marking get the same value. -/
theorem timeInvariant_mark {X : Type} (E : Beh Unit Bool Bool → X) (hE : TimeInvariant E) :
    E markB = E markedB := by
  have : residual markB [((), false)] = markedB := by
    rw [residual_markB]; simp
  rw [← this, hE]

/-- The facts of the marking memory change with time: after marking, it can no longer do
    what it could before. -/
theorem mark_facts_change : ¬ SameFacts markB (residual markB [((), false)]) := by
  have e : residual markB [((), false)] = markedB := by rw [residual_markB]; simp
  rw [e, sameFacts_iff]
  intro hs
  obtain ⟨h, hh⟩ := (hs markB).mp ⟨[], residual_nil markB⟩
  rw [(undisturbed_iff_one_residual markedB).mp markedB_undisturbed h] at hh
  exact markB_ne_markedB hh.symm

/-- A recurrent behavior: whatever it becomes can still do everything it can. -/
def Recurrent (b : Beh K Q A) : Prop :=
  ∀ h r, IsResidual (residual b h) r ↔ IsResidual b r

/-- **In a recurrent behavior the facts do not change with time.** -/
theorem recurrent_facts_stay (b : Beh K Q A) (hb : Recurrent b) (h : List (K × Q)) :
    SameFacts b (residual b h) :=
  (sameFacts_iff _ _).mpr fun r => (hb h r).symm

/-- The flipped memory is recurrent. -/
theorem flipB_recurrent : Recurrent flipB := by
  intro h r
  rw [isResidual_flip flipB (Or.inl rfl)]
  rw [residual_flipB]
  split
  · exact isResidual_flip flipB (Or.inl rfl) r
  · exact isResidual_flip flipB' (Or.inr rfl) r

end PZFC.Circ
