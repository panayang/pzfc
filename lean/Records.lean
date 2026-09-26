/-
  Records and sources (notes/42).  Mathlib-free.

  A finite source is an urn: a nonempty list of outcomes, read by drawing
  one outcome uniformly, with replacement.  Two independent readings give
  all ordered pairs.  A record is a source whose readings always agree.

  §1  two readings, and one reading copied
  §2  a record is exactly a source that re-reading cannot tell from copying;
      the repeat defect counts the disagreements and is zero exactly on records
  §3  the statistics survive re-reading: each reading alone has the source's law
  §4  X + X is not 2X for a source
  §5  the parts do not determine the whole, unless the parts are records
  §6  GLU seen as records: answers asked in many contexts come from one
      global object exactly when each answer is a record across contexts
      (the same in every context where it is asked); the object is unique
  §7  asking changes the asked (notes/46): a memory flipped by every reading;
      its answer is not a record and has no stable law, yet the relation
      between consecutive answers holds at every point of every history
-/

namespace PZFC.Records

/-! ## 1. Two readings, and one reading copied -/

/-- One reading of `u` and one reading of `v`, independently: all ordered pairs. -/
def pairs {α β : Type} (u : List α) (v : List β) : List (α × β) :=
  u.flatMap (fun a => v.map (fun b => (a, b)))

/-- Two independent readings of the same source. -/
def twice {α : Type} (u : List α) : List (α × α) := pairs u u

/-- One reading, written down and copied. -/
def copied {α : Type} (u : List α) : List (α × α) := u.map (fun a => (a, a))

theorem mem_pairs {α β : Type} {u : List α} {v : List β} {a : α} {b : β} :
    (a, b) ∈ pairs u v ↔ a ∈ u ∧ b ∈ v := by
  simp [pairs]

theorem mem_copied {α : Type} {u : List α} {a b : α} :
    (a, b) ∈ copied u ↔ a ∈ u ∧ a = b := by
  simp [copied]
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩; exact ⟨h, rfl⟩

/-! ## 2. Records -/

/-- A record: any two readings agree. -/
def IsRecord {α : Type} (u : List α) : Prop :=
  ∀ a ∈ u, ∀ b ∈ u, a = b

/-- A record is exactly a source whose two independent readings could always
    have come from copying one reading. -/
theorem record_iff_twice_copied {α : Type} (u : List α) :
    IsRecord u ↔ ∀ p ∈ twice u, p ∈ copied u := by
  constructor
  · rintro h ⟨a, b⟩ hp
    have hab := (mem_pairs.mp hp)
    exact mem_copied.mpr ⟨hab.1, h a hab.1 b hab.2⟩
  · intro h a ha b hb
    exact (mem_copied.mp (h (a, b) (mem_pairs.mpr ⟨ha, hb⟩))).2

/-- The repeat defect: the number of pairs of independent readings that disagree. -/
def defect {α : Type} [DecidableEq α] (u : List α) : Nat :=
  (twice u).countP (fun p => decide (p.1 ≠ p.2))

/-- The repeat defect is zero exactly on records. -/
theorem defect_eq_zero {α : Type} [DecidableEq α] (u : List α) :
    defect u = 0 ↔ IsRecord u := by
  unfold defect
  rw [List.countP_eq_zero]
  constructor
  · intro h a ha b hb
    have h' : ¬ decide (a ≠ b) = true := h (a, b) (mem_pairs.mpr ⟨ha, hb⟩)
    exact Decidable.of_not_not (fun hne => h' (decide_eq_true hne))
  · rintro h ⟨a, b⟩ hp hd
    have hab := mem_pairs.mp hp
    exact (of_decide_eq_true hd) (h a hab.1 b hab.2)

/-! ## 3. The statistics survive re-reading -/

/-- The first of two independent readings has the source's law
    (each outcome counted once for every possible second reading). -/
theorem first_reading {α β : Type} [DecidableEq α] (u : List α) (v : List β) (a : α) :
    ((pairs u v).map Prod.fst).count a = v.length * u.count a := by
  induction u with
  | nil => simp [pairs]
  | cons x u ih =>
    have hx : (v.map (fun b => (x, b))).map Prod.fst = List.replicate v.length x := by
      clear ih
      induction v with
      | nil => rfl
      | cons y v ihv => simp [List.replicate_succ, ihv]
    have hsplit : pairs (x :: u) v = v.map (fun b => (x, b)) ++ pairs u v := by
      simp [pairs]
    rw [hsplit, List.map_append, List.count_append, hx, ih, List.count_replicate,
      List.count_cons]
    by_cases h : (x == a) = true
    · simp [h, Nat.mul_add, Nat.add_comm]
    · simp [h]

/-- The second of two independent readings has the source's law too. -/
theorem second_reading {α β : Type} [DecidableEq β] (u : List α) (v : List β) (b : β) :
    ((pairs u v).map Prod.snd).count b = u.length * v.count b := by
  induction u with
  | nil => simp [pairs]
  | cons x u ih =>
    have hx : (v.map (fun b => (x, b))).map Prod.snd = v := by
      clear ih
      induction v with
      | nil => rfl
      | cons y v ihv => simp [ihv]
    have hsplit : pairs (x :: u) v = v.map (fun b => (x, b)) ++ pairs u v := by
      simp [pairs]
    rw [hsplit, List.map_append, List.count_append, hx, ih, List.length_cons,
      Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-! ## 4. X + X is not 2X -/

/-- A fair source of 0 and 1, read twice and added, can give 1. -/
theorem read_twice_sum : (twice [0, 1]).map (fun p => p.1 + p.2) = [0, 1, 1, 2] := by
  decide

/-- The same source read once and doubled never gives 1. -/
theorem copy_sum : (copied [0, 1]).map (fun p => p.1 + p.2) = [0, 2] := by
  decide

/-! ## 5. Parts and whole -/

/-- Two joint sources for two fair bits: always equal, or always different. -/
def sameJ : List (Bool × Bool) := [(true, true), (false, false)]
def oppJ : List (Bool × Bool) := [(true, false), (false, true)]

/-- The parts have the same laws in both joints. -/
theorem same_parts (b : Bool) :
    (sameJ.map Prod.fst).count b = (oppJ.map Prod.fst).count b ∧
    (sameJ.map Prod.snd).count b = (oppJ.map Prod.snd).count b := by
  cases b <;> decide

/-- The wholes differ: one always agrees, the other never. -/
theorem different_wholes :
    sameJ.countP (fun p => p.1 == p.2) = 2 ∧ oppJ.countP (fun p => p.1 == p.2) = 0 := by
  decide

/-- When the parts are records, the whole is determined by them: every joint
    reading whose parts are readings of the two records is the one pair. -/
theorem records_fix_whole {α β : Type} {u : List α} {v : List β} {a : α} {b : β}
    (hu : IsRecord u) (hv : IsRecord v) (ha : a ∈ u) (hb : b ∈ v)
    (j : List (α × β)) (hj : ∀ p ∈ j, p.1 ∈ u ∧ p.2 ∈ v) :
    ∀ p ∈ j, p = (a, b) := by
  rintro ⟨x, y⟩ hp
  have h := hj (x, y) hp
  rw [hu x h.1 a ha, hv y h.2 b hb]

/-! ## 6. GLU is "the answers are records", seen from the results -/

/-- A scene: questions, contexts (which questions are asked together), and
    for each question a designated context where it can be asked. -/
structure Scene where
  Q : Type
  C : Type
  O : Type
  mem : Q → C → Prop
  home : Q → C
  home_mem : ∀ q, mem q (home q)

/-- The answers given in each context, to each question asked there. -/
def Answers (S : Scene) : Type := ∀ c : S.C, ∀ q : S.Q, S.mem q c → S.O

/-- The answers are records across contexts: a question gets the same answer
    in every context where it is asked. -/
def ContextFree {S : Scene} (a : Answers S) : Prop :=
  ∀ q c c' (h : S.mem q c) (h' : S.mem q c'), a c q h = a c' q h'

/-- One global object whose readings are the answers: a joint record. -/
def GluedBy {S : Scene} (a : Answers S) (g : S.Q → S.O) : Prop :=
  ∀ c q (h : S.mem q c), a c q h = g q

/-- GLU, existence, is exactly: the answers are records across contexts. -/
theorem glues_iff_contextFree {S : Scene} (a : Answers S) :
    (∃ g, GluedBy a g) ↔ ContextFree a := by
  constructor
  · rintro ⟨g, hg⟩ q c c' h h'
    rw [hg c q h, hg c' q h']
  · intro hf
    exact ⟨fun q => a (S.home q) q (S.home_mem q),
      fun c q h => hf q c (S.home q) h (S.home_mem q)⟩

/-- GLU, uniqueness: the global object is determined by the answers. -/
theorem glue_unique {S : Scene} (a : Answers S) (g g' : S.Q → S.O)
    (hg : GluedBy a g) (hg' : GluedBy a g') : g = g' := by
  funext q
  rw [← hg (S.home q) q (S.home_mem q), hg' (S.home q) q (S.home_mem q)]

/-! ## 7. Asking changes the asked: a toy -/

/-- A memory flipped by every reading: the answer to the `n`-th reading. -/
def flipAns (n : Nat) : Bool := decide (n % 2 = 1)

/-- Asking again gives a different answer: the answer is not a record. -/
theorem flip_not_repeatable : flipAns 0 ≠ flipAns 1 := by decide

/-- What a single reading shows depends on the history before it: evaluating at
    different points of the history gives different results. -/
theorem flip_depends_on_history : ∀ b : Bool, ∃ n, flipAns n = b := by
  intro b; cases b
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩

/-- The relation between consecutive answers is a record: it holds at every point
    of every history. -/
theorem flip_relation (n : Nat) : flipAns n ≠ flipAns (n + 1) := by
  unfold flipAns
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h' : (n + 1) % 2 = 1 := by omega
    simp [h, h']
  · have h' : (n + 1) % 2 = 0 := by omega
    simp [h, h']

end PZFC.Records
