/-
  Partial exchangeability (notes/65).  Mathlib-free.

  Letters come in classes.  Letters of different classes commute; letters of the
  same class do not.  Two words are in the same trace when one can be turned into
  the other by swapping adjacent letters of different classes.

  §1  swaps, traces, the stream of a class
  §2  the core theorem: two words are in the same trace exactly when they have the
      same stream in every class.  A trace is a tuple of class streams; only the
      interleaving is free
  §3  a weight unchanged by such swaps depends only on the streams
  §4  a word is its schedule (the sequence of classes) together with its streams; any
      schedule with the right number of each class can read given streams.  So a
      weight unchanged by swaps gives, for fixed streams, the same weight to every
      schedule: given the streams, the schedule is exchangeable
  §5  when the asker chooses the questions: the PR box.  Its two classes commute (either
      order gives the same table), but it is not a mixture of hidden records, one
      for each class.  Every list of shared records wins at most 3 of the 4 contexts
      per record; the PR box wins all 4
-/

namespace PZFC.Exch

variable {L C : Type} (cls : L → C)

/-! ## 1. Swaps, traces, streams -/

/-- One swap of adjacent letters of different classes. -/
def Step (w₁ w₂ : List L) : Prop :=
  ∃ h t x y, cls x ≠ cls y ∧ w₁ = h ++ x :: y :: t ∧ w₂ = h ++ y :: x :: t

/-- The same trace: connected by such swaps. -/
inductive TEq : List L → List L → Prop
  | refl (w : List L) : TEq w w
  | step {w₁ w₂ w₃ : List L} : Step cls w₁ w₂ → TEq w₂ w₃ → TEq w₁ w₃

variable {cls}

theorem TEq.trans {w₁ w₂ w₃ : List L} (h₁ : TEq cls w₁ w₂) (h₂ : TEq cls w₂ w₃) :
    TEq cls w₁ w₃ := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact TEq.step hs (ih h₂)

theorem Step.cons (a : L) {w₁ w₂ : List L} (hs : Step cls w₁ w₂) :
    Step cls (a :: w₁) (a :: w₂) := by
  obtain ⟨h, t, x, y, hxy, rfl, rfl⟩ := hs
  exact ⟨a :: h, t, x, y, hxy, rfl, rfl⟩

theorem TEq.cons (a : L) {w₁ w₂ : List L} (h : TEq cls w₁ w₂) : TEq cls (a :: w₁) (a :: w₂) := by
  induction h with
  | refl => exact TEq.refl _
  | step hs _ ih => exact TEq.step (hs.cons a) ih

/-- A letter moves to the front past letters of other classes. -/
theorem move_front (x : L) (s : List L) :
    ∀ u : List L, (∀ z ∈ u, cls z ≠ cls x) → TEq cls (u ++ x :: s) (x :: (u ++ s))
  | [], _ => TEq.refl _
  | z :: u, hu => by
    have ih := move_front x s u (fun z' hz' => hu z' (List.mem_cons_of_mem z hz'))
    have h1 : TEq cls (z :: (u ++ x :: s)) (z :: x :: (u ++ s)) := ih.cons z
    have h2 : Step cls (z :: x :: (u ++ s)) (x :: z :: (u ++ s)) :=
      ⟨[], u ++ s, z, x, hu z List.mem_cons_self, rfl, rfl⟩
    exact h1.trans (TEq.step h2 (TEq.refl _))

variable [DecidableEq C]

variable (cls) in
/-- The stream of one class: the letters of that class, in order. -/
def proj (c : C) (w : List L) : List L := w.filter (fun x => decide (cls x = c))

theorem proj_cons_self (x : L) (w : List L) : proj cls (cls x) (x :: w) = x :: proj cls (cls x) w := by
  simp [proj]

theorem proj_cons_of_ne {x : L} {d : C} (h : cls x ≠ d) (w : List L) :
    proj cls d (x :: w) = proj cls d w := by
  simp [proj, h]

theorem proj_append (c : C) (u v : List L) : proj cls c (u ++ v) = proj cls c u ++ proj cls c v := by
  simp [proj, List.filter_append]

theorem proj_step {w₁ w₂ : List L} (hs : Step cls w₁ w₂) (c : C) :
    proj cls c w₁ = proj cls c w₂ := by
  obtain ⟨h, t, x, y, hxy, rfl, rfl⟩ := hs
  simp only [proj, List.filter_append, List.filter_cons]
  by_cases hx : cls x = c <;> by_cases hy : cls y = c
  · exact absurd (hx.trans hy.symm) hxy
  · simp [hx, hy]
  · simp [hx, hy]
  · simp [hx, hy]

/-! ## 2. The core theorem -/

/-- **Same trace ⟹ same streams.** -/
theorem proj_teq {w₁ w₂ : List L} (h : TEq cls w₁ w₂) (c : C) :
    proj cls c w₁ = proj cls c w₂ := by
  induction h with
  | refl => rfl
  | step hs _ ih => exact (proj_step hs c).trans ih

/-- The first letter of a class, and what comes before and after it. -/
theorem split_first (c : C) :
    ∀ w : List L, proj cls c w ≠ [] →
      ∃ u x s, w = u ++ x :: s ∧ cls x = c ∧ (∀ z ∈ u, cls z ≠ c)
  | [], h => absurd rfl h
  | a :: w, h => by
    by_cases ha : cls a = c
    · exact ⟨[], a, w, rfl, ha, fun z hz => absurd hz List.not_mem_nil⟩
    · have hw : proj cls c w ≠ [] := by
        intro h0; apply h; rw [proj_cons_of_ne ha]; exact h0
      obtain ⟨u, x, s, rfl, hx, hu⟩ := split_first c w hw
      refine ⟨a :: u, x, s, rfl, hx, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ha
      · exact hu z hz

theorem proj_nil_of_free (c : C) : ∀ u : List L, (∀ z ∈ u, cls z ≠ c) → proj cls c u = []
  | [], _ => rfl
  | z :: u, hu => by
    rw [proj_cons_of_ne (hu z List.mem_cons_self)]
    exact proj_nil_of_free c u (fun z' hz' => hu z' (List.mem_cons_of_mem z hz'))

/-- **Same streams ⟹ same trace.** -/
theorem teq_of_proj : ∀ (w' w : List L), (∀ c, proj cls c w = proj cls c w') → TEq cls w w'
  | [], w, h => by
    cases w with
    | nil => exact TEq.refl _
    | cons a w =>
      have := h (cls a)
      rw [proj_cons_self] at this
      simp [proj] at this
  | x :: v', w, h => by
    have hc := h (cls x)
    rw [proj_cons_self] at hc
    obtain ⟨u, x', s, rfl, hxc, hu⟩ := split_first (cls x) w (by rw [hc]; simp)
    rw [proj_append, proj_nil_of_free _ u hu, List.nil_append, ← hxc, proj_cons_self] at hc
    obtain ⟨hxx, hcs⟩ := List.cons.inj hc
    subst x'
    have hmove : TEq cls (u ++ x :: s) (x :: (u ++ s)) := move_front x s u hu
    have hrest : ∀ d, proj cls d (u ++ s) = proj cls d v' := by
      intro d
      by_cases hd : cls x = d
      · subst hd
        rw [proj_append, proj_nil_of_free _ u hu, List.nil_append]
        exact hcs
      · have h1 := h d
        rw [proj_append, proj_cons_of_ne hd, proj_cons_of_ne hd, ← proj_append] at h1
        exact h1
    exact hmove.trans ((teq_of_proj v' (u ++ s) hrest).cons x)

/-- **The core theorem**: two words are in the same trace exactly when they have the same
    stream in every class. -/
theorem teq_iff_proj (w w' : List L) : TEq cls w w' ↔ ∀ c, proj cls c w = proj cls c w' :=
  ⟨fun h c => proj_teq h c, teq_of_proj w' w⟩

/-! ## 3. Weights unchanged by swaps -/

/-- A weight on words unchanged by swaps of different classes depends only on the streams. -/
theorem weight_depends_on_streams {X : Type} (F : List L → X)
    (hF : ∀ w₁ w₂, Step cls w₁ w₂ → F w₁ = F w₂) (w w' : List L)
    (h : ∀ c, proj cls c w = proj cls c w') : F w = F w' := by
  have ht := teq_of_proj w' w h
  clear h
  induction ht with
  | refl => rfl
  | step hs _ ih => exact (hF _ _ hs).trans ih

/-- Conversely, any weight that depends only on the streams is unchanged by swaps. -/
theorem streams_weight_invariant {X : Type} (Φ : (C → List L) → X) (w₁ w₂ : List L)
    (hs : Step cls w₁ w₂) : Φ (fun c => proj cls c w₁) = Φ (fun c => proj cls c w₂) := by
  have : (fun c => proj cls c w₁) = (fun c => proj cls c w₂) := funext (proj_step hs)
  rw [this]

/-- **A weight is unchanged by swaps of different classes exactly when it depends only on the
    streams.**  With letters taken to be (question, answer) pairs, classed by the question, this
    says: the answers can be read in any interleaving of the classes exactly when the law of the
    answers of each class depends only on the questions of that class. -/
theorem stepInvariant_iff {X : Type} (F : List L → X) :
    (∀ w₁ w₂, Step cls w₁ w₂ → F w₁ = F w₂) ↔
      ∀ w w', (∀ c, proj cls c w = proj cls c w') → F w = F w' := by
  constructor
  · exact fun hF w w' h => weight_depends_on_streams F hF w w' h
  · intro h w₁ w₂ hs
    exact h w₁ w₂ (proj_step hs)

/-! ## 4. A word is its schedule and its streams -/

/-- **A word is determined by its schedule and its streams.** -/
theorem word_determined : ∀ (w w' : List L), w.map cls = w'.map cls →
    (∀ c, proj cls c w = proj cls c w') → w = w'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: v, x' :: v', h, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hc, hv⟩ := h
    have h1 := hp (cls x)
    rw [proj_cons_self, hc, proj_cons_self] at h1
    obtain ⟨rfl, ht⟩ := List.cons.inj h1
    congr 1
    apply word_determined v v' hv
    intro d
    by_cases hd : cls x = d
    · subst hd; exact ht
    · have := hp d
      rwa [proj_cons_of_ne hd, proj_cons_of_ne hd] at this

/-- How many times the class `c` occurs in a schedule. -/
def occ (c : C) (y : List C) : Nat := (y.filter (fun d => decide (d = c))).length

/-- Read the streams in the order of the schedule: at each step, the next unread letter of the
    named class. -/
def weave : List C → (C → List L) → List L
  | [], _ => []
  | c :: y, s =>
    match s c with
    | [] => []
    | x :: rest => x :: weave y (fun d => if d = c then rest else s d)

/-- **Any schedule with the right number of each class reads the streams back.** -/
theorem weave_spec : ∀ (y : List C) (s : C → List L),
    (∀ c, (s c).length = occ c y) → (∀ c, ∀ x ∈ s c, cls x = c) →
    (weave y s).map cls = y ∧ ∀ c, proj cls c (weave y s) = s c
  | [], s, hl, _ => by
    have hs : ∀ c, s c = [] := fun c => List.eq_nil_of_length_eq_zero (hl c)
    refine ⟨rfl, fun c => ?_⟩
    rw [hs c]; rfl
  | c :: y, s, hl, hcls => by
    have hlc := hl c
    simp only [occ, List.filter_cons, decide_true, if_true, List.length_cons] at hlc
    obtain ⟨x, rest, hsc⟩ : ∃ x rest, s c = x :: rest := by
      cases h : s c with
      | nil => rw [h, List.length_nil] at hlc; exact absurd hlc.symm (Nat.succ_ne_zero _)
      | cons x rest => exact ⟨x, rest, rfl⟩
    have hxc : cls x = c := hcls c x (by rw [hsc]; exact List.mem_cons_self)
    have hl' : ∀ d, ((fun d => if d = c then rest else s d) d).length = occ d y := by
      intro d
      by_cases hd : d = c
      · subst hd
        rw [hsc] at hlc
        simp only [if_true]
        simpa [occ] using hlc
      · have h2 := hl d
        have hcd : ¬ (c = d) := fun h => hd h.symm
        simp only [occ, List.filter_cons, hcd, decide_false] at h2
        simpa [hd, occ] using h2
    have hcls' : ∀ d, ∀ z ∈ (fun d => if d = c then rest else s d) d, cls z = d := by
      intro d z hz
      by_cases hd : d = c
      · subst hd
        simp only [if_true] at hz
        exact hcls d z (by rw [hsc]; exact List.mem_cons_of_mem x hz)
      · simp only [hd, if_false] at hz
        exact hcls d z hz
    obtain ⟨ih1, ih2⟩ := weave_spec y _ hl' hcls'
    have hw : weave (c :: y) s = x :: weave y (fun d => if d = c then rest else s d) := by
      simp only [weave, hsc]
    rw [hw]
    refine ⟨by simp [ih1, hxc], fun d => ?_⟩
    by_cases hd : cls x = d
    · subst hd
      rw [proj_cons_self, ih2]
      simp [hxc, hsc]
    · rw [proj_cons_of_ne hd, ih2]
      have hdc : ¬ (d = c) := fun h => hd (hxc.trans h.symm)
      simp [hdc]

theorem length_proj (c : C) (w : List L) : (proj cls c w).length = occ c (w.map cls) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    by_cases h : cls x = c
    · rw [← h, proj_cons_self]
      simp only [occ, List.map_cons, List.filter_cons, decide_true, if_true, List.length_cons]
      rw [h, ih]; rfl
    · rw [proj_cons_of_ne h]
      simp only [occ, List.map_cons, List.filter_cons, h, decide_false]
      exact ih

/-- **Every word is its schedule reading its streams.** -/
theorem weave_self (w : List L) : weave (w.map cls) (fun c => proj cls c w) = w := by
  have hcls : ∀ c, ∀ x ∈ proj cls c w, cls x = c := by
    intro c x hx
    simp only [proj, List.mem_filter, decide_eq_true_eq] at hx
    exact hx.2
  obtain ⟨h1, h2⟩ := weave_spec (w.map cls) (fun c => proj cls c w) (fun c => length_proj c w) hcls
  exact word_determined _ _ h1 h2

/-- **Given the streams, every schedule has the same weight.**  Two schedules with the same
    number of each class, reading the same streams, give words of the same weight: under a weight
    unchanged by swaps, the schedule is exchangeable given the streams. -/
theorem weight_schedule_free {X : Type} (F : List L → X)
    (hF : ∀ w₁ w₂, Step cls w₁ w₂ → F w₁ = F w₂) (y y' : List C) (s : C → List L)
    (hl : ∀ c, (s c).length = occ c y) (hl' : ∀ c, (s c).length = occ c y')
    (hcls : ∀ c, ∀ x ∈ s c, cls x = c) : F (weave y s) = F (weave y' s) :=
  weight_depends_on_streams F hF _ _
    (fun c => ((weave_spec y s hl hcls).2 c).trans ((weave_spec y' s hl' hcls).2 c).symm)

/-! ## 5. When the asker chooses: the PR box -/

/-- The PR box.  Alice is asked `x`, Bob is asked `y`; the answers `(a, b)` differ exactly when
    both questions are `true`.  Weight 1 for each allowed pair of answers, out of 2. -/
def pr (x y a b : Bool) : Nat := if (a != b) = (x && y) then 1 else 0

/-- Alice's answer has the same law whatever Bob is asked … -/
theorem pr_alice (x y y' a : Bool) :
    pr x y a false + pr x y a true = pr x y' a false + pr x y' a true := by
  cases x <;> cases y <;> cases y' <;> cases a <;> decide

/-- … and Bob's answer has the same law whatever Alice is asked.  So the table can be read in
    either order: asking Alice first or Bob first gives the same weights.  The two classes
    commute. -/
theorem pr_bob (x x' y b : Bool) :
    pr x y false b + pr x y true b = pr x' y false b + pr x' y true b := by
  cases x <;> cases x' <;> cases y <;> cases b <;> decide

/-- A hidden record for each class: Alice's answers to her two questions, Bob's to his. -/
structure Rec where
  a0 : Bool
  a1 : Bool
  b0 : Bool
  b1 : Bool

def Rec.alice (r : Rec) (x : Bool) : Bool := if x then r.a1 else r.a0
def Rec.bob (r : Rec) (y : Bool) : Bool := if y then r.b1 else r.b0

/-- The weight of answers `(a, b)` to questions `(x, y)` in a mixture of hidden records: the
    number of records that give those answers. -/
def mixW (rs : List Rec) (x y a b : Bool) : Nat :=
  (rs.filter (fun r => r.alice x == a && r.bob y == b)).length

/-- The weight of the answers the PR box allows, summed over the four contexts. -/
def winTotal (rs : List Rec) : Nat :=
  (mixW rs false false false false + mixW rs false false true true) +
  (mixW rs false true false false + mixW rs false true true true) +
  (mixW rs true false false false + mixW rs true false true true) +
  (mixW rs true true false true + mixW rs true true true false)

/-- **Shared records win at most 3 of the 4 contexts each.**  Whatever the list of records — a
    mixture of hidden records, or a table of trials in which each variable has one value per
    trial — the allowed answers occur at most 3 times per record. -/
theorem shared_records_chsh (rs : List Rec) : winTotal rs ≤ 3 * rs.length := by
  induction rs with
  | nil => decide
  | cons r rs ih =>
    obtain ⟨a0, a1, b0, b1⟩ := r
    cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;>
      simp [winTotal, mixW, Rec.alice, Rec.bob] at ih ⊢ <;> omega

/-- In one context, every record gives exactly one pair of answers. -/
theorem length_eq_context (rs : List Rec) (x y : Bool) :
    rs.length = mixW rs x y false false + mixW rs x y false true +
      mixW rs x y true false + mixW rs x y true true := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨a0, a1, b0, b1⟩ := r
    cases x <;> cases y <;> cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;>
      simp [mixW, Rec.alice, Rec.bob] at ih ⊢ <;> omega

/-- **The PR box is not a mixture of hidden records.**  No list of records reproduces its
    weights, at any scale `k > 0`: the allowed answers would occur `8k` times among `2k` records,
    more than 3 per record. -/
theorem pr_not_mixture (rs : List Rec) (k : Nat) (hk : 0 < k)
    (h : ∀ x y a b, mixW rs x y a b = k * pr x y a b) : False := by
  have hwin : winTotal rs = 8 * k := by
    simp only [winTotal, h]
    simp [pr]
    omega
  have hlen : rs.length = 2 * k := by
    rw [length_eq_context rs false false, h, h, h, h]
    simp [pr]
    omega
  have := shared_records_chsh rs
  omega

end PZFC.Exch
