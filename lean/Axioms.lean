/-
  The core of PZF as a question universe (notes/17).  Mathlib-free.

  Individuals; a relation `ε x q` — "x answers yes to question q"; questions
  are individuals too (P4).  A *record* (a set) is an individual that occurs as
  an answer.  An *atom* is an individual that is not a question.

  1. Russell: the question "are you a record that does not answer yes to
     yourself?" can be asked, but it cannot be completed to a record.
  2. Atoms answer nothing, so answers cannot separate them: counting exceeds
     discerning (P2).  A two-atom universe shows this is consistent.
  3. Expansion: every extensional set structure expands to a question universe
     whose records are exactly the original sets, with membership unchanged.
     This is the semantic core of conservativity — adding questions creates no
     new sets.  (This part uses classical logic; see the axiom report.)
-/

namespace PZFC.Axioms

structure QU where
  I : Type
  ε : I → I → Prop
  isQ : I → Prop

namespace QU

variable (U : QU)

/-- A record: an individual that occurs as an answer. -/
def Rec (x : U.I) : Prop := ∃ q, U.ε x q

/-- An atom: an individual that is not a question. -/
def Atom (a : U.I) : Prop := ¬ U.isQ a

/-- P1: questions with the same yes-answers are the same question. -/
def Ext : Prop :=
  ∀ p q, U.isQ p → U.isQ q → (∀ x, U.ε x p ↔ U.ε x q) → p = q

/-- Atoms have no yes-answers. -/
def AtomsBare : Prop := ∀ a x, U.Atom a → ¬ U.ε x a

/-! ### 1. Russell -/

/-- The Russell question can be asked but not completed. -/
theorem russell_not_record (q : U.I)
    (hq : ∀ x, U.ε x q ↔ (U.Rec x ∧ ¬ U.ε x x)) : ¬ U.Rec q := by
  intro hrec
  have hn : ¬ U.ε q q := fun hqq => ((hq q).mp hqq).2 hqq
  exact hn ((hq q).mpr ⟨hrec, hn⟩)

/-- So not every question is a record: Frege's Basic Law V fails. -/
theorem not_all_questions_records (q : U.I) (hQ : U.isQ q)
    (hq : ∀ x, U.ε x q ↔ (U.Rec x ∧ ¬ U.ε x x)) :
    ¬ ∀ p, U.isQ p → U.Rec p :=
  fun h => U.russell_not_record q hq (h q hQ)

/-! ### 2. Atoms -/

theorem atoms_same_answers (h : U.AtomsBare) (a b : U.I) (ha : U.Atom a) (hb : U.Atom b) :
    ∀ x, U.ε x a ↔ U.ε x b :=
  fun x => ⟨fun hx => absurd hx (h a x ha), fun hx => absurd hx (h b x hb)⟩

/-- Two distinct atoms defeat identity-by-answers: counting exceeds discerning. -/
theorem answers_do_not_separate_atoms (h : U.AtomsBare) (a b : U.I)
    (ha : U.Atom a) (hb : U.Atom b) (hab : a ≠ b) :
    ¬ ∀ x y, (∀ z, U.ε z x ↔ U.ε z y) → x = y :=
  fun hext => hab (hext a b (U.atoms_same_answers h a b ha hb))

end QU

/-- A minimal universe: one question, two atoms, both answering yes to it. -/
def twoAtoms : QU where
  I := Option Bool
  ε := fun x q => q = none ∧ x ≠ none
  isQ := fun x => x = none

theorem twoAtoms_ext : twoAtoms.Ext := by
  intro p q hp hq _
  exact hp.trans hq.symm

theorem twoAtoms_bare : twoAtoms.AtomsBare := by
  intro a x ha hx
  exact ha hx.1

theorem twoAtoms_records (b : Bool) : twoAtoms.Rec (some b) :=
  ⟨none, rfl, Option.some_ne_none b⟩

theorem twoAtoms_counting_exceeds_discerning :
    ¬ ∀ x y : twoAtoms.I, (∀ z, twoAtoms.ε z x ↔ twoAtoms.ε z y) → x = y :=
  twoAtoms.answers_do_not_separate_atoms twoAtoms_bare (some true) (some false)
    (Option.some_ne_none true) (Option.some_ne_none false)
    (by decide : (some true : Option Bool) ≠ some false)

/-! ### 3. Expansion of a set structure -/

/-- A bare set structure: membership plus extensionality. -/
structure SetStr where
  S : Type
  mem : S → S → Prop
  ext : ∀ s t, (∀ u, mem u s ↔ mem u t) → s = t

namespace SetStr

variable (M : SetStr)

/-- Questions about sets that no set answers: the proper questions. -/
def ProperQ : Type := { P : M.S → Prop // ¬ ∃ t, ∀ u, P u ↔ M.mem u t }

def epsE : M.S ⊕ M.ProperQ → M.S ⊕ M.ProperQ → Prop
  | Sum.inl s, Sum.inl t => M.mem s t
  | Sum.inl s, Sum.inr P => P.val s
  | Sum.inr _, _ => False

/-- Individuals are the sets and the proper questions; every individual is a
    question; only sets can be answers. -/
def expand : QU := ⟨M.S ⊕ M.ProperQ, M.epsE, fun _ => True⟩

theorem expand_mem (s t : M.S) : M.expand.ε (Sum.inl s) (Sum.inl t) ↔ M.mem s t :=
  Iff.rfl

theorem expand_proper_not_record (P : M.ProperQ) : ¬ M.expand.Rec (Sum.inr P) :=
  fun ⟨_, h⟩ => h

/-- Every set is a record (classically: either `{s}` is a set, or it is a
    proper question; either way `s` answers yes to something). -/
theorem expand_set_record (s : M.S) : M.expand.Rec (Sum.inl s) := by
  cases Classical.em (∃ t, ∀ u, (u = s) ↔ M.mem u t) with
  | inl h =>
    obtain ⟨t, ht⟩ := h
    exact ⟨Sum.inl t, (ht s).mp rfl⟩
  | inr h => exact ⟨Sum.inr ⟨fun u => u = s, h⟩, rfl⟩

/-- The expansion satisfies extensionality for questions. -/
theorem expand_ext : M.expand.Ext := by
  intro p q _ _ h
  cases p with
  | inl s =>
    cases q with
    | inl t => exact congrArg Sum.inl (M.ext s t (fun u => h (Sum.inl u)))
    | inr P => exact absurd ⟨s, fun u => (h (Sum.inl u)).symm⟩ P.property
  | inr P =>
    cases q with
    | inl t => exact absurd ⟨t, fun u => h (Sum.inl u)⟩ P.property
    | inr Q =>
      exact congrArg Sum.inr (Subtype.ext (funext fun u => propext (h (Sum.inl u))))

/-- The Russell predicate is realised by no set … -/
theorem russell_not_setlike : ¬ ∃ t, ∀ u, (¬ M.mem u u) ↔ M.mem u t := by
  rintro ⟨t, ht⟩
  have h := ht t
  have hn : ¬ M.mem t t := fun hm => (h.mpr hm) hm
  exact hn (h.mp hn)

/-- … so in the expansion it is a proper question: asked, never completed. -/
def russellQ : M.expand.I := Sum.inr ⟨fun u => ¬ M.mem u u, M.russell_not_setlike⟩

theorem russellQ_asks (s : M.S) : M.expand.ε (Sum.inl s) M.russellQ ↔ ¬ M.mem s s :=
  Iff.rfl

theorem russellQ_not_record : ¬ M.expand.Rec M.russellQ :=
  M.expand_proper_not_record _

end SetStr

end PZFC.Axioms
