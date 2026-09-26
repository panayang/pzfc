/-
  Truth over contexts (notes/26).  Mathlib-free.

  Contexts form a preorder of refinement: `le c d` says that `d` refines `c`
  (it has settled at least as much).  A proposition over the contexts is what
  holds in each context, stable under refinement; implication and negation look
  at every refinement.  This is the logic of the situations of notes/25, read
  in the plainest setting.

  - Where no context can be properly refined, internal excluded middle is the
    metatheory's own: a single context — the classical origin — is exactly as
    sharp as the language it is written in (`sharp_of_no_refinement`).
  - Conversely, if excluded middle holds internally everywhere, no refinement
    is proper (`no_refinement_of_sharp`).
  - With one context refining another, excluded middle fails in the coarse one
    (`two_contexts_not_sharp`).
  - Yet it is never refuted: its double negation holds in every context of every
    structure (`not_not_sharp`) — the classical origin is present everywhere as
    a ¬¬-shadow.

  So the 0/1 of truth is not a property of truth itself but of the context
  structure: it holds exactly where every question is already settled.
-/

namespace PZFC.Contexts

/-- A structure of contexts: a preorder of refinement. -/
structure Ctx where
  C : Type
  le : C → C → Prop
  refl : ∀ c, le c c
  trans : ∀ {a b c}, le a b → le b c → le a c

/-- A proposition over the contexts: once it holds, it holds in every refinement. -/
structure LProp (K : Ctx) where
  holds : K.C → Prop
  mono : ∀ {c d}, K.le c d → holds c → holds d

variable {K : Ctx}

def LProp.or (P Q : LProp K) : LProp K :=
  ⟨fun c => P.holds c ∨ Q.holds c,
   fun h hc => hc.elim (fun hp => Or.inl (P.mono h hp)) (fun hq => Or.inr (Q.mono h hq))⟩

/-- Implication looks at every refinement. -/
def LProp.imp (P Q : LProp K) : LProp K :=
  ⟨fun c => ∀ d, K.le c d → P.holds d → Q.holds d,
   fun h hc d hd hp => hc d (K.trans h hd) hp⟩

def LProp.bot : LProp K := ⟨fun _ => False, fun _ h => h⟩

def LProp.not (P : LProp K) : LProp K := P.imp LProp.bot

/-- **Where no context can be properly refined, internal excluded middle is the
    metatheory's own.**  A single context, in particular, is exactly as sharp as
    the language it is written in. -/
theorem sharp_of_no_refinement (hK : ∀ c d, K.le c d → K.le d c) (P : LProp K) (c : K.C) :
    (P.or P.not).holds c ↔ (P.holds c ∨ ¬ P.holds c) := by
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (fun hp => h c (K.refl c) hp)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (fun d hd hp => h (P.mono (hK c d hd) hp))

/-- **Sharpness is the absence of proper refinement**: if excluded middle holds
    internally for every proposition in every context, every refinement can be
    undone. -/
theorem no_refinement_of_sharp (h : ∀ (P : LProp K) c, (P.or P.not).holds c) :
    ∀ c d, K.le c d → K.le d c := by
  intro c d hcd
  let P : LProp K := ⟨fun e => K.le d e, fun h1 h2 => K.trans h2 h1⟩
  rcases h P c with hP | hP
  · exact hP
  · exact absurd (K.refl d) (hP d hcd)

theorem true_ne_false' : (true : Bool) ≠ false := by decide

theorem false_ne_true' : (false : Bool) ≠ true := by decide

/-- Two contexts, `true` refining `false`. -/
def twoCtx : Ctx where
  C := Bool
  le := fun a b => a = false ∨ b = true
  refl := fun a => match a with
    | false => Or.inl rfl
    | true => Or.inr rfl
  trans := fun hab hbc => match hab, hbc with
    | Or.inl ha, _ => Or.inl ha
    | Or.inr hb, Or.inl hb' => absurd (hb.symm.trans hb') (by decide)
    | Or.inr _, Or.inr hc => Or.inr hc

/-- "We are in the refined context." -/
def refined : LProp twoCtx :=
  ⟨fun c => c = true, fun h hc => h.elim (fun hf => absurd (hc.symm.trans hf) true_ne_false') id⟩

/-- **With a refinable context, excluded middle fails**: in the coarse context it
    is not yet settled whether we are in the refined one. -/
theorem two_contexts_not_sharp : ¬ (refined.or refined.not).holds false := by
  rintro (h | h)
  · exact absurd h false_ne_true'
  · exact h true (Or.inl rfl) rfl

/-- **Excluded middle is never refuted**: its double negation holds in every
    context — the classical origin is present everywhere as a ¬¬-shadow. -/
theorem not_not_sharp (P : LProp K) (c : K.C) : (P.or P.not).not.not.holds c := by
  intro d _ hnd
  apply hnd d (K.refl d)
  exact Or.inr (fun e hde hp => hnd e hde (Or.inl hp))

end PZFC.Contexts
