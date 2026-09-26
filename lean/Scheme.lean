/-
  GLU(π) as one scheme — stage 1 (notes/28).  Mathlib-free.

  A value structure says what an answer is worth, and how the answers of a
  family combine into "one of them".  A system is a value-valued relation
  "`z` is a child of `x`, to this extent"; a membership structure is a
  value-valued membership.  `SolvesV` says that the members of `f x` are, to
  the right extent, exactly the images of the children of `x`.  `GLUV` is the
  scheme: every allowed system has exactly one solution, and every object is
  the value of a solution of an allowed system.

  Stage 1 checks two claims of the design:
  - with sharp answers the scheme is the classical one (`gluV_sharp`); the
    classical definitions are restated here as in `Shapes.lean`, since the
    files are compiled one by one;
  - value as truth is context: with truth values that are the refinement-stable
    propositions over a preorder of contexts, a solution is exactly a solution
    in every context at once (`solvesV_truth_iff`).
-/

namespace PZFC.Scheme

universe u

/-- **What an answer is worth.**  `W` are the values; `agg` gives the value of
    "one of the family": for sharp answers, *some* member; for truth values, the
    join; for weights, the sum. -/
structure Val where
  W : Type
  agg : {ι : Type} → (ι → W) → W

/-- `f` solves the system `R` in the membership structure `E`: the members of
    `f x` are, to the right extent, the images of the children of `x`. -/
def SolvesV (V : Val) {A : Type} {B : Type u} (R : A → A → V.W) (E : B → B → V.W)
    (f : A → B) : Prop :=
  ∀ x b, E b (f x) = V.agg (fun z : {z : A // f z = b} => R z.1 x)

/-- **GLU(π)** for a value structure and a shape `ok`: every allowed system has
    exactly one solution, and every object is the value of a solution of an
    allowed system. -/
def GLUV (V : Val) {B : Type u} (ok : ∀ {A : Type}, (A → A → V.W) → Prop)
    (E : B → B → V.W) : Prop :=
  (∀ (A : Type) (R : A → A → V.W), ok R →
    (∃ f : A → B, SolvesV V R E f) ∧
    ∀ f g : A → B, SolvesV V R E f → SolvesV V R E g → ∀ x, f x = g x) ∧
  ∀ b : B, ∃ (A : Type) (R : A → A → V.W) (f : A → B) (x : A),
    ok R ∧ SolvesV V R E f ∧ f x = b

/-! ## Sharp answers: the classical instance -/

/-- Sharp answers: a proposition; "one of the family" is "some member". -/
def sharp : Val := ⟨Prop, fun f => ∃ i, f i⟩

/-- The classical notion of solution, as `Shapes.Solves`. -/
def Solves {A : Type} {B : Type u} (R : A → A → Prop) (E : B → B → Prop) (f : A → B) : Prop :=
  ∀ x b, E b (f x) ↔ ∃ z, R z x ∧ f z = b

/-- The classical scheme with a shape parameter, as `Shapes.GLUShape`. -/
def GLUShape {B : Type u} (ok : ∀ {A : Type}, (A → A → Prop) → Prop) (E : B → B → Prop) :
    Prop :=
  (∀ (A : Type) (R : A → A → Prop), ok R →
    (∃ f : A → B, Solves R E f) ∧
    ∀ f g : A → B, Solves R E f → Solves R E g → ∀ x, f x = g x) ∧
  ∀ b : B, ∃ (A : Type) (R : A → A → Prop) (f : A → B) (x : A),
    ok R ∧ Solves R E f ∧ f x = b

theorem solvesV_sharp {A : Type} {B : Type u} (R : A → A → Prop) (E : B → B → Prop)
    (f : A → B) : SolvesV sharp R E f ↔ Solves R E f := by
  constructor
  · intro h x b
    exact (Iff.of_eq (h x b)).trans
      ⟨fun ⟨z, hz⟩ => ⟨z.1, hz, z.2⟩, fun ⟨z, hz, hfz⟩ => ⟨⟨z, hfz⟩, hz⟩⟩
  · intro h x b
    apply propext
    exact (h x b).trans ⟨fun ⟨z, hz, hfz⟩ => ⟨⟨z, hfz⟩, hz⟩, fun ⟨z, hz⟩ => ⟨z.1, hz, z.2⟩⟩

/-- **With sharp answers, the scheme is the classical one.** -/
theorem gluV_sharp {B : Type u} (ok : ∀ {A : Type}, (A → A → Prop) → Prop)
    (E : B → B → Prop) : GLUV sharp ok E ↔ GLUShape ok E := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun A R hR => ?_, fun b => ?_⟩
    · obtain ⟨⟨f, hf⟩, hu⟩ := h1 A R hR
      exact ⟨⟨f, (solvesV_sharp R E f).1 hf⟩, fun f g hf hg =>
        hu f g ((solvesV_sharp R E f).2 hf) ((solvesV_sharp R E g).2 hg)⟩
    · obtain ⟨A, R, f, x, hR, hf, hx⟩ := h2 b
      exact ⟨A, R, f, x, hR, (solvesV_sharp R E f).1 hf, hx⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun A R hR => ?_, fun b => ?_⟩
    · obtain ⟨⟨f, hf⟩, hu⟩ := h1 A R hR
      exact ⟨⟨f, (solvesV_sharp R E f).2 hf⟩, fun f g hf hg =>
        hu f g ((solvesV_sharp R E f).1 hf) ((solvesV_sharp R E g).1 hg)⟩
    · obtain ⟨A, R, f, x, hR, hf, hx⟩ := h2 b
      exact ⟨A, R, f, x, hR, (solvesV_sharp R E f).2 hf, hx⟩

/-! ## Value as truth is context -/

/-- A preorder of contexts: `le c d` says that `d` refines `c`. -/
structure Ctx where
  C : Type
  le : C → C → Prop
  refl : ∀ c, le c c
  trans : ∀ {a b c}, le a b → le b c → le a c

/-- Truth values over contexts: the propositions stable under refinement.  "One of
    the family" holds in a context when some member of the family holds there. -/
def truthVal (K : Ctx) : Val where
  W := {p : K.C → Prop // ∀ {c d}, K.le c d → p c → p d}
  agg := fun f => ⟨fun c => ∃ i, (f i).1 c, fun h ⟨i, hi⟩ => ⟨i, (f i).2 h hi⟩⟩

/-- A solution in every context at once: in each context, the members of `f x`
    are exactly the images of the children of `x` there. -/
def SolvesK (K : Ctx) {A : Type} {B : Type u} (R : K.C → A → A → Prop)
    (E : K.C → B → B → Prop) (f : A → B) : Prop :=
  ∀ c x b, E c b (f x) ↔ ∃ z, R c z x ∧ f z = b

/-- **Value as truth is context.**  With truth values over a preorder of contexts,
    a solution is exactly a solution in every context: a graded truth value and a
    truth that varies over contexts are the same data. -/
theorem solvesV_truth_iff (K : Ctx) {A : Type} {B : Type u}
    (R : A → A → (truthVal K).W) (E : B → B → (truthVal K).W) (f : A → B) :
    SolvesV (truthVal K) R E f ↔
      SolvesK K (fun c z x => (R z x).1 c) (fun c b a => (E b a).1 c) f := by
  constructor
  · intro h c x b
    have e : (E b (f x)).1 c ↔ ∃ z : {z : A // f z = b}, (R z.1 x).1 c :=
      Iff.of_eq (congrArg (fun p => p.1 c) (h x b))
    refine e.trans ⟨?_, ?_⟩
    · rintro ⟨z, hz⟩
      exact ⟨z.1, hz, z.2⟩
    · rintro ⟨z, hz, hfz⟩
      exact ⟨⟨z, hfz⟩, hz⟩
  · intro h x b
    apply Subtype.ext
    funext c
    apply propext
    exact (h c x b).trans ⟨fun ⟨z, hz, hfz⟩ => ⟨⟨z, hfz⟩, hz⟩, fun ⟨z, hz⟩ => ⟨z.1, hz, z.2⟩⟩

/-! ## Maps between value structures: shadows of solutions are solutions -/

/-- A map of value structures: it respects "one of the family".  Its typical use
    is a shadow — forgetting part of what an answer says. -/
structure ValHom (V V' : Val) where
  φ : V.W → V'.W
  agg : ∀ {ι : Type} (f : ι → V.W), φ (V.agg f) = V'.agg (fun i => φ (f i))

/-- **Shadows of solutions are solutions**: a map of value structures carries every
    solution of a system to a solution of the shadow of the system. -/
theorem solvesV_map {V V' : Val} (h : ValHom V V') {A : Type} {B : Type u} (R : A → A → V.W)
    (E : B → B → V.W) (f : A → B) (hf : SolvesV V R E f) :
    SolvesV V' (fun z x => h.φ (R z x)) (fun b a => h.φ (E b a)) f := by
  intro x b
  show h.φ (E b (f x)) = V'.agg (fun z : {z : A // f z = b} => h.φ (R z.1 x))
  rw [hf x b]
  exact h.agg _

/-- Looking at one context is a map of value structures: truth over contexts has a
    sharp shadow in each context. -/
def evalAt (K : Ctx) (c : K.C) : ValHom (truthVal K) sharp :=
  ⟨fun p => p.1 c, fun _ => rfl⟩

/-- The single context. -/
def pointCtx : Ctx := ⟨Unit, fun _ _ => True, fun _ => trivial, fun _ _ => trivial⟩

/-- **The classical origin is the single context**: over one context, truth values
    solve exactly as sharp answers do. -/
theorem solvesV_point_iff {A : Type} {B : Type u}
    (R : A → A → (truthVal pointCtx).W) (E : B → B → (truthVal pointCtx).W) (f : A → B) :
    SolvesV (truthVal pointCtx) R E f ↔
      Solves (fun z x => (R z x).1 ()) (fun b a => (E b a).1 ()) f := by
  refine (solvesV_truth_iff pointCtx R E f).trans ⟨fun h x b => h () x b, fun h c x b => ?_⟩
  cases c
  exact h x b

end PZFC.Scheme
