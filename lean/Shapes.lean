/-
  The shape parameter (notes/23).  Mathlib-free.

  A graph is a system of membership equations: node `x` asks to be the set of
  the values of its children.  A solution — Aczel's *decoration* — sends each
  node to an element whose members are exactly the values of its children.
  On a well-founded graph the solution is computed by recursion; on a graph
  with cycles there is nothing to recurse on, and it can only be solved.

  §1  uniqueness on well-founded shapes follows from extensionality;
  §2  uniqueness on all shapes is exactly strong extensionality
      (bisimilar ⟹ equal);
  §3  on a well-founded structure the two coincide: extensionality is the
      well-founded restriction of strong extensionality;
  §4  two self-membered elements: extensional, yet a loop has two solutions;
  §5  existence on well-founded shapes, by recursion, with no choice; the
      solution is injective exactly when the graph is extensional (Mostowski);
  §6  a choice function on an extensionally identified index decides every
      proposition (Diaconescu);
  §7  the classical origin (notes/24): foundation is the clause "every element
      solves a well-founded system"; on a well-founded structure the four forms
      of uniqueness coincide; and unique solutions of well-founded systems follow
      from extensionality and replacement alone, with no choice;
  §8  the shape extension, constructed (notes/25): pointed graphs up to
      bisimilarity.  Identity there is bisimilarity, every system — of any
      shape — has exactly one solution, small families glue, `Ω = {Ω}` exists,
      and the well-founded trees of §5 sit inside, with equality and membership
      preserved and reflected.  No choice is used;
  §9  one scheme with a shape parameter (notes/27): GLU(S) says the objects are
      exactly the unique solutions of the allowed systems.  Its well-founded
      instance gives foundation and extensionality; the universe of §8 is its
      instance for all systems; and the two instances cannot share one
      membership relation — different shapes live in different kinds of object.
      Nor is there a shadow back: nothing keeping membership maps the universe of
      all shapes into a well-founded structure (notes/33).
-/

namespace PZFC.Shapes

universe u

/-- `f` solves the system `R` in the membership structure `E` (a decoration):
    the members of `f x` are exactly the values of the children of `x`. -/
def Solves {A : Type} {B : Type u} (R : A → A → Prop) (E : B → B → Prop) (f : A → B) : Prop :=
  ∀ x b, E b (f x) ↔ ∃ z, R z x ∧ f z = b

/-- Extensionality: elements with the same members are equal. -/
def Extensional {B : Type u} (E : B → B → Prop) : Prop :=
  ∀ b b', (∀ c, E c b ↔ E c b') → b = b'

/-- `S` is a bisimulation: related elements have members that match up to `S`. -/
def Bisim {B : Type u} (E : B → B → Prop) (S : B → B → Prop) : Prop :=
  ∀ b b', S b b' →
    (∀ c, E c b → ∃ c', E c' b' ∧ S c c') ∧ (∀ c', E c' b' → ∃ c, E c b ∧ S c c')

/-- Strong extensionality: bisimilar elements are equal. -/
def StronglyExtensional {B : Type u} (E : B → B → Prop) : Prop :=
  ∀ S, Bisim E S → ∀ b b', S b b' → b = b'

/-! ## 1. Well-founded shapes: extensionality suffices -/

theorem unique_of_wf {A B : Type} {R : A → A → Prop} {E : B → B → Prop}
    (hR : WellFounded R) (hE : Extensional E) {f g : A → B}
    (hf : Solves R E f) (hg : Solves R E g) (x : A) : f x = g x := by
  refine hR.induction (C := fun x => f x = g x) x ?_
  intro x ih
  apply hE
  intro c
  refine (hf x c).trans (Iff.trans ⟨?_, ?_⟩ (hg x c).symm)
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (ih z hz).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, ih z hz⟩

/-! ## 2. All shapes: uniqueness is exactly strong extensionality -/

theorem unique_of_strong {A : Type} {B : Type u} {R : A → A → Prop} {E : B → B → Prop}
    (hE : StronglyExtensional E) {f g : A → B}
    (hf : Solves R E f) (hg : Solves R E g) (x : A) : f x = g x := by
  refine hE (fun b b' => ∃ y, f y = b ∧ g y = b') ?_ (f x) (g x) ⟨x, rfl, rfl⟩
  rintro b b' ⟨y, rfl, rfl⟩
  constructor
  · intro c hc
    obtain ⟨z, hz, rfl⟩ := (hf y c).1 hc
    exact ⟨g z, (hg y (g z)).2 ⟨z, hz, rfl⟩, z, rfl, rfl⟩
  · intro c hc
    obtain ⟨z, hz, rfl⟩ := (hg y c).1 hc
    exact ⟨f z, (hf y (f z)).2 ⟨z, hz, rfl⟩, z, rfl, rfl⟩

/-- Conversely, if no system has two solutions, the structure is strongly
    extensional: a bisimulation is itself a system, solved by both projections. -/
theorem strong_of_unique {B : Type} {E : B → B → Prop}
    (h : ∀ (A : Type) (R : A → A → Prop) (f g : A → B),
      Solves R E f → Solves R E g → ∀ x, f x = g x) :
    StronglyExtensional E := by
  intro S hS b b' hbb'
  refine h {p : B × B // S p.1 p.2} (fun q p => E q.1.1 p.1.1 ∧ E q.1.2 p.1.2)
    (fun p => p.1.1) (fun p => p.1.2) ?_ ?_ ⟨(b, b'), hbb'⟩
  · intro p c
    constructor
    · intro hc
      obtain ⟨c', hc', hcc'⟩ := (hS p.1.1 p.1.2 p.2).1 c hc
      exact ⟨⟨(c, c'), hcc'⟩, ⟨hc, hc'⟩, rfl⟩
    · rintro ⟨q, ⟨hq, _⟩, rfl⟩
      exact hq
  · intro p c'
    constructor
    · intro hc'
      obtain ⟨c, hc, hcc'⟩ := (hS p.1.1 p.1.2 p.2).2 c' hc'
      exact ⟨⟨(c, c'), hcc'⟩, ⟨hc, hc'⟩, rfl⟩
    · rintro ⟨q, ⟨_, hq⟩, rfl⟩
      exact hq

/-! ## 3. The classical origin: on well-founded structures the two coincide -/

theorem strong_of_wf {B : Type} {E : B → B → Prop}
    (hwf : WellFounded E) (hE : Extensional E) : StronglyExtensional E := by
  intro S hS b
  refine hwf.induction (C := fun b => ∀ b', S b b' → b = b') b ?_
  intro b ih b' hbb'
  apply hE
  intro c
  constructor
  · intro hc
    obtain ⟨c', hc', hcc'⟩ := (hS b b' hbb').1 c hc
    rw [ih c hc c' hcc']
    exact hc'
  · intro hc
    obtain ⟨c0, hc0, hcc⟩ := (hS b b' hbb').2 c hc
    rw [← ih c0 hc0 c hcc]
    exact hc0

/-! ## 4. Cycles: extensionality no longer suffices -/

/-- Two self-membered elements, `true = {true}` and `false = {false}`. -/
def quine (c b : Bool) : Prop := c = b

theorem quine_extensional : Extensional quine :=
  fun b _ h => (h b).1 rfl

/-- The one-node loop, `x = {x}`. -/
def loop (_ _ : Unit) : Prop := True

theorem loop_solved (v : Bool) : Solves loop quine (fun _ => v) :=
  fun _ _ => ⟨fun h => ⟨(), trivial, Eq.symm h⟩, fun ⟨_, _, h⟩ => Eq.symm h⟩

/-- Extensional, yet the loop has two solutions: on a cyclic shape, uniqueness
    needs strong extensionality. -/
theorem quine_not_strong : ¬ StronglyExtensional quine := fun h =>
  absurd (unique_of_strong h (loop_solved true) (loop_solved false) ()) (by decide)

/-! ## 5. Existence on well-founded shapes: recursion, no choice -/

/-- Well-founded trees: Aczel's model of sets. -/
inductive Tree : Type 1
  | mk (α : Type) (sub : α → Tree)

namespace Tree

/-- Extensional equality of trees. -/
def Eqv : Tree → Tree → Prop
  | ⟨_, A⟩, ⟨_, B⟩ => (∀ a, ∃ b, Eqv (A a) (B b)) ∧ (∀ b, ∃ a, Eqv (A a) (B b))

/-- Membership up to extensional equality. -/
def Mem (t : Tree) : Tree → Prop
  | ⟨_, B⟩ => ∃ b, Eqv t (B b)

theorem Eqv.refl : ∀ t : Tree, Eqv t t
  | ⟨_, A⟩ => ⟨fun a => ⟨a, Eqv.refl (A a)⟩, fun a => ⟨a, Eqv.refl (A a)⟩⟩

end Tree

/-- One step: the set of the values of the children. -/
def step {A : Type} (R : A → A → Prop) (x : A) (rec : ∀ z, R z x → Tree) : Tree :=
  Tree.mk {z // R z x} (fun z => rec z.1 z.2)

/-- The solution of a well-founded system, by recursion. -/
noncomputable def solve {A : Type} {R : A → A → Prop} (hR : WellFounded R) : A → Tree :=
  hR.fix (step R)

theorem solve_eq {A : Type} {R : A → A → Prop} (hR : WellFounded R) (x : A) :
    solve hR x = Tree.mk {z // R z x} (fun z => solve hR z.1) :=
  hR.fix_eq (step R) x

/-- Every well-founded system is solved (up to extensional equality). -/
theorem solve_mem {A : Type} {R : A → A → Prop} (hR : WellFounded R) (x : A) (t : Tree) :
    Tree.Mem t (solve hR x) ↔ ∃ z, R z x ∧ Tree.Eqv t (solve hR z) := by
  rw [solve_eq hR x]
  exact ⟨fun ⟨z, h⟩ => ⟨z.1, z.2, h⟩, fun ⟨z, hz, h⟩ => ⟨⟨z, hz⟩, h⟩⟩

/-- On an extensional system the solution is injective: Mostowski's collapse. -/
theorem solve_injective {A : Type} {R : A → A → Prop} (hR : WellFounded R)
    (hext : Extensional R) (x y : A) (h : Tree.Eqv (solve hR x) (solve hR y)) : x = y := by
  revert y
  refine hR.induction (C := fun x => ∀ y, Tree.Eqv (solve hR x) (solve hR y) → x = y) x ?_
  intro x ih y h
  rw [solve_eq hR x, solve_eq hR y] at h
  obtain ⟨h1, h2⟩ := h
  apply hext
  intro z
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := h1 ⟨z, hz⟩
    rw [ih z hz w.1 hw]
    exact w.2
  · intro hz
    obtain ⟨w, hw⟩ := h2 ⟨z, hz⟩
    rw [← ih w.1 w.2 z hw]
    exact w.2

/-- … and nodes with the same children get the same value: injectivity is
    exactly extensionality of the system. -/
theorem solve_same_children {A : Type} {R : A → A → Prop} (hR : WellFounded R) (x y : A)
    (h : ∀ z, R z x ↔ R z y) : Tree.Eqv (solve hR x) (solve hR y) := by
  rw [solve_eq hR x, solve_eq hR y]
  exact ⟨fun a => ⟨⟨a.1, (h a.1).1 a.2⟩, Tree.Eqv.refl _⟩,
         fun b => ⟨⟨b.1, (h b.1).2 b.2⟩, Tree.Eqv.refl _⟩⟩

/-! ## 6. Choice on an extensional index forces sharpness (Diaconescu) -/

/-- A choice function on the inhabited subsets of `Bool` — a function of the
    subset, where subsets with the same members are equal (`propext`, `funext`)
    — decides every proposition. -/
theorem em_of_choice (ch : ∀ P : Bool → Prop, (∃ b, P b) → {b // P b}) (p : Prop) :
    p ∨ ¬p := by
  have key : ∀ (P Q : Bool → Prop) (hP : ∃ b, P b) (hQ : ∃ b, Q b), P = Q →
      (ch P hP).1 = (ch Q hQ).1 := by
    intro P Q hP hQ h
    subst h
    rfl
  have hU : ∃ b : Bool, b = true ∨ p := ⟨true, Or.inl rfl⟩
  have hV : ∃ b : Bool, b = false ∨ p := ⟨false, Or.inl rfl⟩
  cases (ch (fun b => b = true ∨ p) hU).2 with
  | inr hp => exact Or.inl hp
  | inl hu =>
    cases (ch (fun b => b = false ∨ p) hV).2 with
    | inr hp => exact Or.inl hp
    | inl hv =>
      refine Or.inr (fun hp => ?_)
      have hUV : (fun b : Bool => b = true ∨ p) = (fun b => b = false ∨ p) :=
        funext fun _ => propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩
      have h := key (fun b => b = true ∨ p) (fun b => b = false ∨ p) hU hV hUV
      rw [hu, hv] at h
      exact absurd h (by decide)

/-! ## 7. The classical origin: GLU at well-founded shapes -/

/-- Every structure solves its own membership graph. -/
theorem solves_self {B : Type} (E : B → B → Prop) : Solves E E (fun b => b) := by
  intro x b
  constructor
  · intro h
    exact ⟨b, h, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact hz

/-- **Foundation is a gluing clause.**  Membership is well-founded exactly when
    every element is the value of a solution of a well-founded system. -/
theorem wf_iff_solved {B : Type} (E : B → B → Prop) :
    WellFounded E ↔ ∀ b : B, ∃ (A : Type) (R : A → A → Prop) (f : A → B) (x : A),
      WellFounded R ∧ Solves R E f ∧ f x = b := by
  constructor
  · intro hwf b
    exact ⟨B, E, fun b => b, b, hwf, solves_self E, rfl⟩
  · intro h
    apply WellFounded.intro
    intro b
    obtain ⟨A, R, f, x, hR, hf, rfl⟩ := h b
    refine hR.induction (C := fun x => Acc E (f x)) x ?_
    intro x ih
    apply Acc.intro
    intro c hc
    obtain ⟨z, hz, rfl⟩ := (hf x c).1 hc
    exact ih z hz

/-- Strong extensionality includes extensionality. -/
theorem ext_of_strong {B : Type u} {E : B → B → Prop} (h : StronglyExtensional E) :
    Extensional E := by
  intro b b' hbb'
  refine h (fun x y => x = y ∨ (x = b ∧ y = b')) ?_ b b' (Or.inr ⟨rfl, rfl⟩)
  rintro x y (rfl | ⟨rfl, rfl⟩)
  · exact ⟨fun c hc => ⟨c, hc, Or.inl rfl⟩, fun c hc => ⟨c, hc, Or.inl rfl⟩⟩
  · exact ⟨fun c hc => ⟨c, (hbb' c).1 hc, Or.inl rfl⟩,
           fun c hc => ⟨c, (hbb' c).2 hc, Or.inl rfl⟩⟩

/-- The membership graph with one extra node, `none`, whose children are the
    members of `b`. -/
def withTop {B : Type} (E : B → B → Prop) (b : B) : Option B → Option B → Prop
  | some d, none => E d b
  | some d, some c => E d c
  | none, _ => False

/-- Send the extra node to `t` and every other node to itself. -/
def topAt {B : Type} (t : B) : Option B → B
  | none => t
  | some c => c

theorem withTop_wf {B : Type} {E : B → B → Prop} (hwf : WellFounded E) (b : B) :
    WellFounded (withTop E b) := by
  have hsome : ∀ c, Acc (withTop E b) (some c) := by
    intro c
    refine hwf.induction (C := fun c => Acc (withTop E b) (some c)) c ?_
    intro c ih
    apply Acc.intro
    intro y hy
    cases y with
    | none => exact False.elim hy
    | some d => exact ih d hy
  apply WellFounded.intro
  intro y
  cases y with
  | none =>
    apply Acc.intro
    intro y hy
    cases y with
    | none => exact False.elim hy
    | some d => exact hsome d
  | some c => exact hsome c

/-- On a well-founded structure, uniqueness of solutions for well-founded
    systems gives extensionality: two elements with the same members both solve
    the extra node of `withTop`. -/
theorem ext_of_unique_wf {B : Type} {E : B → B → Prop} (hwf : WellFounded E)
    (h : ∀ (A : Type) (R : A → A → Prop) (f g : A → B),
      WellFounded R → Solves R E f → Solves R E g → ∀ x, f x = g x) :
    Extensional E := by
  intro b b' hbb'
  have key : ∀ t : B, (∀ c, E c t ↔ E c b) → Solves (withTop E b) E (topAt t) := by
    intro t ht y c
    cases y with
    | none =>
      constructor
      · intro hc
        exact ⟨some c, (ht c).1 hc, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        cases z with
        | none => exact False.elim hz
        | some d => exact (ht d).2 hz
    | some x =>
      constructor
      · intro hc
        exact ⟨some c, hc, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        cases z with
        | none => exact False.elim hz
        | some d => exact hz
  exact h (Option B) (withTop E b) (topAt b) (topAt b') (withTop_wf hwf b)
    (key b (fun _ => Iff.rfl)) (key b' (fun c => (hbb' c).symm)) none

/-- **On the classical side identity is unambiguous.**  On a well-founded
    structure, extensionality is strong extensionality; with `unique_of_wf`,
    `ext_of_unique_wf`, `unique_of_strong` and `strong_of_unique`, the four forms
    of uniqueness coincide there. -/
theorem wf_ext_iff_strong {B : Type} {E : B → B → Prop} (hwf : WellFounded E) :
    Extensional E ↔ StronglyExtensional E :=
  ⟨strong_of_wf hwf, ext_of_strong⟩

/-- One step of the recursion, as a relation: `b` is a value at `x` when its
    members are exactly the values at the children of `x`. -/
def stepRel {A B : Type} (R : A → A → Prop) (E : B → B → Prop) (x : A)
    (rec : ∀ z, R z x → B → Prop) : B → Prop :=
  fun b => ∀ c, E c b ↔ ∃ z, ∃ h : R z x, rec z h c

/-- The value relation of a well-founded system, by recursion. -/
noncomputable def valRel {A B : Type} {R : A → A → Prop} (hR : WellFounded R)
    (E : B → B → Prop) : A → B → Prop :=
  hR.fix (stepRel R E)

/-- **Unique gluing is free.**  In an extensional structure where the values at
    the children of a node can be collected (replacement: the image of the
    children under a functional relation has a set), every well-founded system
    has exactly one solution, obtained by recursion — with no choice.  It comes
    as a functional relation; making it a function is unique choice, which
    Lean's `Prop` does not supply without an axiom, while in set theory it is
    free. -/
theorem recursion_solves {A B : Type} {R : A → A → Prop} {E : B → B → Prop}
    (hR : WellFounded R) (hE : Extensional E)
    (repl : ∀ (x : A) (F : A → B → Prop), (∀ z b b', F z b → F z b' → b = b') →
      ∃ b, ∀ c, E c b ↔ ∃ z, R z x ∧ F z c) :
    (∀ x, ∃ b, valRel hR E x b) ∧
    (∀ x b b', valRel hR E x b → valRel hR E x b' → b = b') ∧
    (∀ x b, valRel hR E x b → ∀ c, E c b ↔ ∃ z, R z x ∧ valRel hR E z c) := by
  have unfold : ∀ x b, valRel hR E x b ↔ ∀ c, E c b ↔ ∃ z, R z x ∧ valRel hR E z c := by
    intro x b
    have hx : valRel hR E x b ↔ ∀ c, E c b ↔ ∃ z, ∃ _ : R z x, valRel hR E z c := by
      rw [show valRel hR E x = stepRel R E x (fun z _ => valRel hR E z) from
        hR.fix_eq (stepRel R E) x]
      exact Iff.rfl
    refine hx.trans ⟨fun h c => (h c).trans ⟨?_, ?_⟩, fun h c => (h c).trans ⟨?_, ?_⟩⟩
    · rintro ⟨z, hz, hc⟩
      exact ⟨z, hz, hc⟩
    · rintro ⟨z, hz, hc⟩
      exact ⟨z, hz, hc⟩
    · rintro ⟨z, hz, hc⟩
      exact ⟨z, hz, hc⟩
    · rintro ⟨z, hz, hc⟩
      exact ⟨z, hz, hc⟩
  have func : ∀ x b b', valRel hR E x b → valRel hR E x b' → b = b' := by
    intro x b b' hb hb'
    apply hE
    intro c
    exact ((unfold x b).1 hb c).trans ((unfold x b').1 hb' c).symm
  refine ⟨fun x => ?_, func, fun x b hb => (unfold x b).1 hb⟩
  obtain ⟨b, hb⟩ := repl x (valRel hR E) func
  exact ⟨b, (unfold x b).2 hb⟩

/-! ## 8. The shape extension, constructed: pointed graphs up to bisimilarity -/

/-- A pointed graph: an object together with everything below it.  `R m n` says
    that `m` is a child (a member) of `n`. -/
structure PG where
  N : Type
  R : N → N → Prop
  pt : N

/-- The same graph, pointed at another node. -/
def PG.at (G : PG) (n : G.N) : PG := ⟨G.N, G.R, n⟩

/-- `S` is a bisimulation from `G` to `H`. -/
def PG.IsBisim (G H : PG) (S : G.N → H.N → Prop) : Prop :=
  ∀ n m, S n m →
    (∀ n', G.R n' n → ∃ m', H.R m' m ∧ S n' m') ∧
    (∀ m', H.R m' m → ∃ n', G.R n' n ∧ S n' m')

/-- Bisimilar pointed graphs. -/
def PG.Bis (G H : PG) : Prop := ∃ S, PG.IsBisim G H S ∧ S G.pt H.pt

theorem PG.bis_refl (G : PG) : PG.Bis G G := by
  refine ⟨fun n m => n = m, ?_, rfl⟩
  rintro n m rfl
  exact ⟨fun n' h => ⟨n', h, rfl⟩, fun m' h => ⟨m', h, rfl⟩⟩

theorem PG.bis_symm {G H : PG} (h : PG.Bis G H) : PG.Bis H G := by
  obtain ⟨S, hS, hpt⟩ := h
  refine ⟨fun m n => S n m, ?_, hpt⟩
  intro m n hmn
  obtain ⟨h1, h2⟩ := hS n m hmn
  exact ⟨h2, h1⟩

theorem PG.bis_trans {G H K : PG} (h1 : PG.Bis G H) (h2 : PG.Bis H K) : PG.Bis G K := by
  obtain ⟨S, hS, hs⟩ := h1
  obtain ⟨T, hT, ht⟩ := h2
  refine ⟨fun n k => ∃ m, S n m ∧ T m k, ?_, ⟨H.pt, hs, ht⟩⟩
  rintro n k ⟨m, hnm, hmk⟩
  obtain ⟨hS1, hS2⟩ := hS n m hnm
  obtain ⟨hT1, hT2⟩ := hT m k hmk
  constructor
  · intro n' hn'
    obtain ⟨m', hm', hnm'⟩ := hS1 n' hn'
    obtain ⟨k', hk', hmk'⟩ := hT1 m' hm'
    exact ⟨k', hk', m', hnm', hmk'⟩
  · intro k' hk'
    obtain ⟨m', hm', hmk'⟩ := hT2 k' hk'
    obtain ⟨n', hn', hnm'⟩ := hS2 m' hm'
    exact ⟨n', hn', m', hnm', hmk'⟩

instance PG.setoid : Setoid PG := ⟨PG.Bis, ⟨PG.bis_refl, PG.bis_symm, PG.bis_trans⟩⟩

/-- `G` is a member of `H`: bisimilar to `H` pointed at a child of its point. -/
def PG.Mem (G H : PG) : Prop := ∃ m, H.R m H.pt ∧ PG.Bis G (H.at m)

theorem PG.mem_congr {G G' H H' : PG} (hG : PG.Bis G G') (hH : PG.Bis H H') :
    PG.Mem G H → PG.Mem G' H' := by
  rintro ⟨m, hm, hGm⟩
  obtain ⟨T, hT, hpt⟩ := hH
  obtain ⟨m', hm', hmm'⟩ := (hT H.pt H'.pt hpt).1 m hm
  have hsub : PG.Bis (H.at m) (H'.at m') := ⟨T, hT, hmm'⟩
  exact ⟨m', hm', PG.bis_trans (PG.bis_symm hG) (PG.bis_trans hGm hsub)⟩

/-- The universe of the shape extension: pointed graphs up to bisimilarity. -/
def UA : Type 1 := Quotient PG.setoid

def UA.mk (G : PG) : UA := Quotient.mk PG.setoid G

/-- Membership in the shape extension. -/
def UA.Mem : UA → UA → Prop :=
  Quotient.lift₂ PG.Mem (fun _ _ _ _ hG hH =>
    propext ⟨PG.mem_congr hG hH, PG.mem_congr (PG.bis_symm hG) (PG.bis_symm hH)⟩)

theorem UA.mk_eq {G H : PG} (h : PG.Bis G H) : UA.mk G = UA.mk H := Quotient.sound h

theorem UA.bis_of_eq {G H : PG} (h : UA.mk G = UA.mk H) : PG.Bis G H := Quotient.exact h

/-- The solution of a system: node `x` goes to the system itself, pointed at `x`. -/
def UA.dec {A : Type} (R : A → A → Prop) (x : A) : UA := UA.mk ⟨A, R, x⟩

/-- **Every system has a solution — of any shape.** -/
theorem UA.dec_solves {A : Type} (R : A → A → Prop) : Solves R UA.Mem (UA.dec R) := by
  intro x q
  refine Quotient.ind (motive := fun q => UA.Mem q (UA.dec R x) ↔ ∃ z, R z x ∧ UA.dec R z = q)
    (fun G => ?_) q
  constructor
  · rintro ⟨z, hz, hG⟩
    exact ⟨z, hz, UA.mk_eq (PG.bis_symm hG)⟩
  · rintro ⟨z, hz, h⟩
    exact ⟨z, hz, PG.bis_symm (UA.bis_of_eq h)⟩

/-- **Identity in the shape extension is bisimilarity**: the universe is strongly
    extensional. -/
theorem UA.strong : StronglyExtensional UA.Mem := by
  intro S hS a b hab
  revert hab
  refine Quotient.ind (motive := fun a => S a b → a = b) (fun G => ?_) a
  refine Quotient.ind (motive := fun b => S (UA.mk G) b → UA.mk G = b) (fun H => ?_) b
  intro hGH
  apply UA.mk_eq
  refine ⟨fun n m => S (UA.mk (G.at n)) (UA.mk (H.at m)), ?_, hGH⟩
  intro n m hnm
  obtain ⟨h1, h2⟩ := hS _ _ hnm
  constructor
  · intro n' hn'
    have hmem : UA.Mem (UA.mk (G.at n')) (UA.mk (G.at n)) := ⟨n', hn', PG.bis_refl _⟩
    obtain ⟨c, hc, hsc⟩ := h1 _ hmem
    revert hc hsc
    refine Quotient.ind (motive := fun c => UA.Mem c (UA.mk (H.at m)) →
      S (UA.mk (G.at n')) c → ∃ m', H.R m' m ∧ S (UA.mk (G.at n')) (UA.mk (H.at m')))
      (fun K => ?_) c
    rintro ⟨m', hm', hK⟩ hsc
    refine ⟨m', hm', ?_⟩
    have e : Quotient.mk PG.setoid K = UA.mk (H.at m') := UA.mk_eq hK
    exact e ▸ hsc
  · intro m' hm'
    have hmem : UA.Mem (UA.mk (H.at m')) (UA.mk (H.at m)) := ⟨m', hm', PG.bis_refl _⟩
    obtain ⟨c, hc, hsc⟩ := h2 _ hmem
    revert hc hsc
    refine Quotient.ind (motive := fun c => UA.Mem c (UA.mk (G.at n)) →
      S c (UA.mk (H.at m')) → ∃ n', G.R n' n ∧ S (UA.mk (G.at n')) (UA.mk (H.at m')))
      (fun K => ?_) c
    rintro ⟨n', hn', hK⟩ hsc
    refine ⟨n', hn', ?_⟩
    have e : Quotient.mk PG.setoid K = UA.mk (G.at n') := UA.mk_eq hK
    exact e ▸ hsc

/-- **Anti-foundation, in the constructed universe**: every system has exactly one
    solution.  This is GLU₀ with "well-founded" deleted. -/
theorem UA.afa {A : Type} (R : A → A → Prop) :
    Solves R UA.Mem (UA.dec R) ∧ ∀ f : A → UA, Solves R UA.Mem f → ∀ x, f x = UA.dec R x :=
  ⟨UA.dec_solves R, fun _ hf x => unique_of_strong UA.strong hf (UA.dec_solves R) x⟩

/-- The solution of the loop `x = {x}`. -/
def UA.omega : UA := UA.dec loop ()

/-- `Ω ∈ Ω` — and, by `UA.afa`, it is the only solution of the loop. -/
theorem UA.omega_self : UA.Mem UA.omega UA.omega :=
  (UA.dec_solves loop () UA.omega).2 ⟨(), trivial, rfl⟩

/-- Two nodes of a disjoint union are related exactly when they lie in the same
    component and are related there. -/
def SigmaRel {α : Type} {P : α → Type} (r : ∀ a, P a → P a → Prop) :
    (Σ a, P a) → (Σ a, P a) → Prop
  | ⟨a, x⟩, ⟨b, y⟩ => ∃ h : a = b, r b (h ▸ x) y

/-- The disjoint union of a family of pointed graphs, under a new point whose
    children are the old points. -/
def PG.sum {α : Type} (G : α → PG) : PG where
  N := Option (Σ a, (G a).N)
  R := fun m n => match m, n with
    | some ⟨a, x⟩, none => x = (G a).pt
    | some p, some q => SigmaRel (fun a => (G a).R) p q
    | none, _ => False
  pt := none

/-- Inside the sum, each component looks exactly as it did on its own. -/
theorem PG.sum_at {α : Type} (G : α → PG) (a : α) (x : (G a).N) :
    PG.Bis ((PG.sum G).at (some ⟨a, x⟩)) ((G a).at x) := by
  refine ⟨fun m z => m = some ⟨a, z⟩, ?_, rfl⟩
  rintro m z rfl
  constructor
  · intro m' hm'
    cases m' with
    | none => exact False.elim hm'
    | some p =>
      obtain ⟨b, y⟩ := p
      obtain ⟨h, hr⟩ := hm'
      subst h
      exact ⟨y, hr, rfl⟩
  · intro z' hz'
    exact ⟨some ⟨a, z'⟩, ⟨rfl, hz'⟩, rfl⟩

/-- **Small families glue** in the shape extension: the members of the sum are
    exactly the given graphs. -/
theorem UA.mem_sum {α : Type} (G : α → PG) (q : UA) :
    UA.Mem q (UA.mk (PG.sum G)) ↔ ∃ a, UA.mk (G a) = q := by
  refine Quotient.ind (motive := fun q => UA.Mem q (UA.mk (PG.sum G)) ↔ ∃ a, UA.mk (G a) = q)
    (fun K => ?_) q
  constructor
  · rintro ⟨m, hm, hK⟩
    cases m with
    | none => exact False.elim hm
    | some p =>
      obtain ⟨a, x⟩ := p
      have hx : x = (G a).pt := hm
      subst hx
      exact ⟨a, UA.mk_eq (PG.bis_symm (PG.bis_trans hK (PG.sum_at G a (G a).pt)))⟩
  · rintro ⟨a, h⟩
    refine ⟨some ⟨a, (G a).pt⟩, rfl, ?_⟩
    exact PG.bis_trans (PG.bis_symm (UA.bis_of_eq h)) (PG.bis_symm (PG.sum_at G a (G a).pt))

/-- The canonical graph of a well-founded tree. -/
def treePG : Tree → PG
  | ⟨_, sub⟩ => PG.sum (fun a => treePG (sub a))

/-- The classical origin inside the shape extension. -/
def UA.embed (t : Tree) : UA := UA.mk (treePG t)

theorem UA.mem_embed (α : Type) (A : α → Tree) (q : UA) :
    UA.Mem q (UA.embed ⟨α, A⟩) ↔ ∃ a, UA.embed (A a) = q :=
  UA.mem_sum (fun a => treePG (A a)) q

theorem UA.embed_eq_of_eqv : ∀ s t : Tree, Tree.Eqv s t → UA.embed s = UA.embed t
  | ⟨α, A⟩, ⟨β, B⟩, h => by
    obtain ⟨h1, h2⟩ := h
    apply ext_of_strong UA.strong
    intro c
    refine (UA.mem_embed α A c).trans (Iff.trans ⟨?_, ?_⟩ (UA.mem_embed β B c).symm)
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hab⟩ := h1 a
      exact ⟨b, (UA.embed_eq_of_eqv (A a) (B b) hab).symm⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨a, hab⟩ := h2 b
      exact ⟨a, UA.embed_eq_of_eqv (A a) (B b) hab⟩

theorem UA.eqv_of_embed_eq : ∀ s t : Tree, UA.embed s = UA.embed t → Tree.Eqv s t
  | ⟨α, A⟩, ⟨β, B⟩, h => by
    refine ⟨fun a => ?_, fun b => ?_⟩
    · have hm : UA.Mem (UA.embed (A a)) (UA.embed ⟨β, B⟩) := by
        rw [← h]
        exact (UA.mem_embed α A _).2 ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := (UA.mem_embed β B _).1 hm
      exact ⟨b, UA.eqv_of_embed_eq (A a) (B b) hb.symm⟩
    · have hm : UA.Mem (UA.embed (B b)) (UA.embed ⟨α, A⟩) := by
        rw [h]
        exact (UA.mem_embed β B _).2 ⟨b, rfl⟩
      obtain ⟨a, ha⟩ := (UA.mem_embed α A _).1 hm
      exact ⟨a, UA.eqv_of_embed_eq (A a) (B b) ha⟩

/-- **The classical origin sits inside the shape extension**: the embedding of the
    well-founded trees preserves and reflects equality … -/
theorem UA.embed_eq_iff (s t : Tree) : UA.embed s = UA.embed t ↔ Tree.Eqv s t :=
  ⟨UA.eqv_of_embed_eq s t, UA.embed_eq_of_eqv s t⟩

/-- … and membership. -/
theorem UA.embed_mem_iff (s t : Tree) : UA.Mem (UA.embed s) (UA.embed t) ↔ Tree.Mem s t := by
  cases t with
  | mk β B =>
    refine (UA.mem_embed β B _).trans ⟨?_, ?_⟩
    · rintro ⟨b, hb⟩
      exact ⟨b, UA.eqv_of_embed_eq s (B b) hb.symm⟩
    · rintro ⟨b, hb⟩
      exact ⟨b, (UA.embed_eq_of_eqv s (B b) hb).symm⟩

/-! ## 9. One scheme with a shape parameter; its two instances -/

/-- **GLU with a shape parameter.**  `ok` says which systems are allowed.  Every
    allowed system has exactly one solution, and every object is the value of a
    solution of an allowed system. -/
def GLUShape {B : Type u} (ok : ∀ {A : Type}, (A → A → Prop) → Prop) (E : B → B → Prop) :
    Prop :=
  (∀ (A : Type) (R : A → A → Prop), ok R →
    (∃ f : A → B, Solves R E f) ∧
    ∀ f g : A → B, Solves R E f → Solves R E g → ∀ x, f x = g x) ∧
  ∀ b : B, ∃ (A : Type) (R : A → A → Prop) (f : A → B) (x : A),
    ok R ∧ Solves R E f ∧ f x = b

/-- The constructed shape extension of §8 is the instance "all systems". -/
theorem UA.glu_all : GLUShape (fun _ => True) UA.Mem := by
  refine ⟨fun A R _ => ⟨⟨UA.dec R, UA.dec_solves R⟩,
    fun f g hf hg x => unique_of_strong UA.strong hf hg x⟩, fun b => ?_⟩
  refine Quotient.ind (motive := fun b => ∃ (A : Type) (R : A → A → Prop) (f : A → UA) (x : A),
    True ∧ Solves R UA.Mem f ∧ f x = b) (fun G => ?_) b
  exact ⟨G.N, G.R, UA.dec G.R, G.pt, trivial, UA.dec_solves G.R, rfl⟩

/-- **The instance "well-founded systems" is the classical one**: its completeness
    clause is foundation … -/
theorem wf_of_glu_wf {B : Type} {E : B → B → Prop}
    (h : GLUShape (fun R => WellFounded R) E) : WellFounded E :=
  (wf_iff_solved E).2 h.2

/-- … and its uniqueness clause is extensionality.  (Conversely, extensionality
    and replacement give the unique solutions by recursion, `recursion_solves`.) -/
theorem ext_of_glu_wf {B : Type} {E : B → B → Prop}
    (h : GLUShape (fun R => WellFounded R) E) : Extensional E :=
  ext_of_unique_wf (wf_of_glu_wf h) (fun A R f g hR hf hg => (h.1 A R hR).2 f g hf hg)

/-- The instance "all systems" makes identity bisimilarity. -/
theorem strong_of_glu_all {B : Type} {E : B → B → Prop}
    (h : GLUShape (fun _ => True) E) : StronglyExtensional E :=
  strong_of_unique (fun A R f g hf hg => (h.1 A R trivial).2 f g hf hg)

theorem acc_irrefl {B : Type u} {E : B → B → Prop} {a : B} (h : Acc E a) : ¬ E a a := by
  induction h with
  | intro x _ ih => exact fun hxx => ih x hxx hxx

/-- **The two instances cannot share one membership relation.**  "All systems"
    solves the loop and so puts an element inside itself; "well-founded
    systems" forbids exactly that.  Different shapes live in different kinds of
    object — which is why the extension adds kinds instead of changing the old
    one. -/
theorem not_wf_of_glu_all {B : Type u} {E : B → B → Prop}
    (h : GLUShape (fun _ => True) E) : ¬ WellFounded E := by
  intro hwf
  obtain ⟨f, hf⟩ := (h.1 Unit loop trivial).1
  have hself : E (f ()) (f ()) := (hf () (f ())).2 ⟨(), trivial, rfl⟩
  exact acc_irrefl (hwf.apply (f ())) hself

/-- **Along the shapes, the classical origin is not a shadow.**  The well-founded
    trees embed into the universe of all shapes (`UA.embed_eq_iff`,
    `UA.embed_mem_iff`), but nothing maps back into a well-founded structure while
    keeping membership: `Ω = {Ω}` cannot be flattened.  (Along the contexts the
    origin is a retract: `Kinds.U.eval_const`; notes/33.) -/
theorem UA.no_wf_shadow {B : Type u} {E : B → B → Prop} (hwf : WellFounded E) (φ : UA → B)
    (hφ : ∀ a b, UA.Mem a b → E (φ a) (φ b)) : False :=
  acc_irrefl (hwf.apply (φ UA.omega)) (hφ _ _ UA.omega_self)

end PZFC.Shapes
