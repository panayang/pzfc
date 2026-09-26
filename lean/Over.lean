/-
  Values over contexts (notes/36).  Mathlib-free.

  Over a preorder of contexts, an answer can depend on the context and grow as the
  context is refined: a monotone function from contexts to values.  When the
  values are ordered and the aggregate respects the order, such functions,
  aggregated context by context, again form a complete value structure.  So the
  one construction (`Values`) gives a kind with values, all shapes, and a
  preorder of contexts at once — in a presentation where identity is global and
  membership varies with the context.

  §1  ordered complete value structures; sharp answers, ordered by implication;
  §2  values over a preorder of contexts form a complete value structure, so the
      kind over them satisfies GLU (`Values.glu`);
  §3  the classical origin along the contexts: constant values embed, looking at
      one context is a shadow, and together they give the identity; with a
      single context the kind is the kind of the values;
  §4  the first layer of the wall: over two contexts with a common refinement, an
      object has a member in every context, yet no object is its member in every
      context — existence is local.
-/

import Values

namespace PZFC.Over

open PZFC.Values

/-! ## 1. Ordered complete value structures -/

/-- A complete value structure with an order that the aggregate respects. -/
structure OCVal extends CVal where
  le : W → W → Prop
  le_refl : ∀ w, le w w
  agg_mono : ∀ {ι : Type} {f g : ι → W}, (∀ i, le (f i) (g i)) → le (agg f) (agg g)

/-- Sharp answers, ordered by implication. -/
abbrev sharpO : OCVal where
  toCVal := sharp
  le p q := p → q
  le_refl _ := id
  agg_mono h := fun ⟨i, hi⟩ => ⟨i, h i hi⟩

/-! ## 2. Values over a preorder of contexts -/

/-- Values over the contexts: answers that may depend on the context and only grow
    as the context is refined, aggregated context by context. -/
def OCVal.over (V : OCVal) (C : Type) (le : C → C → Prop) : CVal where
  W := {f : C → V.W // ∀ c d, le c d → V.le (f c) (f d)}
  agg f := ⟨fun c => V.agg (fun i => (f i).1 c), fun c d h => V.agg_mono (fun i => (f i).2 c d h)⟩
  agg_iso e f := Subtype.ext (funext fun c => V.agg_iso e (fun k => (f k).1 c))
  agg_unit w := Subtype.ext (funext fun c => V.agg_unit (w.1 c))
  agg_sigma f := Subtype.ext (funext fun c => V.agg_sigma (fun i k => (f i k).1 c))

/-- **GLU over a preorder of contexts, with any ordered values.** -/
theorem glu_over (V : OCVal) (C : Type) (le : C → C → Prop) :
    (∀ G : Sys (V.over C le), SolvesU G (dec G) ∧ ∀ f, SolvesU G f → ∀ x, f x = dec G x) ∧
    ∀ a : UV (V.over C le), ∃ (G : Sys (V.over C le)) (x : G.N), dec G x = a :=
  glu (V.over C le)

/-! ## 3. The classical origin along the contexts -/

/-- Looking at one context: a shadow. -/
def evalAt (V : OCVal) (C : Type) (le : C → C → Prop) (c : C) : CHom (V.over C le) V.toCVal :=
  ⟨fun w => w.1 c, fun _ => rfl⟩

/-- Constant values: the embedding. -/
def constV (V : OCVal) (C : Type) (le : C → C → Prop) : CHom V.toCVal (V.over C le) :=
  ⟨fun w => ⟨fun _ => w, fun _ _ _ => V.le_refl w⟩, fun _ => rfl⟩

/-- **Along the contexts, the origin is a retract**: embed with constant values,
    then look at one context — the object comes back. -/
theorem eval_const (V : OCVal) (C : Type) (le : C → C → Prop) (c : C) (a : UV V.toCVal) :
    UV.map (evalAt V C le c) (UV.map (constV V C le) a) = a :=
  Quotient.ind (motive := fun a => UV.map (evalAt V C le c) (UV.map (constV V C le) a) = a)
    (fun _ => rfl) a

/-- With a single context, values over it are just values: the two kinds correspond. -/
theorem const_eval_point (V : OCVal) (a : UV (V.over Unit (fun _ _ => True))) :
    UV.map (constV V Unit _) (UV.map (evalAt V Unit _ ()) a) = a :=
  Quotient.ind (motive := fun a =>
      UV.map (constV V Unit _) (UV.map (evalAt V Unit _ ()) a) = a)
    (fun _ => rfl) a

/-! ## 4. The first layer of the wall: existence is local -/

/-- Two contexts `l` and `r`, with a common refinement `t`. -/
inductive Ctx3
  | l | r | t

def cle : Ctx3 → Ctx3 → Prop
  | .l, .l => True
  | .r, .r => True
  | .t, .t => True
  | .l, .t => True
  | .r, .t => True
  | _, _ => False

/-- Truth values over the three contexts: the up-sets. -/
abbrev Ω3 : CVal := sharpO.over Ctx3 cle

def inL : Ctx3 → Prop
  | .r => False
  | _ => True

def inR : Ctx3 → Prop
  | .l => False
  | _ => True

/-- True in `l` and `t`. -/
def onL : Ω3.W :=
  ⟨inL, fun c d h hc => by
    cases c <;> cases d <;> first | trivial | exact False.elim h | exact False.elim hc⟩

/-- True in `r` and `t`. -/
def onR : Ω3.W :=
  ⟨inR, fun c d h hc => by
    cases c <;> cases d <;> first | trivial | exact False.elim h | exact False.elim hc⟩

def top : Ω3.W := ⟨fun _ => True, fun _ _ _ _ => trivial⟩

def bot : Ω3.W := ⟨fun _ => False, fun _ _ _ h => h⟩

inductive Nd
  | u | a | b | leaf

/-- `a` is a member of `u` in `l` and `t`, `b` in `r` and `t`; `a` holds a leaf,
    `b` holds nothing. -/
def sys : Sys Ω3 where
  N := Nd
  R z x := match z, x with
    | .a, .u => onL
    | .b, .u => onR
    | .leaf, .a => top
    | _, _ => bot

/-- `a` and `b` are different objects. -/
theorem a_ne_b : dec sys .a ≠ dec sys .b := by
  intro h
  have ha : (UV.E (dec sys .leaf) (dec sys .a)).1 .l := ⟨⟨.leaf, rfl⟩, trivial⟩
  rw [h] at ha
  obtain ⟨⟨z, _⟩, hz⟩ := ha
  cases z <;> exact hz

/-- In every context, `u` has a member. -/
theorem inhabited_everywhere (c : Ctx3) : ∃ y, (UV.E y (dec sys .u)).1 c := by
  cases c with
  | l => exact ⟨dec sys .a, ⟨⟨.a, rfl⟩, trivial⟩⟩
  | r => exact ⟨dec sys .b, ⟨⟨.b, rfl⟩, trivial⟩⟩
  | t => exact ⟨dec sys .a, ⟨⟨.a, rfl⟩, trivial⟩⟩

/-- No object is a member of `u` in every context. -/
theorem no_member_everywhere : ¬ ∃ y, ∀ c, (UV.E y (dec sys .u)).1 c := by
  rintro ⟨y, hy⟩
  obtain ⟨⟨z, hz⟩, hzl⟩ := hy .l
  obtain ⟨⟨w, hw⟩, hwr⟩ := hy .r
  have hza : z = .a := by cases z <;> first | rfl | exact False.elim hzl
  have hwb : w = .b := by cases w <;> first | rfl | exact False.elim hwr
  subst hza
  subst hwb
  exact a_ne_b (hz.trans hw.symm)

/-- **Existence is local, in this presentation**: over two contexts with a common
    refinement, `u` has a member in every context, and yet no object is its member
    in every context. -/
theorem existence_is_local :
    (∀ c, ∃ y, (UV.E y (dec sys .u)).1 c) ∧ ¬ ∃ y, ∀ c, (UV.E y (dec sys .u)).1 c :=
  ⟨inhabited_everywhere, no_member_everywhere⟩

end PZFC.Over
