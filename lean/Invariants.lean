/-
  Invariant walls (notes/07).  Mathlib-free.

  1. Lawvere's fixed-point theorem, absolute and relative to a language.
  2. Cantor / Russell: the Bool instance.  Nothing about *size* is used.
  3. Kripke's escape: on the flat three-element domain every monotone endomap
     has a fixed point, so the diagonal yields a fixed point, not a contradiction.
  4. Revenge: the operator needed to *say* "the liar is not true" is not
     monotone and has no fixed point, so the diagonal bites again.
  5. Equivariance: no symmetric choice from a collection without fixed points.
  6. A total order kills the symmetry: choice and order are one resource.
-/

namespace PZFC.Invariants

/-! ### 1. Lawvere -/

/-- Lawvere's fixed-point theorem in the category of types, with pointwise
    point-surjectivity. -/
theorem lawvere {A Y : Type} (φ : A → A → Y)
    (surj : ∀ g : A → Y, ∃ a : A, ∀ x, φ a x = g x) (f : Y → Y) :
    ∃ y : Y, f y = y := by
  obtain ⟨a, ha⟩ := surj (fun x => f (φ x x))
  exact ⟨φ a a, (ha a).symm⟩

/-- Relative form: a language can only enumerate what it can express.  The
    argument needs exactly one thing from the language — closure under
    "diagonalise, then apply `f`". -/
theorem lawvere_rel {A Y : Type} (Adm : (A → Y) → Prop) (φ : A → A → Y)
    (surj : ∀ g, Adm g → ∃ a, ∀ x, φ a x = g x)
    (f : Y → Y) (closed : Adm (fun x => f (φ x x))) : ∃ y, f y = y := by
  obtain ⟨a, ha⟩ := surj _ closed
  exact ⟨φ a a, (ha a).symm⟩

/-- The usable direction: a single fixed-point-free endomap rules out every
    enumeration of `Y`-valued predicates. -/
theorem no_enumeration {A Y : Type} (f : Y → Y) (hf : ∀ y, f y ≠ y)
    (φ : A → A → Y) : ¬ ∀ g : A → Y, ∃ a, ∀ x, φ a x = g x := by
  intro surj
  obtain ⟨y, hy⟩ := lawvere φ surj f
  exact hf y hy

/-! ### 2. Cantor and Russell -/

theorem bnot_no_fixed : ∀ b : Bool, (!b) ≠ b := by
  intro b; cases b <;> decide

theorem cantor (A : Type) (φ : A → A → Bool) :
    ¬ ∀ g : A → Bool, ∃ a, ∀ x, φ a x = g x :=
  no_enumeration (fun b => !b) bnot_no_fixed φ

/-- Russell.  `mem y x` reads "x ∈ y".  Two-valued membership plus naive
    comprehension for every predicate is impossible — and the proof uses only
    that negation on `Bool` has no fixed point, not any limitation of size. -/
theorem russell (U : Type) (mem : U → U → Bool) :
    ¬ ∀ P : U → Bool, ∃ y, ∀ x, mem y x = P x :=
  cantor U mem

/-! ### 3. Kripke's escape -/

/-- Strong Kleene values; `u` is "ungrounded". -/
inductive K3 where
  | u | f | t
  deriving DecidableEq

/-- Information order: `u` below everything, `f` and `t` incomparable. -/
def K3.le : K3 → K3 → Prop
  | .u, _ => True
  | .f, b => K3.f = b
  | .t, b => K3.t = b

def Monotone3 (g : K3 → K3) : Prop := ∀ a b, K3.le a b → K3.le (g a) (g b)

/-- Every monotone endomap of the flat three-element domain has a fixed point
    (the smallest case of Knaster–Tarski).  In this category Lawvere's theorem
    can never produce a contradiction. -/
theorem monotone_has_fixed (g : K3 → K3) (mono : Monotone3 g) : ∃ x, g x = x := by
  cases h : g .u with
  | u => exact ⟨.u, h⟩
  | f =>
    have hm := mono .u .f trivial
    rw [h] at hm
    exact ⟨.f, (show K3.f = g .f from hm).symm⟩
  | t =>
    have hm := mono .u .t trivial
    rw [h] at hm
    exact ⟨.t, (show K3.t = g .t from hm).symm⟩

/-- Strong Kleene negation. -/
def K3.neg : K3 → K3
  | .u => .u
  | .f => .t
  | .t => .f

theorem neg_monotone : Monotone3 K3.neg := by
  intro a b h
  cases a with
  | u => exact trivial
  | f =>
    have hb : K3.f = b := h
    subst hb
    exact rfl
  | t =>
    have hb : K3.t = b := h
    subst hb
    exact rfl

/-- The liar is assigned `u`: the diagonal lands on a fixed point. -/
theorem liar_is_ungrounded : K3.neg .u = .u := rfl

/-! ### 4. Revenge -/

/-- "Is not true".  Needed to *state* that the liar is not true; it sends `u`
    to `t`. -/
def K3.notTrue : K3 → K3
  | .t => .f
  | .f => .t
  | .u => .t

theorem notTrue_no_fixed : ∀ y, K3.notTrue y ≠ y := by
  intro y; cases y <;> decide

theorem notTrue_not_monotone : ¬ Monotone3 K3.notTrue := by
  intro mono
  have h := mono .u .t trivial
  exact absurd (show K3.t = K3.f from h) (by decide)

/-- Revenge: a language able to express `notTrue` cannot enumerate its own
    three-valued predicates.  Escaping the diagonal cost the language the
    ability to talk about the category it escaped into. -/
theorem revenge {A : Type} (Adm : (A → K3) → Prop) (φ : A → A → K3)
    (closed : Adm (fun x => K3.notTrue (φ x x))) :
    ¬ ∀ g, Adm g → ∃ a, ∀ x, φ a x = g x := by
  intro surj
  obtain ⟨y, hy⟩ := lawvere_rel Adm φ surj K3.notTrue closed
  exact notTrue_no_fixed y hy

/-! ### 5. Equivariance -/

/-- Symmetries `G` act on points `X` and on collections `C`.  If `S` is
    invariant and none of its members is fixed by every symmetry, no
    equivariant choice picks a member of `S`. -/
theorem no_equivariant_choice {G X C : Type}
    (actX : G → X → X) (actC : G → C → C) (mem : X → C → Prop)
    (choose : C → X)
    (equivariant : ∀ g c, choose (actC g c) = actX g (choose c))
    (S : C) (picks : mem (choose S) S)
    (invariant : ∀ g, actC g S = S)
    (noFixed : ∀ x, mem x S → ∃ g, actX g x ≠ x) : False := by
  obtain ⟨g, hg⟩ := noFixed (choose S) picks
  apply hg
  rw [← equivariant g S, invariant g]

inductive Atom where
  | a | b
  deriving DecidableEq

def swap : Atom → Atom
  | .a => .b
  | .b => .a

/-- Two indistinguishable atoms: `true` swaps them, `false` does nothing. -/
def actAtom : Bool → Atom → Atom
  | true,  x => swap x
  | false, x => x

/-- The shared core of: AC failing in a permutation model; a symmetric network
    unable to elect a leader (Angluin 1980); a deterministic machine over atoms
    unable to pick one. -/
theorem cannot_pick_an_atom (choose : Unit → Atom)
    (equivariant : ∀ (g : Bool) (c : Unit), choose c = actAtom g (choose c)) :
    False :=
  no_equivariant_choice actAtom (fun _ c => c) (fun _ _ => True) choose
    (fun g c => equivariant g c) () trivial (fun _ => rfl)
    (fun x _ => ⟨true, by cases x <;> decide⟩)

/-! ### 6. Order is symmetry breaking -/

/-- No strict total order on the atoms survives the swap.  Whoever has an order
    can choose (take the least); having the order already broke the symmetry. -/
theorem order_breaks_swap (lt : Atom → Atom → Prop)
    (total : lt .a .b ∨ lt .b .a)
    (asymm : ∀ x y, lt x y → ¬ lt y x) :
    ¬ ∀ x y, lt x y → lt (swap x) (swap y) := by
  intro pres
  cases total with
  | inl h => exact asymm _ _ h (pres _ _ h)
  | inr h => exact asymm _ _ h (pres _ _ h)

end PZFC.Invariants
