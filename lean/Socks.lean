/-
  Russell's socks (notes/21 §5).  Mathlib-free.

  A type that is *merely* two-element — a bijection with `Bool` exists, but
  none is handed to us (`Mere`, the quotient by the total relation) — carries
  a canonical uniform weight: compute it through any bijection; the answer
  does not depend on which.  No choice is
  used.  Selecting an element needs a bijection in hand; selecting from each of
  infinitely many such types at once is a choice function.

  Distributions exist; joint outcomes need not.
-/

namespace PZFC.Socks

/-- A bijection with `Bool`, as a pair of inverse maps. -/
structure Two (S : Type) where
  to : S → Bool
  inv : Bool → S
  left : ∀ s, inv (to s) = s
  right : ∀ b, to (inv b) = b

/-- Mere existence: the quotient of `α` by the total relation.  An element of
    `Mere α` says that some `a : α` exists without handing it over. -/
abbrev Mere (α : Type) : Type := Quot (fun (_ _ : α) => True)

def ind (b : Bool) : Nat := if b then 1 else 0

/-- How many of the two elements satisfy `A`, computed through a bijection. -/
def countVia {S : Type} (e : Two S) (A : S → Bool) : Nat :=
  ind (A (e.inv false)) + ind (A (e.inv true))

/-- The count does not depend on the bijection used. -/
theorem countVia_indep {S : Type} (e f : Two S) (A : S → Bool) :
    countVia e A = countVia f A := by
  have hf : ∀ b, f.inv b = e.inv (e.to (f.inv b)) := fun b => (e.left (f.inv b)).symm
  have ginj : ∀ b b', e.to (f.inv b) = e.to (f.inv b') → b = b' := by
    intro b b' h
    have h1 : f.inv b = f.inv b' := by
      have h' := congrArg e.inv h
      rwa [e.left, e.left] at h'
    have h2 := congrArg f.to h1
    rwa [f.right, f.right] at h2
  unfold countVia
  rw [hf false, hf true]
  cases h0 : e.to (f.inv false) <;> cases h1 : e.to (f.inv true)
  · exact absurd (ginj false true (h0.trans h1.symm)) (by decide)
  · rfl
  · exact Nat.add_comm _ _
  · exact absurd (ginj false true (h0.trans h1.symm)) (by decide)

/-- The canonical weight on a merely-two-element type: defined from the mere
    existence of a bijection, with no choice. -/
def weight {S : Type} (t : Mere (Two S)) (A : S → Bool) : Nat :=
  Quot.lift (fun e => countVia e A) (fun e f _ => countVia_indep e f A) t

/-- The whole pair weighs 2 … -/
theorem weight_whole {S : Type} (t : Mere (Two S)) : weight t (fun _ => true) = 2 := by
  refine Quot.ind (β := fun t => weight t (fun _ => true) = 2) (fun e => ?_) t
  rfl

/-- … and complementary events share it: the weight is a uniform
    distribution on the pair (after dividing by 2). -/
theorem weight_compl {S : Type} (t : Mere (Two S)) (A : S → Bool) :
    weight t A + weight t (fun s => !A s) = 2 := by
  refine Quot.ind (β := fun t => weight t A + weight t (fun s => !A s) = 2) (fun e => ?_) t
  show ind (A (e.inv false)) + ind (A (e.inv true))
      + (ind (!A (e.inv false)) + ind (!A (e.inv true))) = 2
  generalize A (e.inv false) = a
  generalize A (e.inv true) = b
  cases a <;> cases b <;> rfl

/-- Infinitely many pairs of socks: from the mere two-elementness of every
    pair, a whole family of weights — still with no choice.  A family of
    selections `∀ n, S n` would be a choice function; nothing here gives one.
    (That no symmetric selection exists is `Invariants.cannot_pick_an_atom`.) -/
def sockWeights (S : Nat → Type) (h : ∀ n, Mere (Two (S n))) (n : Nat) :
    (S n → Bool) → Nat :=
  weight (h n)

end PZFC.Socks
