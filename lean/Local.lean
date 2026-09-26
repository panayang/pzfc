/-
  Local computation (notes/39).  Mathlib-free.

  A deterministic local algorithm runs on a system.  Every node has a state; in each
  round every node updates its state from its own state and from what it observes
  of its members' states.  What it can observe is fixed by the value structure:
  with sharp answers, which states occur among its members (a set); with weights,
  how much of each state occurs (a multiset).  The nodes have no names: every node
  starts in the same state.

  §1  local algorithms and their runs;
  §2  a run commutes with solutions, so the state of a node depends only on the
      object the node is — nodes that are one object are never told apart;
  §3  where all nodes are one object, no algorithm elects a leader; the complete
      system is an example.
  (`lean-mathlib/Observe.lean`: sets versus counts; breaking symmetry with coins.)
-/

import Values

namespace PZFC.Local

open PZFC.Values

/-! ## 1. Local algorithms -/

/-- A deterministic local algorithm over a value structure `V`: states, an initial
    state, and a rule that updates a node's state from its own state and from the
    value with which each state occurs among its members. -/
structure Alg (V : CVal) where
  S : Type
  init : S
  step : S → (S → V.W) → S

variable {V : CVal}

/-- What a node observes of its members, given their states: for each state, the
    aggregated value of the members in that state. -/
def observe (G : Sys V) {S : Type} (st : G.N → S) (x : G.N) : S → V.W :=
  fun s => V.agg (fun z : {z // st z = s} => G.R z.1 x)

/-- The run of an algorithm on a system: the state of each node after `k` rounds.
    Every node starts in the same state — the nodes have no names. -/
def run (A : Alg V) (G : Sys V) : Nat → G.N → A.S
  | 0, _ => A.init
  | k + 1, x => A.step (run A G k x) (observe G (run A G k) x)

/-! ## 2. A node's state depends only on the object it is -/

/-- **A run commutes with solutions.** -/
theorem run_solves (A : Alg V) {G K : Sys V} {f : G.N → K.N} (hf : Solves G K f) :
    ∀ k x, run A K k (f x) = run A G k x
  | 0, _ => rfl
  | k + 1, x => by
    have ih := run_solves A hf k
    have hobs : observe K (run A K k) (f x) = observe G (run A G k) x := by
      funext s
      exact (solves_fiber hf (run A K k) s x).trans
        (V.agg_iff (fun z => run A K k (f z) = s) (fun z => run A G k z = s)
          (fun z => Iff.of_eq (congrArg (· = s) (ih z))) (fun z => G.R z x))
    show A.step (run A K k (f x)) (observe K (run A K k) (f x)) =
      A.step (run A G k x) (observe G (run A G k) x)
    rw [ih x, hobs]

/-- **Local algorithms see only objects**: nodes that are the same object are in the
    same state after any number of rounds, whatever the algorithm. -/
theorem run_object (A : Alg V) {G H : Sys V} {x : G.N} {y : H.N} (h : dec G x = dec H y)
    (k : Nat) : run A G k x = run A H k y := by
  obtain ⟨K, f, g, hf, hg, e⟩ := (dec_eq_iff G H x y).1 h
  rw [← run_solves A hf k x, ← run_solves A hg k y, e]

/-! ## 3. Where all nodes are one object, no leader -/

/-- **No leader where all nodes are one object**: if all nodes of a system are the
    same object and two of them differ, then after any number of rounds no state is
    held by exactly one node. -/
theorem no_leader (A : Alg V) (G : Sys V) (hsym : ∀ x y, dec G x = dec G y)
    {x₀ y₀ : G.N} (hne : x₀ ≠ y₀) (k : Nat) (s : A.S) :
    ¬ ∃ x, run A G k x = s ∧ ∀ y, run A G k y = s → y = x := by
  rintro ⟨x, hx, huniq⟩
  have h1 : x₀ = x := huniq x₀ ((run_object A (hsym x₀ x) k).trans hx)
  have h2 : y₀ = x := huniq y₀ ((run_object A (hsym y₀ x) k).trans hx)
  exact hne (h1.trans h2.symm)

/-- The complete system: every node is a member of every node, all with value `w`. -/
def complete (N : Type) (w : V.W) : Sys V := ⟨N, fun _ _ => w⟩

/-- A single node, a member of itself with the aggregate of `w` over `N`. -/
def loop (N : Type) (w : V.W) : Sys V := ⟨Unit, fun _ _ => V.agg (fun _ : N => w)⟩

theorem complete_solves (N : Type) (w : V.W) :
    Solves (complete N w) (loop N w) (fun _ => ()) := by
  intro _ b
  exact V.agg_iso (⟨fun z => ⟨z, rfl⟩, fun z => z.1, fun _ => rfl, fun _ => rfl⟩ :
    Iso N {z : N // (fun _ => ()) z = b}) (fun _ => w)

/-- In the complete system all nodes are one object. -/
theorem complete_same (N : Type) (w : V.W) (x y : N) :
    dec (complete N w) x = dec (complete N w) y :=
  (dec_image (complete_solves N w) x).trans (dec_image (complete_solves N w) y).symm

/-- **Anonymous nodes that all see each other alike elect no leader**, whatever the
    deterministic local algorithm. -/
theorem complete_no_leader (A : Alg V) (N : Type) (w : V.W) {x₀ y₀ : N} (hne : x₀ ≠ y₀)
    (k : Nat) (s : A.S) :
    ¬ ∃ x, run A (complete N w) k x = s ∧ ∀ y, run A (complete N w) k y = s → y = x :=
  no_leader A (complete N w) (complete_same N w) hne k s

end PZFC.Local
