/-
  Objects are exactly what local computation can tell apart (notes/39).

  On a finite system, two nodes are the same object exactly when no deterministic
  local algorithm ever tells them apart.  One algorithm suffices: every node
  remembers everything it has seen — its view.  Views refine round by round; on a
  finite system they stop refining, and the stable views form a Larsen–Skou
  bisimulation (`Values.same_iff_ls`).  This holds for every value structure: with
  sharp answers, algorithms observe sets and objects are bisimulation classes; with
  weights, algorithms observe counts and objects are weighted bisimulation classes.
-/

import Local
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod

namespace PZFC.Views

open PZFC.Values PZFC.Local

variable {V : CVal}

/-- Views of depth `k`: all a node can know after `k` rounds. -/
def View (V : CVal) : Nat → Type
  | 0 => Unit
  | k + 1 => View V k × (View V k → V.W)

/-- The view of a node after `k` rounds: its earlier view, and the value with which
    each earlier view occurs among its members. -/
def view (G : Sys V) : (k : Nat) → G.N → View V k
  | 0, _ => ()
  | k + 1, x => (view G k x, fun u => V.agg (fun z : {z // view G k z = u} => G.R z.1 x))

/-- The view algorithm: every node remembers everything it has seen. -/
def viewAlg (V : CVal) : Alg V where
  S := Σ k, View V k
  init := ⟨0, ()⟩
  step s obs := ⟨s.1 + 1, (s.2, fun u => obs ⟨s.1, u⟩)⟩

/-- Running the view algorithm computes the views. -/
theorem run_view (G : Sys V) : ∀ k x, run (viewAlg V) G k x = ⟨k, view G k x⟩
  | 0, _ => rfl
  | k + 1, x => by
    have ih := run_view G k
    have hobs : (fun u => observe G (run (viewAlg V) G k) x ⟨k, u⟩) =
        (fun u => V.agg (fun z : {z // view G k z = u} => G.R z.1 x)) := by
      funext u
      exact V.agg_iff (fun z => run (viewAlg V) G k z = ⟨k, u⟩) (fun z => view G k z = u)
        (fun z => Iff.trans (Iff.of_eq (congrArg (· = ⟨k, u⟩) (ih z)))
          ⟨fun h => eq_of_heq (Sigma.mk.inj h).2, fun h => by rw [h]⟩)
        (fun z => G.R z x)
    show (viewAlg V).step (run (viewAlg V) G k x) (observe G (run (viewAlg V) G k) x) =
      ⟨k + 1, view G (k + 1) x⟩
    rw [ih x]
    show (⟨k + 1, (view G k x, fun u => observe G (run (viewAlg V) G k) x ⟨k, u⟩)⟩ :
        Σ k, View V k) =
      ⟨k + 1, (view G k x, fun u => V.agg (fun z : {z // view G k z = u} => G.R z.1 x))⟩
    rw [hobs]

theorem view_eq_of_run (G : Sys V) {k : Nat} {x y : G.N}
    (h : run (viewAlg V) G k x = run (viewAlg V) G k y) : view G k x = view G k y := by
  rw [run_view, run_view] at h
  exact eq_of_heq (Sigma.mk.inj h).2

open Classical in
/-- On a finite system, views stop refining: at some depth, nodes with the same view
    keep the same view one round later. -/
theorem views_stabilize (G : Sys V) [Finite G.N] :
    ∃ k, ∀ a b, view G k a = view G k b → view G (k + 1) a = view G (k + 1) b := by
  have := Fintype.ofFinite G.N
  let P : Nat → Finset (G.N × G.N) :=
    fun k => Finset.univ.filter (fun p => view G k p.1 = view G k p.2)
  have hsub : ∀ k, P (k + 1) ⊆ P k := by
    intro k p hp
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact congrArg Prod.fst hp
  have hcard : ∃ k, (P (k + 1)).card = (P k).card := by
    by_contra hne
    push Not at hne
    have hlt : ∀ k, (P (k + 1)).card < (P k).card := fun k =>
      lt_of_le_of_ne (Finset.card_le_card (hsub k)) (hne k)
    have hbound : ∀ k, (P k).card + k ≤ (P 0).card := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have := hlt k
        omega
    have := hbound ((P 0).card + 1)
    omega
  obtain ⟨k, hk⟩ := hcard
  refine ⟨k, fun a b hab => ?_⟩
  have heq : P (k + 1) = P k := Finset.eq_of_subset_of_card_le (hsub k) (le_of_eq hk.symm)
  have hmem : (a, b) ∈ P k := by
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hab
  rw [← heq] at hmem
  simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact hmem

/-- **On a finite system, two nodes are the same object exactly when all their views
    agree.** -/
theorem objects_are_views (G : Sys V) [Finite G.N] (x y : G.N) :
    dec G x = dec G y ↔ ∀ k, view G k x = view G k y := by
  constructor
  · intro h k
    exact view_eq_of_run G (run_object (viewAlg V) h k)
  · intro h
    obtain ⟨k, hk⟩ := views_stabilize G
    let v : G.N ⊕ G.N → View V k := Sum.elim (view G k) (view G k)
    refine (same_iff_ls G G x y).2 ⟨fun s t => v s = v t,
      ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2, fun {s t} hst c => ?_⟩, h k⟩
    have hs : ∀ s', classVal (G := G) (H := G) (fun s t => v s = v t) c s' =
        (view G (k + 1) (Sum.elim id id s')).2 (v c) := by
      intro s'
      cases s' with
      | inl a => rfl
      | inr b => rfl
    rw [hs, hs]
    have hv : view G (k + 1) (Sum.elim id id s) = view G (k + 1) (Sum.elim id id t) := by
      apply hk
      cases s <;> cases t <;> exact hst
    rw [hv]

/-- **On a finite system, objects are exactly what local computation can tell apart**:
    two nodes are the same object exactly when every deterministic local algorithm
    keeps them in the same state. -/
theorem objects_are_what_computation_sees (G : Sys V) [Finite G.N] (x y : G.N) :
    dec G x = dec G y ↔ ∀ (A : Alg V) (k : Nat), run A G k x = run A G k y := by
  constructor
  · exact fun h A k => run_object A h k
  · intro h
    exact (objects_are_views G x y).2 fun k => view_eq_of_run G (h (viewAlg V) k)

end PZFC.Views
