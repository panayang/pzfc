/-
  General independence relations (notes/69).  Mathlib-free.

  §1  swaps for an arbitrary independence relation; invariance under more swaps implies
      invariance under fewer, so a process symmetric for a relation is symmetric for every
      coarser one (in particular for the classes given by the components of the dependence graph)
  §2  sliding: a letter followed only by letters independent of it can be moved past them
      without changing a swap-invariant weight.  So the position of an element that nothing
      follows carries no weight of its own; in an infinite process this forces probability 0
-/
import Exchange

namespace PZFC.Traces

variable {L : Type}

/-! ## 1. Swaps for an arbitrary independence relation -/

/-- One swap of adjacent independent letters. -/
def IStep (I : L → L → Prop) (w₁ w₂ : List L) : Prop :=
  ∃ h t x y, I x y ∧ w₁ = h ++ x :: y :: t ∧ w₂ = h ++ y :: x :: t

/-- A weight unchanged by swaps of independent letters. -/
def Invariant (I : L → L → Prop) {X : Type} (F : List L → X) : Prop :=
  ∀ w₁ w₂, IStep I w₁ w₂ → F w₁ = F w₂

/-- **Coarsening**: invariance under the swaps of `I` gives invariance under the swaps of any
    smaller relation `I'`. -/
theorem invariant_mono {I I' : L → L → Prop} (h : ∀ x y, I' x y → I x y) {X : Type}
    (F : List L → X) (hF : Invariant I F) : Invariant I' F := by
  rintro w₁ w₂ ⟨u, t, x, y, hxy, rfl, rfl⟩
  exact hF _ _ ⟨u, t, x, y, h x y hxy, rfl, rfl⟩

/-- The class swaps of `Exchange` are the swaps of the relation "different classes". -/
theorem step_iff {C : Type} (cls : L → C) (w₁ w₂ : List L) :
    PZFC.Exch.Step cls w₁ w₂ ↔ IStep (fun x y => cls x ≠ cls y) w₁ w₂ := Iff.rfl

/-- So a weight invariant for `I` is invariant for the classes of any `cls` whose different
    classes are `I`-independent — for instance the components of the dependence graph. -/
theorem invariant_classes {C : Type} (cls : L → C) {I : L → L → Prop}
    (h : ∀ x y, cls x ≠ cls y → I x y) {X : Type} (F : List L → X) (hF : Invariant I F) :
    ∀ w₁ w₂, PZFC.Exch.Step cls w₁ w₂ → F w₁ = F w₂ :=
  fun w₁ w₂ hs => invariant_mono h F hF w₁ w₂ ((step_iff cls w₁ w₂).mp hs)

/-! ## 2. Sliding a letter that nothing depends on -/

/-- **Sliding**: if `m` is independent of every letter of `v₁`, moving `m` past `v₁` does not
    change a swap-invariant weight. -/
theorem slide (I : L → L → Prop) {X : Type} (F : List L → X) (hF : Invariant I F) (m : L)
    (v₂ : List L) : ∀ (u v₁ : List L), (∀ z ∈ v₁, I m z) →
      F (u ++ m :: (v₁ ++ v₂)) = F (u ++ v₁ ++ m :: v₂)
  | u, [], _ => by simp
  | u, z :: v₁, hv => by
    have h1 : F (u ++ m :: z :: (v₁ ++ v₂)) = F (u ++ z :: m :: (v₁ ++ v₂)) :=
      hF _ _ ⟨u, v₁ ++ v₂, m, z, hv z List.mem_cons_self, rfl, rfl⟩
    have h2 := slide I F hF m v₂ (u ++ [z]) v₁ (fun z' hz' => hv z' (List.mem_cons_of_mem z hz'))
    simp only [List.cons_append, List.append_assoc, List.nil_append] at h1 h2 ⊢
    rw [h1, h2]

/-- In particular, a letter that nothing after it depends on can be moved to the end. -/
theorem delay (I : L → L → Prop) {X : Type} (F : List L → X) (hF : Invariant I F) (u : List L)
    (m : L) (v : List L) (hv : ∀ z ∈ v, I m z) : F (u ++ m :: v) = F (u ++ v ++ [m]) := by
  have := slide I F hF m [] u v hv
  simpa using this

end PZFC.Traces
