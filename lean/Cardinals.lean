/-
  Where cardinality sits on the W-axis depends on choice (notes/16).
  Mathlib-free.

  A set is Dedekind-finite when every injective self-map is surjective.

  1. A Dedekind-finite set cannot absorb a point: A ⊕ 1 ≄ A.  Adding a point
     strictly increases its size — cancellative behaviour.
  2. A nonempty Dedekind-finite set cannot absorb its own double: A ⊕ A ≄ A.
  3. Absorbing a point is incompatible with Dedekind-finiteness; ℕ absorbs one.

  So "κ + κ = κ for every infinite κ" fails at every infinite Dedekind-finite
  set.  ZF has models with such sets; idempotency of cardinal addition is
  therefore a choice principle.  Choice is what pushes cardinality to the
  idempotent end of the W-axis.
-/

namespace PZFC.Cardinals

def Injective {α β : Type} (f : α → β) : Prop := ∀ a b, f a = f b → a = b
def Surjective {α β : Type} (f : α → β) : Prop := ∀ b, ∃ a, f a = b

/-- A bijection, as a pair of mutually inverse maps. -/
structure Bij (α β : Type) where
  to : α → β
  inv : β → α
  left : ∀ a, inv (to a) = a
  right : ∀ b, to (inv b) = b

def DedekindFinite (A : Type) : Prop :=
  ∀ f : A → A, Injective f → Surjective f

theorem bij_injective {α β : Type} (e : Bij α β) : Injective e.to := by
  intro a b h
  have h' := congrArg e.inv h
  rw [e.left, e.left] at h'
  exact h'

/-- A Dedekind-finite set cannot absorb a point. -/
theorem dfinite_no_absorb_point (A : Type) (hD : DedekindFinite A)
    (e : Bij (Sum A Unit) A) : False := by
  have hinj : Injective (fun a => e.to (Sum.inl a)) := by
    intro a b h
    exact Sum.inl.inj (bij_injective e _ _ h)
  obtain ⟨a, ha⟩ := hD _ hinj (e.to (Sum.inr ()))
  have h := bij_injective e _ _ ha
  cases h

/-- A nonempty Dedekind-finite set cannot absorb its own double. -/
theorem dfinite_no_absorb_double (A : Type) (hD : DedekindFinite A)
    (e : Bij (Sum A A) A) (a₀ : A) : False := by
  have hinj : Injective (fun a => e.to (Sum.inl a)) := by
    intro a b h
    exact Sum.inl.inj (bij_injective e _ _ h)
  obtain ⟨a, ha⟩ := hD _ hinj (e.to (Sum.inr a₀))
  have h := bij_injective e _ _ ha
  cases h

/-- Whatever absorbs a point is Dedekind-infinite. -/
theorem absorb_point_not_dfinite (A : Type) (e : Bij (Sum A Unit) A) :
    ¬ DedekindFinite A :=
  fun hD => dfinite_no_absorb_point A hD e

/-- ℕ absorbs a point (Hilbert's hotel), so ℕ sits at the idempotent end. -/
def natAbsorbsPoint : Bij (Sum Nat Unit) Nat where
  to
    | Sum.inl n => n + 1
    | Sum.inr _ => 0
  inv
    | 0 => Sum.inr ()
    | n + 1 => Sum.inl n
  left
    | Sum.inl _ => rfl
    | Sum.inr () => rfl
  right
    | 0 => rfl
    | _ + 1 => rfl

theorem nat_not_dfinite : ¬ DedekindFinite Nat :=
  absorb_point_not_dfinite Nat natAbsorbsPoint

end PZFC.Cardinals
