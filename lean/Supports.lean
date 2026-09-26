/-
  The symmetry extension: supports are contexts (notes/25).  Mathlib-free.

  In a universe with atoms, an object is given "in a context" `E` when every
  permutation of the atoms that `E` does not name leaves it unchanged — `E` is
  its support.  A selector on the two-element sets of atoms, given in a context
  `E`, must commute with every swap of two atoms outside `E`; on such a pair it
  would have to pick both.  So choice fails exactly for want of a context that
  names all the atoms (all but at most one), and no finite context does
  (`no_finite_context_chooses`).  Indiscernibility and the lack of a global
  context are the same thing here: an atom is indiscernible because no context
  in hand names it.
-/

namespace PZFC.Supports

/-- Swap two atoms. -/
def swap {A : Type} [DecidableEq A] (a b : A) (x : A) : A :=
  if x = a then b else if x = b then a else x

theorem swap_left {A : Type} [DecidableEq A] (a b : A) : swap a b a = b := by
  unfold swap
  exact if_pos rfl

theorem swap_right {A : Type} [DecidableEq A] {a b : A} (hab : a ≠ b) : swap a b b = a := by
  unfold swap
  rw [if_neg (fun h => hab h.symm), if_pos rfl]

/-- A selector on the two-element sets of atoms — `f a b` picks one of `a`, `b`,
    whatever the order they are given in — **given in the context `E`**: it
    commutes with every swap of two atoms that `E` does not name. -/
structure SelectorIn {A : Type} [DecidableEq A] (E : List A) where
  f : A → A → A
  picks : ∀ a b, f a b = a ∨ f a b = b
  sym : ∀ a b, f a b = f b a
  supported : ∀ a b x y, a ∉ E → b ∉ E → f (swap a b x) (swap a b y) = swap a b (f x y)

/-- **A selector given in context `E` cannot choose between two atoms that `E`
    does not name.** -/
theorem no_choice_outside {A : Type} [DecidableEq A] {E : List A} (s : SelectorIn E)
    {a b : A} (ha : a ∉ E) (hb : b ∉ E) (hab : a ≠ b) : False := by
  have h := s.supported a b a b ha hb
  rw [swap_left, swap_right hab, s.sym b a] at h
  rcases s.picks a b with hp | hp
  · rw [hp, swap_left] at h
    exact hab h
  · rw [hp, swap_right hab] at h
    exact hab h.symm

/-- Every atom a finite context names is at most the sum of the context. -/
theorem le_sum : ∀ (E : List Nat) (x : Nat), x ∈ E → x ≤ E.foldr (· + ·) 0
  | [], _, h => nomatch h
  | y :: E, x, h => by
    cases h with
    | head => exact Nat.le_add_right _ _
    | tail _ h' => exact Nat.le_trans (le_sum E x h') (Nat.le_add_left _ y)

/-- **No finite context names all the atoms**, so none supports a choice on all
    the pairs: over the atoms `ℕ`, every finite context leaves two atoms unnamed. -/
theorem no_finite_context_chooses (E : List Nat) : SelectorIn E → False := by
  intro s
  have hN : E.foldr (· + ·) 0 + 1 ∉ E := fun h =>
    Nat.not_succ_le_self _ (le_sum E _ h)
  have hN1 : E.foldr (· + ·) 0 + 2 ∉ E := fun h =>
    Nat.not_succ_le_self _ (Nat.le_trans (Nat.le_succ _) (le_sum E _ h))
  exact no_choice_outside s hN hN1 (fun h => Nat.succ_ne_self _ h.symm)

end PZFC.Supports
