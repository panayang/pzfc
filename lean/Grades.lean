/-
  Graded structures (notes/15).  Mathlib-free.

  1. Discernibility is a filtration: nested equivalence relations whose limit
     is equality.
  2. Membership is known at each depth only up to an interval
     (inner ⊆ set ⊆ outer), and the interval can only narrow.
  3. Counting discernibility classes is consistent under refinement:
     each refinement exactly doubles the count.
  4. Refinement forces the value algebra: with an idempotent addition the
     consistent weights are constant (binary); over ℕ no normalised weight
     exists (fractions are forced); with exclusive-or everything collapses.
     Existence is the image of counting under n ↦ (n > 0): the idempotent
     shadow of "how many".
  5. Indivisible values force binarism: truncated addition on ℕ admits only
     the saturated (constant) weight.
  6. Omniscience is a lattice, not a switch: LPO ⟹ WLPO ⟹ LLPO, and
     LPO ⟺ WLPO ∧ MP.
-/

namespace PZFC.Grades

abbrev Record := Nat → Bool

/-! ## 1. Discernibility as a filtration -/

def Agree (N : Nat) (α β : Record) : Prop := ∀ n, n < N → α n = β n

theorem agree_refl (N : Nat) (α : Record) : Agree N α α := fun _ _ => rfl

theorem agree_symm {N : Nat} {α β : Record} (h : Agree N α β) : Agree N β α :=
  fun n hn => (h n hn).symm

theorem agree_trans {N : Nat} {α β γ : Record}
    (h₁ : Agree N α β) (h₂ : Agree N β γ) : Agree N α γ :=
  fun n hn => (h₁ n hn).trans (h₂ n hn)

/-- Deeper agreement implies shallower agreement: the relations are nested. -/
theorem agree_mono {M N : Nat} (hMN : M ≤ N) {α β : Record} (h : Agree N α β) :
    Agree M α β :=
  fun n hn => h n (Nat.lt_of_lt_of_le hn hMN)

/-- Equality is the limit of the filtration, not a primitive bit. -/
theorem eq_iff_agree_all (α β : Record) : (∀ n, α n = β n) ↔ ∀ N, Agree N α β :=
  ⟨fun h _ n _ => h n, fun h n => h (n + 1) n (Nat.lt_succ_self n)⟩

/-! ## 2. Membership up to an interval -/

/-- The whole depth-`N` class of `α` lies inside `A`. -/
def Inner (N : Nat) (A : Record → Prop) (α : Record) : Prop :=
  ∀ β, Agree N α β → A β

/-- The depth-`N` class of `α` meets `A`. -/
def Outer (N : Nat) (A : Record → Prop) (α : Record) : Prop :=
  ∃ β, Agree N α β ∧ A β

theorem inner_sub {N : Nat} {A : Record → Prop} {α : Record} :
    Inner N A α → A α :=
  fun h => h α (agree_refl N α)

theorem sub_outer {N : Nat} {A : Record → Prop} {α : Record} :
    A α → Outer N A α :=
  fun h => ⟨α, agree_refl N α, h⟩

/-- Going deeper can only enlarge the inner approximation … -/
theorem inner_mono {N : Nat} {A : Record → Prop} {α : Record} :
    Inner N A α → Inner (N + 1) A α :=
  fun h β hβ => h β (agree_mono (Nat.le_succ N) hβ)

/-- … and only shrink the outer one: the interval narrows. -/
theorem outer_anti {N : Nat} {A : Record → Prop} {α : Record} :
    Outer (N + 1) A α → Outer N A α :=
  fun ⟨β, hβ, hA⟩ => ⟨β, agree_mono (Nat.le_succ N) hβ, hA⟩

def zeroRec : Record := fun _ => false
def IsZero (α : Record) : Prop := ∀ n, α n = false

/-- At no depth does `{zeroRec}` contain zeroRec's whole class … -/
theorem zero_never_inner (N : Nat) : ¬ Inner N IsZero zeroRec := by
  intro h
  have hβ := h (fun n => if n < N then false else true) (by
    intro n hn
    show false = (if n < N then false else true)
    rw [if_pos hn])
  have hN : (if N < N then false else true) = false := hβ N
  rw [if_neg (Nat.lt_irrefl N)] at hN
  exact absurd hN (by decide)

/-- … yet at every depth it meets it: at this point the interval never closes. -/
theorem zero_always_outer (N : Nat) : Outer N IsZero zeroRec :=
  sub_outer (fun _ => rfl)

/-! ## 3. Counting discernibility classes -/

/-- Number of length-`n` prefixes satisfying `p`.  Each prefix is one depth-`n`
    discernibility class. -/
def count : Nat → (List Bool → Bool) → Nat
  | 0, p => if p [] then 1 else 0
  | n + 1, p => count n (fun s => p (s ++ [false])) + count n (fun s => p (s ++ [true]))

theorem count_congr : ∀ (n : Nat) (p q : List Bool → Bool),
    (∀ s, p s = q s) → count n p = count n q
  | 0, p, q, h => by
    show (if p [] then 1 else 0) = (if q [] then 1 else 0)
    rw [h []]
  | n + 1, p, q, h => by
    show count n (fun s => p (s ++ [false])) + count n (fun s => p (s ++ [true]))
       = count n (fun s => q (s ++ [false])) + count n (fun s => q (s ++ [true]))
    rw [count_congr n (fun s => p (s ++ [false])) (fun s => q (s ++ [false]))
          (fun s => h (s ++ [false])),
        count_congr n (fun s => p (s ++ [true])) (fun s => q (s ++ [true]))
          (fun s => h (s ++ [true]))]

theorem dropLast_snoc (b : Bool) : ∀ s : List Bool, (s ++ [b]).dropLast = s
  | [] => rfl
  | [_] => rfl
  | x :: y :: ys => by
    show x :: ((y :: ys) ++ [b]).dropLast = x :: y :: ys
    rw [dropLast_snoc b (y :: ys)]

/-- Refine a depth-`n` predicate to depth `n+1` by ignoring the newest answer. -/
def refine (p : List Bool → Bool) : List Bool → Bool := fun s => p s.dropLast

/-- Each refinement exactly doubles the count. -/
theorem count_refine (n : Nat) (p : List Bool → Bool) :
    count (n + 1) (refine p) = 2 * count n p := by
  show count n (fun s => p (s ++ [false]).dropLast)
     + count n (fun s => p (s ++ [true]).dropLast) = 2 * count n p
  rw [count_congr n (fun s => p (s ++ [false]).dropLast) p
        (fun s => congrArg p (dropLast_snoc false s)),
      count_congr n (fun s => p (s ++ [true]).dropLast) p
        (fun s => congrArg p (dropLast_snoc true s)),
      Nat.two_mul]

/-- There are `2^n` classes at depth `n`. -/
theorem count_true : ∀ n : Nat, count n (fun _ => true) = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    show count n (fun _ => true) + count n (fun _ => true) = 2 ^ (n + 1)
    rw [count_true n, Nat.pow_succ, Nat.mul_two]

/-! ## 4. Refinement forces the value algebra -/

def iter {W : Type} (f : W → W) : Nat → W → W
  | 0, x => x
  | k + 1, x => f (iter f k x)

theorem iter_succ' {W : Type} (f : W → W) : ∀ (k : Nat) (x : W),
    iter f (k + 1) x = iter f k (f x)
  | 0, _ => rfl
  | k + 1, x => by
    show f (iter f (k + 1) x) = f (iter f k (f x))
    rw [iter_succ' f k x]

/-- Every depth-`n` class carries the same weight `u n` (indifference), and a
    class weighs the sum of its two refinements (consistency).  Then, in *any*
    value algebra, the whole is `2^n`-fold a depth-`n` class. -/
theorem refinement_forces_doubling {W : Type} (add : W → W → W) (u : Nat → W)
    (consistent : ∀ n, u n = add (u (n + 1)) (u (n + 1))) :
    ∀ n, u 0 = iter (fun x => add x x) n (u n)
  | 0 => rfl
  | n + 1 => by
    rw [refinement_forces_doubling add u consistent n, consistent n, iter_succ']

theorem idempotent_step {W : Type} (add : W → W → W) (idem : ∀ x, add x x = x)
    (u : Nat → W) (consistent : ∀ n, u n = add (u (n + 1)) (u (n + 1))) :
    ∀ n, u (n + 1) = u n := by
  intro n
  rw [consistent n, idem]

/-- Idempotent addition: consistent weights are constant.  The weight records
    only *whether*, never *how much* — the binary case. -/
theorem idempotent_forces_constant {W : Type} (add : W → W → W)
    (idem : ∀ x, add x x = x) (u : Nat → W)
    (consistent : ∀ n, u n = add (u (n + 1)) (u (n + 1))) :
    ∀ n, u n = u 0
  | 0 => rfl
  | n + 1 => (idempotent_step add idem u consistent n).trans
      (idempotent_forces_constant add idem u consistent n)

theorem add_self_ne_one : ∀ x : Nat, x + x ≠ 1
  | 0, h => Nat.noConfusion h
  | x + 1, h => by
    have h' : (x + 1) + x = 0 := Nat.succ.inj h
    cases x with
    | zero => exact Nat.noConfusion h'
    | succ y => exact Nat.noConfusion h'

/-- Over `ℕ` with `+`, no normalised consistent weight exists: counting cannot
    stay integral under refinement.  Fractions are forced. -/
theorem no_integer_normalisation :
    ¬ ∃ u : Nat → Nat, u 0 = 1 ∧ ∀ n, u n = u (n + 1) + u (n + 1) := by
  rintro ⟨u, h0, hc⟩
  exact add_self_ne_one (u 1) ((hc 0).symm.trans h0)

theorem or_idempotent : ∀ x : Bool, (x || x) = x := by
  intro x; cases x <;> rfl

/-- With `||` a normalised consistent weight exists; by
    `idempotent_forces_constant` it is the constant one: "possible" at every
    depth, and nothing finer. -/
theorem or_possibility :
    ∃ u : Nat → Bool, u 0 = true ∧ ∀ n, u n = (u (n + 1) || u (n + 1)) :=
  ⟨fun _ => true, rfl, fun _ => rfl⟩

def bxor : Bool → Bool → Bool
  | true, b => !b
  | false, b => b

/-- With exclusive-or, doubling annihilates: no normalised consistent weight. -/
theorem xor_collapses :
    ¬ ∃ u : Nat → Bool, u 0 = true ∧ ∀ n, u n = bxor (u (n + 1)) (u (n + 1)) := by
  rintro ⟨u, h0, hc⟩
  have h := (hc 0).symm.trans h0
  cases hu : u 1 <;> rw [hu] at h <;> exact absurd h (by decide)

/-- The idempotent count: is some depth-`n` class in `p`? -/
def anyN : Nat → (List Bool → Bool) → Bool
  | 0, p => p []
  | n + 1, p => anyN n (fun s => p (s ++ [false])) || anyN n (fun s => p (s ++ [true]))

theorem pos_add_iff : ∀ x y : Nat, 0 < x + y ↔ 0 < x ∨ 0 < y
  | 0, 0 => ⟨fun h => absurd h (Nat.lt_irrefl 0),
      fun h => h.elim (fun h => absurd h (Nat.lt_irrefl 0)) (fun h => absurd h (Nat.lt_irrefl 0))⟩
  | x + 1, y => ⟨fun _ => Or.inl (Nat.succ_pos x),
      fun _ => Nat.lt_of_lt_of_le (Nat.succ_pos x) (Nat.le_add_right (x + 1) y)⟩
  | 0, y + 1 => ⟨fun _ => Or.inr (Nat.succ_pos y), fun _ => Nat.succ_pos _⟩

theorem or_true_iff : ∀ a b : Bool, (a || b) = true ↔ a = true ∨ b = true
  | true, _ => ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | false, true => ⟨fun _ => Or.inr rfl, fun _ => rfl⟩
  | false, false => ⟨fun h => absurd h (by decide),
      fun h => h.elim (fun h => absurd h (by decide)) (fun h => absurd h (by decide))⟩

/-- Existence is the image of counting under `n ↦ (n > 0)`, the homomorphism
    from `(ℕ, +)` onto `(Bool, ||)`.  Set-theoretic "there is one" is the
    idempotent shadow of "how many" — and because `||` is idempotent, the whole
    (`2^n` classes) already has weight `true`: no normalisation, no fractions. -/
theorem any_iff_count_pos : ∀ (n : Nat) (p : List Bool → Bool),
    anyN n p = true ↔ 0 < count n p
  | 0, p => by
    show p [] = true ↔ 0 < (if p [] then 1 else 0)
    cases h : p [] with
    | false => exact ⟨fun h => absurd h (by decide), fun h => absurd h (Nat.lt_irrefl 0)⟩
    | true => exact ⟨fun _ => Nat.zero_lt_one, fun _ => rfl⟩
  | n + 1, p => by
    have hf := any_iff_count_pos n (fun s => p (s ++ [false]))
    have ht := any_iff_count_pos n (fun s => p (s ++ [true]))
    show (anyN n (fun s => p (s ++ [false])) || anyN n (fun s => p (s ++ [true]))) = true
      ↔ 0 < count n (fun s => p (s ++ [false])) + count n (fun s => p (s ++ [true]))
    refine (or_true_iff _ _).trans (Iff.trans ?_ (pos_add_iff _ _).symm)
    exact ⟨fun h => h.elim (fun h => Or.inl (hf.mp h)) (fun h => Or.inr (ht.mp h)),
           fun h => h.elim (fun h => Or.inl (hf.mpr h)) (fun h => Or.inr (ht.mpr h))⟩

/-! ## 5. Indivisible values force binarism

  The one place in these files that uses `omega`, hence the axioms `propext`
  and `Quot.sound`.  Both hold in every topos; neither is choice or excluded
  middle, so the theorem still transfers to every foundation considered here.
-/

theorem lt_two_pow : ∀ n : Nat, n < 2 ^ n
  | 0 => Nat.zero_lt_one
  | n + 1 => by
    have ih := lt_two_pow n
    rw [Nat.pow_succ, Nat.mul_two]
    omega

/-- With truncated addition on `ℕ` (values capped at `K`), the only normalised
    consistent weight is the saturated one: every class weighs the full `K`.
    An indivisible value algebra admits no graded weights at all — binarism is
    a consequence of the value algebra, not a primitive. -/
theorem truncated_saturates (K : Nat) (hK : 0 < K) (u : Nat → Nat)
    (h0 : u 0 = K) (hc : ∀ n, u n = min K (u (n + 1) + u (n + 1))) :
    ∀ n, u n = K := by
  have below : ∀ m, u m < K → u m = u (m + 1) + u (m + 1) ∧ u (m + 1) < K := by
    intro m hm
    have h := hc m
    constructor <;> omega
  have descent : ∀ m, u m < K → ∀ j, u m = 2 ^ j * u (m + j) ∧ u (m + j) < K := by
    intro m hm j
    induction j with
    | zero => exact ⟨(Nat.one_mul _).symm, hm⟩
    | succ j ih =>
      obtain ⟨h1, h2⟩ := ih
      obtain ⟨h3, h4⟩ := below (m + j) h2
      refine ⟨?_, h4⟩
      rw [h1, h3, Nat.pow_succ, Nat.mul_assoc, Nat.two_mul]
      rfl
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    have hpos : 1 ≤ u (n + 1) := by
      have h := hc n
      omega
    have hle : u (n + 1) ≤ K := by
      have h := hc (n + 1)
      omega
    cases Nat.lt_or_ge (u (n + 1)) K with
    | inr hge => omega
    | inl hlt =>
      obtain ⟨hK', _⟩ := descent (n + 1) hlt K
      have hx : 1 ≤ u (n + 1 + K) := by
        cases hx0 : u (n + 1 + K) with
        | zero =>
          rw [hx0, Nat.mul_zero] at hK'
          omega
        | succ x => exact Nat.succ_le_succ (Nat.zero_le x)
      have hbig : 2 ^ K ≤ u (n + 1) := by
        rw [hK']
        exact Nat.le_mul_of_pos_right _ hx
      have := lt_two_pow K
      omega

/-! ## 6. Omniscience is a lattice -/

def LPO : Prop := ∀ α : Record, (∀ n, α n = false) ∨ ∃ n, α n = true
def WLPO : Prop := ∀ α : Record, (∀ n, α n = false) ∨ ¬ ∀ n, α n = false
def MP : Prop := ∀ α : Record, (¬ ∀ n, α n = false) → ∃ n, α n = true
def AtMostOne (α : Record) : Prop := ∀ m n, α m = true → α n = true → m = n
def LLPO : Prop := ∀ α : Record, AtMostOne α →
  (∀ n, α (2 * n) = false) ∨ ∀ n, α (2 * n + 1) = false

theorem lpo_wlpo : LPO → WLPO := by
  intro h α
  cases h α with
  | inl h0 => exact Or.inl h0
  | inr hex =>
    obtain ⟨n, hn⟩ := hex
    exact Or.inr (fun hall => absurd ((hall n).symm.trans hn) (by decide))

theorem lpo_mp : LPO → MP := by
  intro h α hne
  cases h α with
  | inl h0 => exact absurd h0 hne
  | inr hex => exact hex

theorem wlpo_mp_lpo : WLPO → MP → LPO := by
  intro hw hm α
  cases hw α with
  | inl h0 => exact Or.inl h0
  | inr hne => exact Or.inr (hm α hne)

theorem two_mul_ne_succ : ∀ n m : Nat, 2 * n ≠ 2 * m + 1
  | 0, _, h => Nat.noConfusion h
  | _ + 1, 0, h => Nat.noConfusion (Nat.succ.inj h)
  | n + 1, m + 1, h => two_mul_ne_succ n m (Nat.succ.inj (Nat.succ.inj h))

theorem wlpo_llpo : WLPO → LLPO := by
  intro hw α h1
  cases hw (fun n => α (2 * n)) with
  | inl heven => exact Or.inl heven
  | inr hne =>
    refine Or.inr (fun m => ?_)
    cases hm : α (2 * m + 1) with
    | false => rfl
    | true =>
      exact absurd (fun n => show α (2 * n) = false by
        cases hn : α (2 * n) with
        | false => rfl
        | true => exact absurd (h1 _ _ hn hm) (two_mul_ne_succ n m)) hne

end PZFC.Grades
