/-
  GLU as one scheme (notes/23).  Mathlib-free.

  A shape is a family of contexts with a restriction relation.  Local data
  give each context a type of local sections, with restriction maps.  The
  glued objects are the compatible families.  GLU has two components:

    existence   locally consistent data glue
    uniqueness  a global object is determined by its local data

  Everything below is an instance of this one scheme:

  §2  discrete shape:   existence is exactly choice;
  §3  chain shape:      local consistency glues, using dependent choice;
  §4  membership shape: uniqueness is extensionality; existence fails (Russell);
  §5  the obstruction:  an odd cycle of negations — the diagonal (a self-loop)
                        and contextuality (a triangle) are the same theorem;
                        even cycles and paths glue; a fixed point of negation
                        dissolves it;
  §6  weights:          the uniqueness gap is measured by the spread of the
                        possible global extensions, and equals the defect.
-/

namespace PZFC.Glue

/-! ## 1. The scheme -/

/-- A shape: contexts, and which context restricts to which. -/
structure Shape where
  I : Type
  le : I → I → Prop

/-- Local data on a shape: local sections on each context, with restrictions. -/
structure Local (K : Shape) where
  D : K.I → Type
  res : ∀ {i j : K.I}, K.le i j → D j → D i

namespace Local

variable {K : Shape} (L : Local K)

/-- A compatible family: one local section per context, agreeing under restriction. -/
def Compatible (s : ∀ i, L.D i) : Prop :=
  ∀ i j (h : K.le i j), L.res h (s j) = s i

/-- The glued objects: compatible families. -/
def Glued : Type := { s : ∀ i, L.D i // L.Compatible s }

/-- Local consistency: every context is inhabited and every restriction is onto. -/
def LocallyConsistent : Prop :=
  (∀ i, Nonempty (L.D i)) ∧ ∀ i j (h : K.le i j) (a : L.D i), ∃ b, L.res h b = a

/-- GLU, existence: locally consistent data glue. -/
def GluesExist : Prop := L.LocallyConsistent → Nonempty L.Glued

end Local

/-- A candidate global object: a type with compatible projections to the local data. -/
structure Cone {K : Shape} (L : Local K) where
  G : Type
  proj : ∀ i, G → L.D i
  compat : ∀ i j (h : K.le i j) (g : G), L.res h (proj j g) = proj i g

namespace Cone

variable {K : Shape} {L : Local K} (C : Cone L)

/-- GLU, uniqueness: a global object is determined by its local data. -/
def Separated : Prop := ∀ g g', (∀ i, C.proj i g = C.proj i g') → g = g'

/-- GLU, existence relative to the cone: every compatible family is realised. -/
def Surjective : Prop := ∀ s : L.Glued, ∃ g, ∀ i, C.proj i g = s.val i

/-- The full local–global correspondence. -/
def GLU : Prop := C.Separated ∧ C.Surjective

end Cone

/-! ## 2. Discrete shape: existence is choice -/

def discrete (I : Type) : Shape := ⟨I, fun _ _ => False⟩

def discreteLocal {I : Type} (D : I → Type) : Local (discrete I) :=
  ⟨D, fun h _ => h.elim⟩

theorem discrete_glue_iff_choice {I : Type} (D : I → Type) :
    (discreteLocal D).GluesExist ↔ ((∀ i, Nonempty (D i)) → Nonempty (∀ i, D i)) := by
  constructor
  · intro h hne
    obtain ⟨s⟩ := h ⟨hne, fun _ _ hle => hle.elim⟩
    exact ⟨s.val⟩
  · intro h hlc
    obtain ⟨s⟩ := h hlc.1
    exact ⟨⟨s, fun _ _ hle => hle.elim⟩⟩

/-! ## 3. Chain shape: local consistency glues, using dependent choice -/

def chain : Shape := ⟨Nat, fun i j => j = i + 1⟩

def chainLocal (D : Nat → Type) (r : ∀ n, D (n + 1) → D n) : Local chain where
  D := D
  res := fun {i j} h x => by subst h; exact r i x

noncomputable def liftSeq (D : Nat → Type) (r : ∀ n, D (n + 1) → D n) (a0 : D 0)
    (surj : ∀ n (a : D n), ∃ b, r n b = a) : ∀ n, D n
  | 0 => a0
  | n + 1 => Classical.choose (surj n (liftSeq D r a0 surj n))

theorem chain_glues (D : Nat → Type) (r : ∀ n, D (n + 1) → D n) :
    (chainLocal D r).GluesExist := by
  intro hlc
  obtain ⟨a0⟩ := hlc.1 (0 : Nat)
  have surj : ∀ n (a : D n), ∃ b, r n b = a := fun n a => hlc.2 n (n + 1) rfl a
  refine ⟨⟨liftSeq D r a0 surj, ?_⟩⟩
  intro i j h
  subst h
  exact Classical.choose_spec (surj i (liftSeq D r a0 surj i))

/-! ## 4. Membership shape: uniqueness is extensionality, existence fails -/

structure SetStrB where
  S : Type
  mem : S → S → Bool

/-- Contexts are the sets themselves; the local datum of a set at `u` is whether
    `u` is a member. -/
def memLocal (M : SetStrB) : Local (discrete M.S) := discreteLocal (fun _ => Bool)

def memCone (M : SetStrB) : Cone (memLocal M) where
  G := M.S
  proj := fun u x => M.mem u x
  compat := fun _ _ h _ => h.elim

theorem memCone_separated_iff (M : SetStrB) :
    (memCone M).Separated ↔ ∀ x y, (∀ u, M.mem u x = M.mem u y) → x = y :=
  Iff.rfl

theorem memCone_not_surjective (M : SetStrB) : ¬ (memCone M).Surjective := by
  intro h
  obtain ⟨r, hr⟩ := h ⟨fun u => !(M.mem u u), fun _ _ hle => hle.elim⟩
  have hrr : M.mem r r = !(M.mem r r) := hr r
  revert hrr
  generalize M.mem r r = b
  cases b <;> decide

/-! ## 5. The obstruction: odd cycles of negation -/

def bxor : Bool → Bool → Bool
  | true, b => !b
  | false, b => b

theorem bxor_self (a : Bool) : bxor a a = false := by cases a <;> rfl

def lastOf {V : Type} : V → List V → V
  | a, [] => a
  | _, b :: rest => lastOf b rest

/-- Every consecutive pair on the walk meets its constraint `x u ⊕ x v = s u v`. -/
def EdgesOK {V : Type} (x : V → Bool) (s : V → V → Bool) : V → List V → Prop
  | _, [] => True
  | a, b :: rest => bxor (x a) (x b) = s a b ∧ EdgesOK x s b rest

/-- Parity of the constraint signs along the walk. -/
def signXor {V : Type} (s : V → V → Bool) : V → List V → Bool
  | _, [] => false
  | a, b :: rest => bxor (s a b) (signXor s b rest)

theorem signXor_telescope {V : Type} (x : V → Bool) (s : V → V → Bool) :
    ∀ (a : V) (l : List V), EdgesOK x s a l → signXor s a l = bxor (x a) (x (lastOf a l))
  | a, [], _ => (bxor_self (x a)).symm
  | a, b :: rest, ⟨hab, hrest⟩ => by
    show bxor (s a b) (signXor s b rest) = bxor (x a) (x (lastOf b rest))
    rw [signXor_telescope x s b rest hrest, ← hab]
    generalize x a = p
    generalize x b = q
    generalize x (lastOf b rest) = t
    cases p <;> cases q <;> cases t <;> rfl

/-- **The obstruction.**  If the signs around a closed walk have odd parity, no
    global assignment meets the local constraints along it. -/
theorem odd_cycle_obstructs {V : Type} (s : V → V → Bool) (a : V) (l : List V)
    (closed : lastOf a l = a) (odd : signXor s a l = true) :
    ¬ ∃ x : V → Bool, EdgesOK x s a l := by
  rintro ⟨x, hx⟩
  have h := signXor_telescope x s a l hx
  rw [closed, bxor_self, odd] at h
  exact absurd h (by decide)

/-- **Russell is an odd self-loop.**  A set `R` with `u ∈ R ↔ u ∉ u` gives, at
    `u = R`, a one-edge cycle whose constraint is a single negation. -/
theorem russell_is_odd_loop (M : SetStrB) (R : M.S)
    (hR : ∀ u, M.mem u R = !(M.mem u u)) : False := by
  have hloop : bxor (M.mem R R) (M.mem R R) = true := by
    have h := hR R
    revert h
    generalize M.mem R R = b
    cases b <;> decide
  exact odd_cycle_obstructs (fun _ _ => true) R [R] rfl rfl
    ⟨fun u => M.mem u R, hloop, trivial⟩

inductive Tri | a | b | c

/-- **Contextuality is an odd triangle.**  Three yes/no questions, each pair
    asked together and always answered differently: locally consistent,
    globally impossible. -/
theorem triangle_obstructs :
    ¬ ∃ x : Tri → Bool, EdgesOK x (fun _ _ => true) .a [.b, .c, .a] :=
  odd_cycle_obstructs _ _ _ rfl rfl

inductive Sq | a | b | c | d

/-- An even cycle of negations glues: parity, not the mere presence of a
    cycle, is the obstruction. -/
theorem square_glues : ∃ x : Sq → Bool, EdgesOK x (fun _ _ => true) .a [.b, .c, .d, .a] :=
  ⟨fun v => match v with | .a => true | .b => false | .c => true | .d => false,
   rfl, rfl, rfl, rfl, trivial⟩

/-- Drop one edge of the triangle — an acyclic shape — and it glues. -/
theorem path_glues : ∃ x : Tri → Bool, EdgesOK x (fun _ _ => true) .a [.b, .c] :=
  ⟨fun v => match v with | .a => true | .b => false | .c => true, rfl, rfl, trivial⟩

/-- With a value that negation fixes, every negation constraint on every shape is
    met by the constant assignment: the obstruction dissolves.
    (Kleene's `u` in `Invariants.K3`; `1/2` for `x ↦ 1 - x`.) -/
theorem fixed_point_dissolves {V W : Type} (neg : W → W) (c : W) (hc : neg c = c)
    (E : V → V → Prop) : ∀ u v, E u v → (fun _ : V => c) v = neg ((fun _ : V => c) u) :=
  fun _ _ _ => hc.symm

/-! ## 6. Weights: the uniqueness gap is a spread -/

inductive Status | inside | outside | split

/-- An atom of a finite partition: its mass, its position relative to a new event
    `A`, and — for one extension of the weight to `A` — the part of the mass
    assigned to `A`. -/
structure AtomExt where
  mass : Nat
  status : Status
  portion : Nat
  portion_le : portion ≤ mass

/-- What the extension gives to `A` from this atom. -/
def value (x : AtomExt) : Nat :=
  match x.status with
  | .inside => x.mass
  | .outside => 0
  | .split => x.portion

/-- Inner weight: atoms wholly inside `A`. -/
def inner (x : AtomExt) : Nat :=
  match x.status with
  | .inside => x.mass
  | _ => 0

/-- Outer weight: atoms meeting `A`. -/
def outer (x : AtomExt) : Nat :=
  match x.status with
  | .outside => 0
  | _ => x.mass

/-- The split mass: the atoms `A` cuts through. -/
def splitMass (x : AtomExt) : Nat :=
  match x.status with
  | .split => x.mass
  | _ => 0

def sumBy (f : AtomExt → Nat) : List AtomExt → Nat
  | [] => 0
  | x :: xs => f x + sumBy f xs

theorem inner_le_value (x : AtomExt) : inner x ≤ value x := by
  unfold inner value
  cases x.status
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact Nat.zero_le _

theorem value_le_outer (x : AtomExt) : value x ≤ outer x := by
  unfold value outer
  cases x.status
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact x.portion_le

theorem outer_eq (x : AtomExt) : outer x = inner x + splitMass x := by
  unfold outer inner splitMass
  cases x.status <;> first | rfl | exact (Nat.zero_add _).symm

/-- Every extension lies between the inner and the outer weight … -/
theorem extension_between : ∀ l : List AtomExt,
    sumBy inner l ≤ sumBy value l ∧ sumBy value l ≤ sumBy outer l
  | [] => ⟨Nat.le_refl _, Nat.le_refl _⟩
  | x :: xs =>
    ⟨Nat.add_le_add (inner_le_value x) (extension_between xs).1,
     Nat.add_le_add (value_le_outer x) (extension_between xs).2⟩

/-- … and the width of that interval is exactly the split mass — the defect.
    Uniqueness fails by precisely the mass that the new event cuts through. -/
theorem spread_eq_defect : ∀ l : List AtomExt,
    sumBy outer l = sumBy inner l + sumBy splitMass l
  | [] => rfl
  | x :: xs => by
    show outer x + sumBy outer xs = (inner x + sumBy inner xs) + (splitMass x + sumBy splitMass xs)
    rw [outer_eq x, spread_eq_defect xs]
    omega

end PZFC.Glue
