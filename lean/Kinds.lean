/-
  Kinds over contexts — stages 2 and 2b (notes/29, notes/30).  Mathlib-free.

  A structure of contexts is a small category: an arrow `c ⟶ d` carries what is
  known at `c` into `d` (a refinement), and an arrow from a context to itself is
  a symmetry.  A system over the contexts gives, in each context, nodes and
  which node is a member of which; arrows carry nodes along, and membership
  persists along them.  An answer can also be a name — "I am this atom" — and
  names are carried along arrows too; pure sets are the systems with no names.

  §1  the kind (sharp answers, all shapes, contexts `K`, names `Λ`): pointed
      systems, up to bisimulation that persists along arrows and matches names.
      GLU holds: every system has exactly one solution, natural in the
      contexts; every object is the value of one; identity is bisimilarity;
  §2  the classical origin inside: a plain system held constant over the
      contexts gives global objects, equal exactly when plainly bisimilar;
  §3  the first layer of the wall, formally: over two contexts with a common
      refinement, an object can have a member in every context and yet no global
      member — existence is local.  With a single context, local is global;
  §4  pure sets carry no symmetry: over a group of symmetries every pure object
      is fixed, since objects in one orbit are bisimilar;
  §5  names carry it: over the group of order two swapping two socks, the pair is
      global and has members, but no member is global — Russell's socks, in the
      kind; the symmetric form of "existence is local";
  §6  when local members do glue (notes/32): with a root — a context every other
      refines — a member in the root is carried everywhere, with no choice; over
      disjoint contexts, choice picks one member in each.  Together with §3 and
      §5: choice survives the loss of a global context exactly as far as local
      choices can be glued along the contexts;
  §7  the origin is also a shadow (notes/33): looking at one context keeps
      membership and names, and a constant object looked at in one context is the
      plain object again — along the contexts, the classical origin is a retract
      of every kind;
  §8  the criterion over a preorder of contexts (notes/35): local existence always
      glues exactly when each context has a root below it that does not change
      along arrows — a least context in each connected component.  Choice picks
      across the roots; conversely, the names of a global member exhibit the
      roots, with no choice;
  §9  the criterion over any structure of contexts (notes/38): local existence
      always glues exactly when there is a chosen arrow into every context,
      compatible with all arrows.  Over a group this happens only for the
      trivial group: with any symmetry, some locally inhabited global object has
      no global member.
-/

namespace PZFC.Kinds

/-- A structure of contexts: a small category.  `comp f g` is "first `f`, then `g`". -/
structure Ctx where
  C : Type
  Hom : C → C → Type
  id : ∀ c, Hom c c
  comp : ∀ {a b c}, Hom a b → Hom b c → Hom a c
  id_comp : ∀ {a b} (f : Hom a b), comp (id a) f = f
  comp_id : ∀ {a b} (f : Hom a b), comp f (id b) = f
  assoc : ∀ {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d),
    comp (comp f g) h = comp f (comp g h)

/-- Names: in each context, the names an answer can give ("I am this atom"),
    carried along arrows. -/
structure Lab (K : Ctx) where
  L : K.C → Type
  lact : ∀ {c d}, K.Hom c d → L c → L d

/-- No names: pure sets. -/
def Lab.pure (K : Ctx) : Lab K := ⟨fun _ => Empty, fun _ e => e⟩

/-- A system over the contexts: nodes in each context, carried along arrows;
    membership in each context, persisting along arrows; and, for a node that is
    an atom, its name. -/
structure CSys (K : Ctx) (Λ : Lab K) where
  N : K.C → Type
  act : ∀ {c d}, K.Hom c d → N c → N d
  act_id : ∀ c (x : N c), act (K.id c) x = x
  act_comp : ∀ {a b c} (f : K.Hom a b) (g : K.Hom b c) (x : N a),
    act (K.comp f g) x = act g (act f x)
  R : ∀ c, N c → N c → Prop
  mono : ∀ {c d} (f : K.Hom c d) {z x : N c}, R c z x → R d (act f z) (act f x)
  lab : ∀ c, N c → Option (Λ.L c)
  lab_act : ∀ {c d} (f : K.Hom c d) (x : N c), lab d (act f x) = (lab c x).map (Λ.lact f)

/-- A system is pure when none of its nodes is an atom. -/
def CSys.Pure {K : Ctx} {Λ : Lab K} (G : CSys K Λ) : Prop := ∀ c x, G.lab c x = none

/-- A bisimulation between two systems: in each context it relates nodes with the
    same name whose members match, and it persists along arrows. -/
def CSys.IsBisim {K : Ctx} {Λ : Lab K} (G H : CSys K Λ) (S : ∀ c, G.N c → H.N c → Prop) :
    Prop :=
  (∀ {c d} (f : K.Hom c d) {x y}, S c x y → S d (G.act f x) (H.act f y)) ∧
  (∀ c x y, S c x y → G.lab c x = H.lab c y) ∧
  ∀ c x y, S c x y →
    (∀ x', G.R c x' x → ∃ y', H.R c y' y ∧ S c x' y') ∧
    (∀ y', H.R c y' y → ∃ x', G.R c x' x ∧ S c x' y')

/-! ## 1. The kind -/

/-- A system pointed at a node in context `c`. -/
structure Pt (K : Ctx) (Λ : Lab K) (c : K.C) where
  sys : CSys K Λ
  pt : sys.N c

def Pt.Bis {K : Ctx} {Λ : Lab K} {c : K.C} (p q : Pt K Λ c) : Prop :=
  ∃ S, CSys.IsBisim p.sys q.sys S ∧ S c p.pt q.pt

theorem Pt.bis_refl {K : Ctx} {Λ : Lab K} {c : K.C} (p : Pt K Λ c) : p.Bis p := by
  refine ⟨fun _ x y => x = y, ⟨?_, ?_, ?_⟩, rfl⟩
  · intro _ _ f x y h
    subst h
    rfl
  · intro _ x y h
    rw [h]
  · intro _ x y h
    subst h
    exact ⟨fun x' hx => ⟨x', hx, rfl⟩, fun y' hy => ⟨y', hy, rfl⟩⟩

theorem Pt.bis_symm {K : Ctx} {Λ : Lab K} {c : K.C} {p q : Pt K Λ c} (h : p.Bis q) :
    q.Bis p := by
  obtain ⟨S, ⟨hp, hl, hb⟩, hs⟩ := h
  refine ⟨fun d y x => S d x y,
    ⟨fun {_c _d} f {_x _y} h => hp f h, fun d y x h => (hl d x y h).symm, ?_⟩, hs⟩
  intro d y x hxy
  obtain ⟨h1, h2⟩ := hb d x y hxy
  exact ⟨h2, h1⟩

theorem Pt.bis_trans {K : Ctx} {Λ : Lab K} {c : K.C} {p q r : Pt K Λ c} (h1 : p.Bis q)
    (h2 : q.Bis r) : p.Bis r := by
  obtain ⟨S, ⟨hSp, hSl, hSb⟩, hs⟩ := h1
  obtain ⟨T, ⟨hTp, hTl, hTb⟩, ht⟩ := h2
  refine ⟨fun d x z => ∃ y, S d x y ∧ T d y z, ⟨?_, ?_, ?_⟩, ⟨q.pt, hs, ht⟩⟩
  · rintro d e f x z ⟨y, hxy, hyz⟩
    exact ⟨q.sys.act f y, hSp f hxy, hTp f hyz⟩
  · rintro d x z ⟨y, hxy, hyz⟩
    exact (hSl d x y hxy).trans (hTl d y z hyz)
  · rintro d x z ⟨y, hxy, hyz⟩
    obtain ⟨hS1, hS2⟩ := hSb d x y hxy
    obtain ⟨hT1, hT2⟩ := hTb d y z hyz
    constructor
    · intro x' hx'
      obtain ⟨y', hy', hxy'⟩ := hS1 x' hx'
      obtain ⟨z', hz', hyz'⟩ := hT1 y' hy'
      exact ⟨z', hz', y', hxy', hyz'⟩
    · intro z' hz'
      obtain ⟨y', hy', hyz'⟩ := hT2 z' hz'
      obtain ⟨x', hx', hxy'⟩ := hS2 y' hy'
      exact ⟨x', hx', y', hxy', hyz'⟩

instance Pt.setoid (K : Ctx) (Λ : Lab K) (c : K.C) : Setoid (Pt K Λ c) :=
  ⟨Pt.Bis, ⟨Pt.bis_refl, Pt.bis_symm, Pt.bis_trans⟩⟩

/-- The kind over the contexts: in each context, pointed systems up to bisimulation. -/
def U (K : Ctx) (Λ : Lab K) (c : K.C) : Type 1 := Quotient (Pt.setoid K Λ c)

def U.mk {K : Ctx} {Λ : Lab K} {c : K.C} (p : Pt K Λ c) : U K Λ c :=
  Quotient.mk (Pt.setoid K Λ c) p

/-- `p` is a member of `q` in context `c`: bisimilar to `q` pointed at one of its
    members there. -/
def Pt.Mem {K : Ctx} {Λ : Lab K} {c : K.C} (p q : Pt K Λ c) : Prop :=
  ∃ m, q.sys.R c m q.pt ∧ p.Bis ⟨q.sys, m⟩

theorem Pt.mem_congr {K : Ctx} {Λ : Lab K} {c : K.C} {p p' q q' : Pt K Λ c} (hp : p.Bis p')
    (hq : q.Bis q') : p.Mem q → p'.Mem q' := by
  rintro ⟨m, hm, hpm⟩
  obtain ⟨T, hT, hpt⟩ := hq
  obtain ⟨m', hm', hmm'⟩ := (hT.2.2 c q.pt q'.pt hpt).1 m hm
  have hsub : Pt.Bis (⟨q.sys, m⟩ : Pt K Λ c) ⟨q'.sys, m'⟩ := ⟨T, hT, hmm'⟩
  exact ⟨m', hm', Pt.bis_trans (Pt.bis_symm hp) (Pt.bis_trans hpm hsub)⟩

/-- Membership in the kind, in context `c`. -/
def U.Mem {K : Ctx} {Λ : Lab K} {c : K.C} : U K Λ c → U K Λ c → Prop :=
  Quotient.lift₂ Pt.Mem (fun _ _ _ _ hp hq =>
    propext ⟨Pt.mem_congr hp hq, Pt.mem_congr (Pt.bis_symm hp) (Pt.bis_symm hq)⟩)

/-- The name of an object of the kind, if it is an atom. -/
def U.lab {K : Ctx} {Λ : Lab K} {c : K.C} : U K Λ c → Option (Λ.L c) :=
  Quotient.lift (fun p => p.sys.lab c p.pt) (fun _ _ h => by
    obtain ⟨S, hS, hs⟩ := h
    exact hS.2.1 c _ _ hs)

/-- Carry a pointed system along an arrow. -/
def Pt.act {K : Ctx} {Λ : Lab K} {c d : K.C} (f : K.Hom c d) (p : Pt K Λ c) : Pt K Λ d :=
  ⟨p.sys, p.sys.act f p.pt⟩

theorem Pt.act_congr {K : Ctx} {Λ : Lab K} {c d : K.C} (f : K.Hom c d) {p q : Pt K Λ c}
    (h : p.Bis q) : (p.act f).Bis (q.act f) := by
  obtain ⟨S, hS, hs⟩ := h
  exact ⟨S, hS, hS.1 f hs⟩

/-- Carry an object of the kind along an arrow. -/
def U.act {K : Ctx} {Λ : Lab K} {c d : K.C} (f : K.Hom c d) : U K Λ c → U K Λ d :=
  Quotient.lift (fun p => U.mk (p.act f)) (fun _ _ h => Quotient.sound (Pt.act_congr f h))

theorem U.act_id {K : Ctx} {Λ : Lab K} (c : K.C) (u : U K Λ c) : U.act (K.id c) u = u := by
  refine Quotient.ind (motive := fun u => U.act (K.id c) u = u) (fun p => ?_) u
  show U.mk ⟨p.sys, p.sys.act (K.id c) p.pt⟩ = U.mk p
  rw [p.sys.act_id]

theorem U.act_comp {K : Ctx} {Λ : Lab K} {a b c : K.C} (f : K.Hom a b) (g : K.Hom b c)
    (u : U K Λ a) : U.act (K.comp f g) u = U.act g (U.act f u) := by
  refine Quotient.ind (motive := fun u => U.act (K.comp f g) u = U.act g (U.act f u))
    (fun p => ?_) u
  show U.mk ⟨p.sys, p.sys.act (K.comp f g) p.pt⟩ = U.mk ⟨p.sys, p.sys.act g (p.sys.act f p.pt)⟩
  rw [p.sys.act_comp]

/-- Membership in the kind persists along arrows. -/
theorem U.mem_act {K : Ctx} {Λ : Lab K} {c d : K.C} (f : K.Hom c d) {a b : U K Λ c}
    (h : U.Mem a b) : U.Mem (U.act f a) (U.act f b) := by
  revert h
  refine Quotient.ind₂ (motive := fun a b => U.Mem a b → U.Mem (U.act f a) (U.act f b))
    (fun p q => ?_) a b
  rintro ⟨m, hm, hpm⟩
  exact ⟨q.sys.act f m, q.sys.mono f hm, Pt.act_congr f hpm⟩

/-- Names are carried along arrows. -/
theorem U.lab_act {K : Ctx} {Λ : Lab K} {c d : K.C} (f : K.Hom c d) (u : U K Λ c) :
    U.lab (U.act f u) = (U.lab u).map (Λ.lact f) := by
  refine Quotient.ind (motive := fun u => U.lab (U.act f u) = (U.lab u).map (Λ.lact f))
    (fun p => ?_) u
  exact p.sys.lab_act f p.pt

/-- The solution of a system: node `x` in context `c` goes to the system pointed
    at `x`. -/
def dec {K : Ctx} {Λ : Lab K} (G : CSys K Λ) (c : K.C) (x : G.N c) : U K Λ c := U.mk ⟨G, x⟩

theorem dec_natural {K : Ctx} {Λ : Lab K} (G : CSys K Λ) {c d : K.C} (f : K.Hom c d)
    (x : G.N c) : U.act f (dec G c x) = dec G d (G.act f x) := rfl

/-- In each context, the members of the value of `x` are exactly the values of the
    members of `x`. -/
theorem dec_solves {K : Ctx} {Λ : Lab K} (G : CSys K Λ) (c : K.C) (x : G.N c)
    (q : U K Λ c) : U.Mem q (dec G c x) ↔ ∃ z, G.R c z x ∧ dec G c z = q := by
  refine Quotient.ind (motive := fun q => U.Mem q (dec G c x) ↔ ∃ z, G.R c z x ∧ dec G c z = q)
    (fun p => ?_) q
  constructor
  · rintro ⟨z, hz, hp⟩
    exact ⟨z, hz, Quotient.sound (Pt.bis_symm hp)⟩
  · rintro ⟨z, hz, h⟩
    exact ⟨z, hz, Pt.bis_symm (Quotient.exact h)⟩

/-- A bisimulation on the kind itself: a relation in each context that persists
    along arrows, matches names, and matches members. -/
def UBisim {K : Ctx} {Λ : Lab K} (S : ∀ c, U K Λ c → U K Λ c → Prop) : Prop :=
  (∀ {c d} (f : K.Hom c d) {a b}, S c a b → S d (U.act f a) (U.act f b)) ∧
  (∀ c a b, S c a b → U.lab a = U.lab b) ∧
  ∀ c a b, S c a b →
    (∀ a', U.Mem a' a → ∃ b', U.Mem b' b ∧ S c a' b') ∧
    (∀ b', U.Mem b' b → ∃ a', U.Mem a' a ∧ S c a' b')

/-- **Identity in the kind is bisimilarity**: related objects are equal. -/
theorem U.strong {K : Ctx} {Λ : Lab K} (S : ∀ c, U K Λ c → U K Λ c → Prop) (hS : UBisim S)
    (c : K.C) (a b : U K Λ c) (hab : S c a b) : a = b := by
  revert hab
  refine Quotient.ind (motive := fun a => S c a b → a = b) (fun p => ?_) a
  refine Quotient.ind (motive := fun b => S c (U.mk p) b → U.mk p = b) (fun q => ?_) b
  intro hpq
  apply Quotient.sound
  refine ⟨fun d n m => S d (U.mk ⟨p.sys, n⟩) (U.mk ⟨q.sys, m⟩), ⟨?_, ?_, ?_⟩, hpq⟩
  · intro d e f n m h
    exact hS.1 f h
  · intro d n m h
    exact hS.2.1 d _ _ h
  · intro d n m hnm
    obtain ⟨h1, h2⟩ := hS.2.2 d _ _ hnm
    constructor
    · intro n' hn'
      have hmem : U.Mem (U.mk (⟨p.sys, n'⟩ : Pt K Λ d)) (U.mk ⟨p.sys, n⟩) :=
        ⟨n', hn', Pt.bis_refl _⟩
      obtain ⟨w, hw, hsw⟩ := h1 _ hmem
      revert hw hsw
      refine Quotient.ind (motive := fun w => U.Mem w (U.mk (⟨q.sys, m⟩ : Pt K Λ d)) →
        S d (U.mk ⟨p.sys, n'⟩) w →
          ∃ m', q.sys.R d m' m ∧ S d (U.mk ⟨p.sys, n'⟩) (U.mk ⟨q.sys, m'⟩))
        (fun r => ?_) w
      rintro ⟨m', hm', hr⟩ hsw
      refine ⟨m', hm', ?_⟩
      have e : Quotient.mk (Pt.setoid K Λ d) r = U.mk ⟨q.sys, m'⟩ := Quotient.sound hr
      exact e ▸ hsw
    · intro m' hm'
      have hmem : U.Mem (U.mk (⟨q.sys, m'⟩ : Pt K Λ d)) (U.mk ⟨q.sys, m⟩) :=
        ⟨m', hm', Pt.bis_refl _⟩
      obtain ⟨w, hw, hsw⟩ := h2 _ hmem
      revert hw hsw
      refine Quotient.ind (motive := fun w => U.Mem w (U.mk (⟨p.sys, n⟩ : Pt K Λ d)) →
        S d w (U.mk ⟨q.sys, m'⟩) →
          ∃ n', p.sys.R d n' n ∧ S d (U.mk ⟨p.sys, n'⟩) (U.mk ⟨q.sys, m'⟩))
        (fun r => ?_) w
      rintro ⟨n', hn', hr⟩ hsw
      refine ⟨n', hn', ?_⟩
      have e : Quotient.mk (Pt.setoid K Λ d) r = U.mk ⟨p.sys, n'⟩ := Quotient.sound hr
      exact e ▸ hsw

/-- A solution of `G` in the kind: natural in the contexts, keeping names, and
    solving `G` in each context. -/
def Solution {K : Ctx} {Λ : Lab K} (G : CSys K Λ) (f : ∀ c, G.N c → U K Λ c) : Prop :=
  (∀ {c d} (g : K.Hom c d) x, U.act g (f c x) = f d (G.act g x)) ∧
  (∀ c x, U.lab (f c x) = G.lab c x) ∧
  ∀ c x q, U.Mem q (f c x) ↔ ∃ z, G.R c z x ∧ f c z = q

theorem dec_solution {K : Ctx} {Λ : Lab K} (G : CSys K Λ) : Solution G (dec G) :=
  ⟨fun g x => dec_natural G g x, fun _ _ => rfl, dec_solves G⟩

theorem solution_unique {K : Ctx} {Λ : Lab K} (G : CSys K Λ) {f g : ∀ c, G.N c → U K Λ c}
    (hf : Solution G f) (hg : Solution G g) (c : K.C) (x : G.N c) : f c x = g c x := by
  refine U.strong (fun d a b => ∃ y, f d y = a ∧ g d y = b) ⟨?_, ?_, ?_⟩ c _ _ ⟨x, rfl, rfl⟩
  · rintro d e h a b ⟨y, rfl, rfl⟩
    exact ⟨G.act h y, (hf.1 h y).symm, (hg.1 h y).symm⟩
  · rintro d a b ⟨y, rfl, rfl⟩
    exact (hf.2.1 d y).trans (hg.2.1 d y).symm
  · rintro d a b ⟨y, rfl, rfl⟩
    constructor
    · intro a' ha'
      obtain ⟨z, hz, rfl⟩ := (hf.2.2 d y a').1 ha'
      exact ⟨g d z, (hg.2.2 d y (g d z)).2 ⟨z, hz, rfl⟩, z, rfl, rfl⟩
    · intro b' hb'
      obtain ⟨z, hz, rfl⟩ := (hg.2.2 d y b').1 hb'
      exact ⟨f d z, (hf.2.2 d y (f d z)).2 ⟨z, hz, rfl⟩, z, rfl, rfl⟩

/-- **GLU over contexts** (sharp answers and names, all shapes): every system has
    exactly one solution, and every object of the kind is the value of a solution. -/
theorem glu_over_contexts (K : Ctx) (Λ : Lab K) :
    (∀ G : CSys K Λ, Solution G (dec G) ∧ ∀ f, Solution G f → ∀ c x, f c x = dec G c x) ∧
    ∀ c (u : U K Λ c), ∃ (G : CSys K Λ) (x : G.N c), dec G c x = u := by
  refine ⟨fun G => ⟨dec_solution G, fun f hf c x => solution_unique G hf (dec_solution G) c x⟩,
    fun c u => ?_⟩
  refine Quotient.ind (motive := fun u => ∃ (G : CSys K Λ) (x : G.N c), dec G c x = u)
    (fun p => ?_) u
  exact ⟨p.sys, p.pt, rfl⟩

/-! ## 2. The classical origin inside: constant objects -/

/-- A plain system — one context's nodes and membership, no atoms — held constant
    over all the contexts. -/
def const (K : Ctx) (Λ : Lab K) (A : Type) (R : A → A → Prop) : CSys K Λ where
  N := fun _ => A
  act := fun _ x => x
  act_id := fun _ _ => rfl
  act_comp := fun _ _ _ => rfl
  R := fun _ => R
  mono := fun {_c _d} _ {_z _x} h => h
  lab := fun _ _ => none
  lab_act := fun _ _ => rfl

/-- A plain bisimulation. -/
def PBisim {A B : Type} (R : A → A → Prop) (R' : B → B → Prop) (S : A → B → Prop) : Prop :=
  ∀ x y, S x y →
    (∀ x', R x' x → ∃ y', R' y' y ∧ S x' y') ∧ (∀ y', R' y' y → ∃ x', R x' x ∧ S x' y')

/-- Constant objects are global: every arrow carries them to themselves. -/
theorem const_global {K : Ctx} {Λ : Lab K} {c d : K.C} (f : K.Hom c d) {A : Type}
    (R : A → A → Prop) (x : A) : U.act f (dec (const K Λ A R) c x) = dec (const K Λ A R) d x :=
  rfl

/-- **The classical origin sits inside every kind over contexts**: constant objects
    are equal exactly when they are plainly bisimilar. -/
theorem const_eq_iff {K : Ctx} {Λ : Lab K} (c : K.C) {A B : Type} (R : A → A → Prop)
    (R' : B → B → Prop) (x : A) (y : B) :
    dec (const K Λ A R) c x = dec (const K Λ B R') c y ↔ ∃ S, PBisim R R' S ∧ S x y := by
  constructor
  · intro h
    obtain ⟨S, hS, hs⟩ := Quotient.exact h
    exact ⟨S c, fun x y hxy => hS.2.2 c x y hxy, hs⟩
  · rintro ⟨S, hS, hs⟩
    apply Quotient.sound
    exact ⟨fun _ => S, ⟨fun {_c _d} _ {_x _y} h => h, fun _ _ _ _ => rfl,
      fun _ x y hxy => hS x y hxy⟩, hs⟩

/-! ## 3. The first layer of the wall: existence is local -/

/-- A preorder of contexts as a context structure: at most one arrow, `c ⟶ d` when
    `d` refines `c`. -/
def Ctx.ofPreorder (C : Type) (le : C → C → Prop) (refl : ∀ c, le c c)
    (trans : ∀ {a b c}, le a b → le b c → le a c) : Ctx where
  C := C
  Hom := fun a b => PLift (le a b)
  id := fun c => ⟨refl c⟩
  comp := fun f g => ⟨trans f.down g.down⟩
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl

/-- A global object: one in every context, carried into itself along every arrow. -/
def Glob (K : Ctx) (Λ : Lab K) : Type 1 :=
  {u : ∀ c, U K Λ c // ∀ {c d} (f : K.Hom c d), U.act f (u c) = u d}

inductive Cosp | l | r | t
  deriving DecidableEq

/-- Two contexts `l` and `r` with a common refinement `t`. -/
def cosp : Ctx :=
  Ctx.ofPreorder Cosp (fun a b => a = b ∨ b = .t) (fun _ => Or.inl rfl)
    (fun hab hbc => by
      rcases hab with rfl | rfl <;> rcases hbc with rfl | rfl <;>
        first | exact Or.inl rfl | exact Or.inr rfl)

inductive Top4 | u | a | b | e
  deriving DecidableEq

def exN : Cosp → Type
  | .l => Bool
  | .r => Bool
  | .t => Top4

/-- Along `l ⟶ t` the member `true` becomes `a`; along `r ⟶ t` it becomes `b`. -/
def exAct : ∀ {c d : Cosp}, cosp.Hom c d → exN c → exN d
  | .l, .l, _, x => x
  | .r, .r, _, x => x
  | .t, .t, _, x => x
  | .l, .t, _, x => cond x Top4.a Top4.u
  | .r, .t, _, x => cond x Top4.b Top4.u
  | .l, .r, h, _ => absurd (PLift.down h) (by decide)
  | .r, .l, h, _ => absurd (PLift.down h) (by decide)
  | .t, .l, h, _ => absurd (PLift.down h) (by decide)
  | .t, .r, h, _ => absurd (PLift.down h) (by decide)

/-- In `l` and in `r`, `true` is the one member of `false`; in `t`, `a` and `b`
    are the members of `u`, and `e` is a member of `b`. -/
def exR : ∀ c, exN c → exN c → Prop
  | .l, z, x => x = false ∧ z = true
  | .r, z, x => x = false ∧ z = true
  | .t, z, x => (x = Top4.u ∧ (z = Top4.a ∨ z = Top4.b)) ∨ (x = Top4.b ∧ z = Top4.e)

def exSys : CSys cosp (Lab.pure cosp) where
  N := exN
  act := exAct
  act_id := by
    intro c x
    cases c <;> rfl
  act_comp := by
    intro a b c f g x
    cases a <;> cases b <;> cases c <;>
      first
        | rfl
        | exact absurd (PLift.down f) (by decide)
        | exact absurd (PLift.down g) (by decide)
  R := exR
  mono := by
    intro c d f z x h
    cases c <;> cases d
    all_goals first
      | exact h
      | exact absurd (PLift.down f) (by decide)
      | (obtain ⟨rfl, rfl⟩ := h; exact Or.inl ⟨rfl, Or.inl rfl⟩)
      | (obtain ⟨rfl, rfl⟩ := h; exact Or.inl ⟨rfl, Or.inr rfl⟩)
  lab := fun _ _ => none
  lab_act := fun _ _ => rfl

def exU : ∀ c, exN c
  | .l => false
  | .r => false
  | .t => Top4.u

/-- The object `u`, which is global. -/
def uGlob : Glob cosp (Lab.pure cosp) :=
  ⟨fun c => dec exSys c (exU c), by
    intro c d f
    cases c <;> cases d <;>
      first
        | rfl
        | exact absurd (PLift.down f) (by decide)⟩

/-- In every context, `u` has a member … -/
theorem ex_inhabited (c : Cosp) : ∃ v, U.Mem v (uGlob.1 c) := by
  cases c
  · exact ⟨dec exSys .l true, (dec_solves exSys .l false _).2 ⟨true, ⟨rfl, rfl⟩, rfl⟩⟩
  · exact ⟨dec exSys .r true, (dec_solves exSys .r false _).2 ⟨true, ⟨rfl, rfl⟩, rfl⟩⟩
  · exact ⟨dec exSys .t Top4.a,
      (dec_solves exSys .t Top4.u _).2 ⟨Top4.a, Or.inl ⟨rfl, Or.inl rfl⟩, rfl⟩⟩

/-- … but **no global member**: the members found in `l` and in `r` become
    different in their common refinement.  Existence is local. -/
theorem ex_no_global_member :
    ¬ ∃ v : Glob cosp (Lab.pure cosp), ∀ c, U.Mem (v.1 c) (uGlob.1 c) := by
  rintro ⟨⟨v, hv⟩, hmem⟩
  obtain ⟨zl, hzl, hl⟩ := (dec_solves exSys .l false (v .l)).1 (hmem .l)
  obtain ⟨zr, hzr, hr⟩ := (dec_solves exSys .r false (v .r)).1 (hmem .r)
  obtain ⟨-, rfl⟩ := hzl
  obtain ⟨-, rfl⟩ := hzr
  have e1 : v .t = dec exSys .t Top4.a := by
    rw [← @hv .l .t (PLift.up (Or.inr rfl)), ← hl]
    rfl
  have e2 : v .t = dec exSys .t Top4.b := by
    rw [← @hv .r .t (PLift.up (Or.inr rfl)), ← hr]
    rfl
  obtain ⟨S, hS, hs⟩ := Quotient.exact (e1.symm.trans e2)
  obtain ⟨x', hx', -⟩ := (hS.2.2 .t Top4.a Top4.b hs).2 Top4.e (Or.inr ⟨rfl, rfl⟩)
  rcases hx' with ⟨h, -⟩ | ⟨h, -⟩ <;> exact Top4.noConfusion h

/-- The single context. -/
def pointCtx : Ctx :=
  Ctx.ofPreorder Unit (fun _ _ => True) (fun _ => trivial) (fun _ _ => trivial)

/-- **With a single context, local is global**: every object is carried into itself,
    so every member is a global member. -/
theorem point_local_is_global {Λ : Lab pointCtx} (f : pointCtx.Hom () ())
    (u : U pointCtx Λ ()) : U.act f u = u := by
  have hf : f = pointCtx.id () := rfl
  rw [hf]
  exact U.act_id (K := pointCtx) () u

/-! ## 4. Pure sets carry no symmetry -/

/-- A group, written out. -/
structure Grp where
  G : Type
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  inv_mul : ∀ a, mul (inv a) a = one
  mul_inv : ∀ a, mul a (inv a) = one

/-- A group of symmetries as a context structure: one context; an arrow is a
    symmetry.  "First `f`, then `g`" is `g * f`. -/
def Ctx.ofGroup (Γ : Grp) : Ctx where
  C := Unit
  Hom := fun _ _ => Γ.G
  id := fun _ => Γ.one
  comp := fun f g => Γ.mul g f
  id_comp := fun f => Γ.mul_one f
  comp_id := fun f => Γ.one_mul f
  assoc := fun f g h => (Γ.mul_assoc h g f).symm

/-- The action of a symmetry on the nodes of a system over a group. -/
def gact {Γ : Grp} {Λ : Lab (Ctx.ofGroup Γ)} (G : CSys (Ctx.ofGroup Γ) Λ) (g : Γ.G)
    (x : G.N ()) : G.N () :=
  G.act (c := ()) (d := ()) g x

theorem gact_mul {Γ : Grp} {Λ : Lab (Ctx.ofGroup Γ)} (G : CSys (Ctx.ofGroup Γ) Λ)
    (g h : Γ.G) (x : G.N ()) : gact G (Γ.mul g h) x = gact G g (gact G h x) :=
  G.act_comp (a := ()) (b := ()) (c := ()) h g x

theorem gact_one {Γ : Grp} {Λ : Lab (Ctx.ofGroup Γ)} (G : CSys (Ctx.ofGroup Γ) Λ)
    (x : G.N ()) : gact G Γ.one x = x :=
  G.act_id () x

theorem gact_mono {Γ : Grp} {Λ : Lab (Ctx.ofGroup Γ)} (G : CSys (Ctx.ofGroup Γ) Λ) (g : Γ.G)
    {z x : G.N ()} (h : G.R () z x) : G.R () (gact G g z) (gact G g x) :=
  G.mono (c := ()) (d := ()) g h

/-- **In a pure system, objects in one orbit are bisimilar**: the orbit relation
    persists along the symmetries and matches members. -/
theorem symmetry_collapses {Γ : Grp} {Λ : Lab (Ctx.ofGroup Γ)} (G : CSys (Ctx.ofGroup Γ) Λ)
    (hG : G.Pure) (g : Γ.G) (y : G.N ()) : dec G () y = dec G () (gact G g y) := by
  apply Quotient.sound
  refine ⟨fun _ n m => ∃ h : Γ.G, m = gact G h n, ⟨?_, ?_, ?_⟩, ⟨g, rfl⟩⟩
  · intro c d k n m hnm
    cases c
    cases d
    obtain ⟨h, rfl⟩ := hnm
    refine ⟨Γ.mul (Γ.mul k h) (Γ.inv k), ?_⟩
    have e : ∀ k' : Γ.G, gact G k' (gact G h n) =
        gact G (Γ.mul (Γ.mul k' h) (Γ.inv k')) (gact G k' n) := by
      intro k'
      rw [← gact_mul, ← gact_mul, Γ.mul_assoc (Γ.mul k' h) (Γ.inv k') k', Γ.inv_mul k',
        Γ.mul_one (Γ.mul k' h)]
    exact e k
  · intro c n m hnm
    cases c
    obtain ⟨h, rfl⟩ := hnm
    exact (hG () n).trans (hG () _).symm
  · intro c n m hnm
    cases c
    obtain ⟨h, rfl⟩ := hnm
    constructor
    · intro n' hn'
      exact ⟨gact G h n', gact_mono G h hn', h, rfl⟩
    · intro m' hm'
      refine ⟨gact G (Γ.inv h) m', ?_, h, ?_⟩
      · have := gact_mono G (Γ.inv h) hm'
        rwa [← gact_mul, Γ.inv_mul, gact_one] at this
      · rw [← gact_mul, Γ.mul_inv, gact_one]

/-- Without names every system is pure. -/
theorem pure_of_no_names {K : Ctx} (G : CSys K (Lab.pure K)) : G.Pure := by
  intro c x
  cases h : G.lab c x with
  | none => rfl
  | some e => exact Empty.elim e

/-- **Pure sets carry no symmetry**: over a group of symmetries, with no names,
    every object of the kind is fixed by every symmetry — every object is global. -/
theorem kind_all_fixed {Γ : Grp} (g : Γ.G) (u : U (Ctx.ofGroup Γ) (Lab.pure _) ()) :
    U.act (K := Ctx.ofGroup Γ) (c := ()) (d := ()) g u = u := by
  refine Quotient.ind
    (motive := fun u => U.act (K := Ctx.ofGroup Γ) (c := ()) (d := ()) g u = u) (fun p => ?_) u
  exact (symmetry_collapses p.sys (pure_of_no_names p.sys) g p.pt).symm

/-! ## 5. Names carry symmetry: Russell's socks, in the kind -/

/-- The group of order two: `true` swaps. -/
def z2 : Grp where
  G := Bool
  mul := xor
  one := false
  inv := id
  mul_assoc := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  one_mul := fun a => by cases a <;> rfl
  mul_one := fun a => by cases a <;> rfl
  inv_mul := fun a => by cases a <;> rfl
  mul_inv := fun a => by cases a <;> rfl

def socksCtx : Ctx := Ctx.ofGroup z2

/-- Two socks, named `false` and `true`; the swap exchanges their names. -/
def socksLab : Lab socksCtx := ⟨fun _ => Bool, fun g b => xor g b⟩

/-- The system: `none` is the pair, `some b` is the sock named `b`. -/
def socks : CSys socksCtx socksLab where
  N := fun _ => Option Bool
  act := fun g x => x.map (xor g)
  act_id := fun _ x => by
    cases x with
    | none => rfl
    | some b => cases b <;> rfl
  act_comp := fun f g x => by
    cases x with
    | none => rfl
    | some b => cases f <;> cases g <;> cases b <;> rfl
  R := fun _ z x => x = none ∧ z ≠ none
  mono := fun {_c _d} g {z x} h => by
    obtain ⟨hx, hz⟩ := h
    subst hx
    refine ⟨rfl, ?_⟩
    cases z with
    | none => exact absurd rfl hz
    | some b => exact Option.some_ne_none _
  lab := fun _ x => x
  lab_act := fun _ _ => rfl

/-- The pair of socks. -/
def pair : U socksCtx socksLab () := dec socks () none

/-- The pair is global: the swap carries it to itself … -/
theorem pair_global (g : Bool) : U.act (K := socksCtx) (c := ()) (d := ()) g pair = pair := rfl

/-- … and it has a member … -/
theorem pair_inhabited : U.Mem (dec socks () (some true)) pair :=
  (dec_solves socks () none _).2 ⟨some true, ⟨rfl, Option.some_ne_none _⟩, rfl⟩

/-- … but the swap moves each sock: its name changes. -/
theorem sock_moved (b : Bool) :
    U.act (K := socksCtx) (c := ()) (d := ()) true (dec socks () (some b)) ≠
      dec socks () (some b) := by
  intro h
  have h' : (some (xor true b) : Option Bool) = some b := congrArg U.lab h
  cases b <;> exact absurd (Option.some.inj h') (by decide)

/-- **Russell's socks, in the kind**: the pair is global and has members, but no
    member is global — no sock can be picked in a way every symmetry respects.
    The symmetric form of "existence is local". -/
theorem no_global_sock :
    ¬ ∃ v, U.Mem v pair ∧ ∀ g : Bool, U.act (K := socksCtx) (c := ()) (d := ()) g v = v := by
  rintro ⟨v, hv, hfix⟩
  obtain ⟨z, ⟨-, hz⟩, rfl⟩ := (dec_solves socks () none v).1 hv
  cases z with
  | none => exact hz rfl
  | some b => exact sock_moved b (hfix true)

/-! ## 6. When local members glue: a root, or choice over disjoint contexts -/

/-- **With a root, existence is global**: over a preorder of contexts with a least
    context, a global object with a member in the root has a global member — the
    root's member, carried everywhere.  No choice is used: the root is a global
    context. -/
theorem rooted_glue {C : Type} {le : C → C → Prop} {refl : ∀ c, le c c}
    {trans : ∀ {a b c}, le a b → le b c → le a c} {Λ : Lab (Ctx.ofPreorder C le refl trans)}
    (c₀ : C) (h₀ : ∀ c, le c₀ c) (u : Glob (Ctx.ofPreorder C le refl trans) Λ)
    (hu : ∃ v, U.Mem v (u.1 c₀)) :
    ∃ w : Glob (Ctx.ofPreorder C le refl trans) Λ, ∀ c, U.Mem (w.1 c) (u.1 c) := by
  obtain ⟨v, hv⟩ := hu
  refine ⟨⟨fun c => U.act (K := Ctx.ofPreorder C le refl trans) (⟨h₀ c⟩ : PLift (le c₀ c)) v,
    ?_⟩, ?_⟩
  · intro c d f
    exact (U.act_comp (K := Ctx.ofPreorder C le refl trans) (⟨h₀ c⟩ : PLift (le c₀ c)) f v).symm
  · intro c
    have := U.mem_act (K := Ctx.ofPreorder C le refl trans) (⟨h₀ c⟩ : PLift (le c₀ c)) hv
    exact Eq.mp (congrArg (U.Mem (U.act (K := Ctx.ofPreorder C le refl trans)
      (⟨h₀ c⟩ : PLift (le c₀ c)) v)) (u.2 (⟨h₀ c⟩ : PLift (le c₀ c)))) this

/-- Contexts with no arrows between distinct ones. -/
def Ctx.discrete (C : Type) : Ctx :=
  Ctx.ofPreorder C (fun a b => a = b) (fun _ => rfl) (fun h1 h2 => h1.trans h2)

/-- **Over disjoint contexts, choice glues local members**: a global object with a
    member in every context has a global member — one chosen in each context.  This
    uses choice: the non-unique gluing of the origin, transported. -/
theorem discrete_glue {C : Type} {Λ : Lab (Ctx.discrete C)} (u : Glob (Ctx.discrete C) Λ)
    (hu : ∀ c, ∃ v, U.Mem v (u.1 c)) :
    ∃ w : Glob (Ctx.discrete C) Λ, ∀ c, U.Mem (w.1 c) (u.1 c) := by
  refine ⟨⟨fun c => Classical.choose (hu c), ?_⟩, fun c => Classical.choose_spec (hu c)⟩
  intro c d f
  cases f with
  | up h =>
    subst h
    exact U.act_id (K := Ctx.discrete C) c _

/-! ## 7. The origin is also a shadow: looking at one context -/

/-- The names of context `c`, as names over the single context. -/
def Lab.at {K : Ctx} (Λ : Lab K) (c : K.C) : Lab pointCtx := ⟨fun _ => Λ.L c, fun _ l => l⟩

/-- A system seen only in context `c`. -/
def CSys.at {K : Ctx} {Λ : Lab K} (G : CSys K Λ) (c : K.C) : CSys pointCtx (Λ.at c) where
  N := fun _ => G.N c
  act := fun _ x => x
  act_id := fun _ _ => rfl
  act_comp := fun _ _ _ => rfl
  R := fun _ => G.R c
  mono := fun {_c _d} _ {_z _x} h => h
  lab := fun _ => G.lab c
  lab_act := fun {_c _d} _ x => by
    show G.lab c x = (G.lab c x).map (fun l => l)
    cases G.lab c x <;> rfl

/-- Look at an object of the kind only in context `c`: forget the refinements and
    symmetries, keep the members and names there. -/
def U.eval {K : Ctx} {Λ : Lab K} (c : K.C) : U K Λ c → U pointCtx (Λ.at c) () :=
  Quotient.lift (fun p => U.mk (⟨p.sys.at c, p.pt⟩ : Pt pointCtx (Λ.at c) ()))
    (fun _ _ h => by
      obtain ⟨S, hS, hs⟩ := h
      apply Quotient.sound
      exact ⟨fun _ => S c, ⟨fun {_c _d} _ {_x _y} h => h, fun _ x y h => hS.2.1 c x y h,
        fun _ x y h => hS.2.2 c x y h⟩, hs⟩)

/-- Looking at one context sends the solution of a system to the solution of what
    the system says there. -/
theorem U.eval_dec {K : Ctx} {Λ : Lab K} (G : CSys K Λ) (c : K.C) (x : G.N c) :
    U.eval c (dec G c x) = dec (G.at c) () x := rfl

/-- Looking at one context keeps membership there … -/
theorem U.eval_mem {K : Ctx} {Λ : Lab K} {c : K.C} {a b : U K Λ c} (h : U.Mem a b) :
    U.Mem (U.eval c a) (U.eval c b) := by
  revert h
  refine Quotient.ind₂ (motive := fun a b => U.Mem a b → U.Mem (U.eval c a) (U.eval c b))
    (fun p q => ?_) a b
  rintro ⟨m, hm, S, hS, hs⟩
  exact ⟨m, hm, fun _ => S c, ⟨fun {_c _d} _ {_x _y} h => h, fun _ x y h => hS.2.1 c x y h,
    fun _ x y h => hS.2.2 c x y h⟩, hs⟩

/-- … and names. -/
theorem U.eval_lab {K : Ctx} {Λ : Lab K} {c : K.C} (u : U K Λ c) :
    U.lab (U.eval c u) = U.lab u := by
  refine Quotient.ind (motive := fun u => U.lab (U.eval c u) = U.lab u) (fun p => ?_) u
  rfl

/-- **Along the contexts, the classical origin is a retract of every kind**: hold a
    plain system constant over the contexts, then look at one context — the plain
    object comes back unchanged.  (Along the shapes there is no such shadow:
    `Shapes.UA.no_wf_shadow`.) -/
theorem U.eval_const {K : Ctx} {Λ : Lab K} (c : K.C) {A : Type} (R : A → A → Prop) (x : A) :
    U.eval c (dec (const K Λ A R) c x) = dec (const pointCtx (Λ.at c) A R) () x := rfl

/-! ## 8. The criterion over a preorder of contexts -/

/-- **With a system of roots, existence is global** (uses choice): if each context
    has a root below it, and roots do not change along arrows, then a global object
    with a member in every context has a global member — a member chosen at each
    root, carried along.  One root needs no choice (`rooted_glue`); over disjoint
    contexts the roots are the contexts themselves (`discrete_glue`). -/
theorem roots_glue {C : Type} {le : C → C → Prop} {refl : ∀ c, le c c}
    {trans : ∀ {a b c}, le a b → le b c → le a c} {Λ : Lab (Ctx.ofPreorder C le refl trans)}
    (ρ : C → C) (h₁ : ∀ c, le (ρ c) c) (h₂ : ∀ c d, le c d → ρ c = ρ d)
    (u : Glob (Ctx.ofPreorder C le refl trans) Λ) (hu : ∀ c, ∃ v, U.Mem v (u.1 c)) :
    ∃ w : Glob (Ctx.ofPreorder C le refl trans) Λ, ∀ c, U.Mem (w.1 c) (u.1 c) := by
  let v : ∀ r : C, U (Ctx.ofPreorder C le refl trans) Λ r := fun r => Classical.choose (hu r)
  have hv : ∀ r, U.Mem (v r) (u.1 r) := fun r => Classical.choose_spec (hu r)
  have key : ∀ {a b d : C} (_ : a = b) (p : PLift (le a d)) (q : PLift (le b d)),
      U.act (K := Ctx.ofPreorder C le refl trans) p (v a) =
        U.act (K := Ctx.ofPreorder C le refl trans) q (v b) := by
    intro a b d e p q
    subst e
    cases p
    cases q
    rfl
  refine ⟨⟨fun c => U.act (K := Ctx.ofPreorder C le refl trans)
    (⟨h₁ c⟩ : PLift (le (ρ c) c)) (v (ρ c)), ?_⟩, fun c => ?_⟩
  · intro c d f
    exact (U.act_comp (K := Ctx.ofPreorder C le refl trans) (⟨h₁ c⟩ : PLift (le (ρ c) c)) f
      (v (ρ c))).symm.trans (key (h₂ c d (PLift.down f)) _ _)
  · have := U.mem_act (K := Ctx.ofPreorder C le refl trans) (⟨h₁ c⟩ : PLift (le (ρ c) c))
      (hv (ρ c))
    exact Eq.mp (congrArg (U.Mem (U.act (K := Ctx.ofPreorder C le refl trans)
      (⟨h₁ c⟩ : PLift (le (ρ c) c)) (v (ρ c)))) (u.2 (⟨h₁ c⟩ : PLift (le (ρ c) c)))) this

/-- Names for the criterion: every context can name every context, and names do
    not change along arrows. -/
def critLab (C : Type) (le : C → C → Prop) (refl : ∀ c, le c c)
    (trans : ∀ {a b c}, le a b → le b c → le a c) : Lab (Ctx.ofPreorder C le refl trans) :=
  ⟨fun _ => C, fun _ d => d⟩

/-- In context `c`: a top node, whose members are atoms named by the contexts
    below `c`. -/
def critSys (C : Type) (le : C → C → Prop) (refl : ∀ c, le c c)
    (trans : ∀ {a b c}, le a b → le b c → le a c) :
    CSys (Ctx.ofPreorder C le refl trans) (critLab C le refl trans) where
  N := fun c => Option {d : C // le d c}
  act := fun {_c _d} f x => x.map (fun e => ⟨e.1, trans e.2 (PLift.down f)⟩)
  act_id := fun _ x => by cases x <;> rfl
  act_comp := fun {_a _b _c} _ _ x => by cases x <;> rfl
  R := fun _ z x => x = none ∧ z ≠ none
  mono := fun {_c _d} _ {z _x} h => ⟨by rw [h.1]; rfl, by
    cases z with
    | none => exact absurd rfl h.2
    | some _ => exact Option.some_ne_none _⟩
  lab := fun _ x => x.map Subtype.val
  lab_act := fun {_c _d} _ x => by cases x <;> rfl

/-- The top node, in every context: a global object. -/
def critObj (C : Type) (le : C → C → Prop) (refl : ∀ c, le c c)
    (trans : ∀ {a b c}, le a b → le b c → le a c) :
    Glob (Ctx.ofPreorder C le refl trans) (critLab C le refl trans) :=
  ⟨fun c => dec (critSys C le refl trans) c none, fun _ => rfl⟩

/-- In every context it has a member: the atom named by the context itself. -/
theorem critObj_inhabited (C : Type) (le : C → C → Prop) (refl : ∀ c, le c c)
    (trans : ∀ {a b c}, le a b → le b c → le a c) (c : C) :
    ∃ v, U.Mem v ((critObj C le refl trans).1 c) :=
  ⟨dec (critSys C le refl trans) c (some ⟨c, refl c⟩),
    (dec_solves (critSys C le refl trans) c none _).2
      ⟨some ⟨c, refl c⟩, ⟨rfl, Option.some_ne_none _⟩, rfl⟩⟩

/-- **Without a system of roots, existence is local**: if the global object above
    has a global member, then each context has a root below it that does not
    change along arrows — read off the member's name, with no choice. -/
theorem roots_of_glue (C : Type) (le : C → C → Prop) (refl : ∀ c, le c c)
    (trans : ∀ {a b c}, le a b → le b c → le a c)
    (h : ∃ w : Glob (Ctx.ofPreorder C le refl trans) (critLab C le refl trans),
      ∀ c, U.Mem (w.1 c) ((critObj C le refl trans).1 c)) :
    ∃ ρ : C → C, (∀ c, le (ρ c) c) ∧ ∀ c d, le c d → ρ c = ρ d := by
  obtain ⟨w, hw⟩ := h
  have name : ∀ c, ∃ d, le d c ∧ U.lab (w.1 c) = some d := by
    intro c
    obtain ⟨z, ⟨_, hz⟩, hzw⟩ := (dec_solves (critSys C le refl trans) c none (w.1 c)).1 (hw c)
    cases z with
    | none => exact absurd rfl hz
    | some d => exact ⟨d.1, d.2, by rw [← hzw]; rfl⟩
  refine ⟨fun c => (U.lab (w.1 c)).getD c, fun c => ?_, fun c d hcd => ?_⟩
  · obtain ⟨d, hd, e⟩ := name c
    show le ((U.lab (w.1 c)).getD c) c
    rw [e]
    exact hd
  · have e3 : U.lab (w.1 d) = (U.lab (w.1 c)).map
        ((critLab C le refl trans).lact (⟨hcd⟩ : PLift (le c d))) :=
      (congrArg U.lab (w.2 (⟨hcd⟩ : PLift (le c d)))).symm.trans
        (U.lab_act (K := Ctx.ofPreorder C le refl trans) (⟨hcd⟩ : PLift (le c d)) (w.1 c))
    show (U.lab (w.1 c)).getD c = (U.lab (w.1 d)).getD d
    rw [e3]
    obtain ⟨d', _, e⟩ := name c
    rw [e]
    rfl

/-- **The criterion over a preorder of contexts**: local existence always glues —
    for every global object, with any names — exactly when each context has a root
    below it that does not change along arrows, that is, when every connected
    component has a least context.  Choice is used only to pick across roots. -/
theorem criterion (C : Type) (le : C → C → Prop) (refl : ∀ c, le c c)
    (trans : ∀ {a b c}, le a b → le b c → le a c) :
    (∀ (Λ : Lab (Ctx.ofPreorder C le refl trans)) (u : Glob (Ctx.ofPreorder C le refl trans) Λ),
      (∀ c, ∃ v, U.Mem v (u.1 c)) →
        ∃ w : Glob (Ctx.ofPreorder C le refl trans) Λ, ∀ c, U.Mem (w.1 c) (u.1 c)) ↔
    ∃ ρ : C → C, (∀ c, le (ρ c) c) ∧ ∀ c d, le c d → ρ c = ρ d :=
  ⟨fun h => roots_of_glue C le refl trans
      (h _ (critObj C le refl trans) (critObj_inhabited C le refl trans)),
    fun ⟨ρ, h₁, h₂⟩ _ u hu => roots_glue ρ h₁ h₂ u hu⟩

/-! ## 9. The criterion over any structure of contexts -/

/-- An arrow into `c`, from some context. -/
def Into (K : Ctx) (c : K.C) : Type := Σ a : K.C, K.Hom a c

/-- A chosen arrow into every context, such that following any arrow afterwards gives
    the arrow chosen for its target.  Over a preorder: a root below every context,
    unchanged along arrows.  Over a group: only the trivial group has one. -/
def Cones (K : Ctx) : Prop :=
  ∃ g : ∀ c, Into K c, ∀ {c d} (f : K.Hom c d), (⟨(g c).1, K.comp (g c).2 f⟩ : Into K d) = g d

/-- **With chosen arrows, existence is global** (uses choice): pick a member at the
    source of each chosen arrow and carry it along. -/
theorem cones_glue {K : Ctx} {Λ : Lab K} (hK : Cones K) (u : Glob K Λ)
    (hu : ∀ c, ∃ v, U.Mem v (u.1 c)) : ∃ w : Glob K Λ, ∀ c, U.Mem (w.1 c) (u.1 c) := by
  obtain ⟨g, hg⟩ := hK
  let v : ∀ r : K.C, U K Λ r := fun r => Classical.choose (hu r)
  have hv : ∀ r, U.Mem (v r) (u.1 r) := fun r => Classical.choose_spec (hu r)
  let F : ∀ d, Into K d → U K Λ d := fun _ p => U.act p.2 (v p.1)
  refine ⟨⟨fun c => F c (g c), fun {c d} f => ?_⟩, fun c => ?_⟩
  · show U.act f (U.act (g c).2 (v (g c).1)) = F d (g d)
    rw [← U.act_comp]
    exact congrArg (F d) (hg f)
  · have := U.mem_act (g c).2 (hv (g c).1)
    exact Eq.mp (congrArg (U.Mem (U.act (g c).2 (v (g c).1))) (u.2 (g c).2)) this

/-- Names for the general criterion: the arrows into a context, carried along by
    following arrows afterwards. -/
def coneLab (K : Ctx) : Lab K := ⟨fun c => Into K c, fun f p => ⟨p.1, K.comp p.2 f⟩⟩

/-- In context `c`: a top node, whose members are atoms named by the arrows into `c`. -/
def coneSys (K : Ctx) : CSys K (coneLab K) where
  N := fun c => Option (Into K c)
  act := fun {_c _d} f x => x.map (fun p => ⟨p.1, K.comp p.2 f⟩)
  act_id := fun c x => by
    cases x with
    | none => rfl
    | some p =>
      obtain ⟨a, h⟩ := p
      show some (⟨a, K.comp h (K.id c)⟩ : Into K c) = some ⟨a, h⟩
      rw [K.comp_id]
  act_comp := fun {_a _b _c} f g x => by
    cases x with
    | none => rfl
    | some p =>
      show some (⟨p.1, K.comp p.2 (K.comp f g)⟩ : Into K _) = some ⟨p.1, K.comp (K.comp p.2 f) g⟩
      rw [K.assoc]
  R := fun _ z x => x = none ∧ z ≠ none
  mono := fun {_c _d} _ {z _x} h => ⟨by rw [h.1]; rfl, by
    cases z with
    | none => exact absurd rfl h.2
    | some _ => exact Option.some_ne_none _⟩
  lab := fun _ x => x
  lab_act := fun {_c _d} _ x => by cases x <;> rfl

/-- The top node, in every context: a global object. -/
def coneObj (K : Ctx) : Glob K (coneLab K) := ⟨fun c => dec (coneSys K) c none, fun _ => rfl⟩

theorem coneObj_inhabited (K : Ctx) (c : K.C) : ∃ v, U.Mem v ((coneObj K).1 c) :=
  ⟨dec (coneSys K) c (some ⟨c, K.id c⟩),
    (dec_solves (coneSys K) c none _).2 ⟨some ⟨c, K.id c⟩, ⟨rfl, Option.some_ne_none _⟩, rfl⟩⟩

/-- **Without chosen arrows, existence is local**: a global member of the object above
    names, in each context, an arrow into it; these names are the chosen arrows.  No
    choice is used. -/
theorem cones_of_glue (K : Ctx)
    (h : ∃ w : Glob K (coneLab K), ∀ c, U.Mem (w.1 c) ((coneObj K).1 c)) : Cones K := by
  obtain ⟨w, hw⟩ := h
  have name : ∀ c, ∃ p : Into K c, U.lab (w.1 c) = some p := by
    intro c
    obtain ⟨z, ⟨_, hz⟩, hzw⟩ := (dec_solves (coneSys K) c none (w.1 c)).1 (hw c)
    cases z with
    | none => exact absurd rfl hz
    | some p => exact ⟨p, by rw [← hzw]; rfl⟩
  refine ⟨fun c => (U.lab (w.1 c)).getD ⟨c, K.id c⟩, fun {c d} f => ?_⟩
  have e3 : U.lab (w.1 d) = (U.lab (w.1 c)).map ((coneLab K).lact f) :=
    (congrArg U.lab (w.2 f)).symm.trans (U.lab_act f (w.1 c))
  show (⟨((U.lab (w.1 c)).getD ⟨c, K.id c⟩).1,
      K.comp ((U.lab (w.1 c)).getD ⟨c, K.id c⟩).2 f⟩ : Into K d) =
    (U.lab (w.1 d)).getD ⟨d, K.id d⟩
  rw [e3]
  obtain ⟨p, e⟩ := name c
  rw [e]
  rfl

/-- **The criterion over any structure of contexts**: local existence always glues —
    for every global object, with any names — exactly when there is a chosen arrow
    into every context, compatible with all arrows.  Choice is used only to pick a
    member at the sources of the chosen arrows. -/
theorem criterion_general (K : Ctx) :
    (∀ (Λ : Lab K) (u : Glob K Λ), (∀ c, ∃ v, U.Mem v (u.1 c)) →
      ∃ w : Glob K Λ, ∀ c, U.Mem (w.1 c) (u.1 c)) ↔ Cones K :=
  ⟨fun h => cones_of_glue K (h _ (coneObj K) (coneObj_inhabited K)),
    fun hK _ u hu => cones_glue hK u hu⟩

/-- **With symmetry, local existence always glues only when there is no symmetry**:
    over a group, chosen arrows exist exactly when the group is trivial. -/
theorem cones_group_iff (Γ : Grp) : Cones (Ctx.ofGroup Γ) ↔ ∀ g : Γ.G, g = Γ.one := by
  have cancel : ∀ f γ : Γ.G, Γ.mul f γ = γ → f = Γ.one := by
    intro f γ h
    calc f = Γ.mul f Γ.one := (Γ.mul_one f).symm
      _ = Γ.mul f (Γ.mul γ (Γ.inv γ)) := by rw [Γ.mul_inv]
      _ = Γ.mul (Γ.mul f γ) (Γ.inv γ) := (Γ.mul_assoc _ _ _).symm
      _ = Γ.mul γ (Γ.inv γ) := by rw [h]
      _ = Γ.one := Γ.mul_inv _
  constructor
  · rintro ⟨g, hg⟩ f
    have h1 : (⟨(g ()).1, Γ.mul f (g ()).2⟩ : Into (Ctx.ofGroup Γ) ()) = g () := hg (c := ()) (d := ()) f
    exact cancel f (g ()).2 (congrArg Sigma.snd h1)
  · intro htriv
    refine ⟨fun _ => ⟨(), Γ.one⟩, fun {c d} f => ?_⟩
    cases c
    cases d
    show (⟨(), Γ.mul f Γ.one⟩ : Into (Ctx.ofGroup Γ) ()) = ⟨(), Γ.one⟩
    rw [htriv f, Γ.mul_one]

end PZFC.Kinds
