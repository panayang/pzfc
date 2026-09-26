/-
  One construction, the value a parameter (notes/34, notes/35).  Mathlib-free.

  A value structure says what an answer is and how "one of a family" aggregates:
  sharp answers aggregate by `∃`, weights by `∑'` (the weights live in the mathlib
  part, `lean-mathlib/WeightedKind.lean`).  It is complete when the aggregate does not
  depend on how the family is indexed, is the value itself on one element, and can
  be taken block by block.

  §1  complete value structures; sharp answers are an instance;
  §2  systems, and solutions of one system in another — the maps keeping the
      aggregate.  They compose, and two solutions out of one system can be glued;
  §3  the kind over any complete value structure: pointed systems, identified
      when some solutions send them to one node.  GLU holds — every system has
      exactly one solution, every object is the value of one — and identity is
      having a common image.  GLU uses `Quot.sound` only;
  §4  maps between value structures give maps between kinds — shadows — which
      send solutions to solutions, functorially;
  §5  the sharp instance: a common image exists exactly when there is a
      bisimulation.  (`Instances.lean`: it is the shape extension of `Shapes`.);
  §6  identity as a relation, for every complete value structure: two nodes are
      the same object exactly when a Larsen–Skou bisimulation relates them — an
      equivalence under which related nodes answer with the same value into
      every class.
-/

namespace PZFC.Values

universe u

/-! ## 1. Complete value structures -/

/-- A bijection, written out. -/
structure Iso (α β : Type) where
  to : α → β
  inv : β → α
  inv_to : ∀ a, inv (to a) = a
  to_inv : ∀ b, to (inv b) = b

/-- A complete value structure: values, and the aggregate of a family of values. -/
structure CVal where
  W : Type
  agg : {ι : Type} → (ι → W) → W
  agg_iso : ∀ {ι κ : Type} (e : Iso ι κ) (f : κ → W), agg (fun i => f (e.to i)) = agg f
  agg_unit : ∀ w : W, agg (fun _ : Unit => w) = w
  agg_sigma : ∀ {ι : Type} {κ : ι → Type} (f : (i : ι) → κ i → W),
    agg (fun p : (Σ i, κ i) => f p.1 p.2) = agg (fun i => agg (f i))

/-- Sharp answers: the family says yes when one of it does. -/
abbrev sharp : CVal where
  W := Prop
  agg f := ∃ i, f i
  agg_iso e f := propext ⟨fun ⟨i, h⟩ => ⟨e.to i, h⟩,
    fun ⟨k, h⟩ => ⟨e.inv k, show f (e.to (e.inv k)) by rw [e.to_inv]; exact h⟩⟩
  agg_unit _ := propext ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩
  agg_sigma _ := propext ⟨fun ⟨⟨i, k⟩, h⟩ => ⟨i, k, h⟩, fun ⟨i, k, h⟩ => ⟨⟨i, k⟩, h⟩⟩

variable {V : CVal}

theorem CVal.agg_congr (V : CVal) {ι : Type} {f g : ι → V.W} (h : ∀ i, f i = g i) :
    V.agg f = V.agg g :=
  congrArg V.agg (funext h)

/-- Aggregating over the single element `b`. -/
theorem CVal.agg_single (V : CVal) {A : Type} (b : A) (f : A → V.W) :
    V.agg (fun z : {z // z = b} => f z.1) = f b := by
  let e : Iso Unit {z : A // z = b} :=
    ⟨fun _ => ⟨b, rfl⟩, fun _ => (), fun _ => rfl, by rintro ⟨_, rfl⟩; rfl⟩
  calc V.agg (fun z : {z // z = b} => f z.1)
      = V.agg (fun i : Unit => f (e.to i).1) := (V.agg_iso e (fun z => f z.1)).symm
    _ = f b := V.agg_unit (f b)

/-- Re-indexing along equivalent conditions. -/
theorem CVal.agg_iff (V : CVal) {A : Type} (P Q : A → Prop) (h : ∀ a, P a ↔ Q a)
    (f : A → V.W) :
    V.agg (fun z : {z // P z} => f z.1) = V.agg (fun z : {z // Q z} => f z.1) :=
  V.agg_iso (⟨fun z => ⟨z.1, (h z.1).1 z.2⟩, fun z => ⟨z.1, (h z.1).2 z.2⟩,
    fun _ => rfl, fun _ => rfl⟩ : Iso {z // P z} {z // Q z}) (fun z : {z // Q z} => f z.1)

/-! ## 2. Systems and solutions -/

/-- A system: nodes, and the value with which `z` answers as a member of `x`. -/
structure Sys (V : CVal) where
  N : Type
  R : N → N → V.W

/-- `f` solves `G` in `H`: the value of `b` as a member of `f x` aggregates the
    members of `x` that land on `b`. -/
def Solves {V : CVal} (G H : Sys V) (f : G.N → H.N) : Prop :=
  ∀ x b, H.R b (f x) = V.agg (fun z : {z // f z = b} => G.R z.1 x)

theorem solves_id (G : Sys V) : Solves G G id :=
  fun x b => (V.agg_single b (fun z => G.R z x)).symm

/-- Aggregating along a solution: a condition on the image pulls back to the source. -/
theorem solves_fiber {G H : Sys V} {f : G.N → H.N} (hf : Solves G H f) {X : Type u}
    (q : H.N → X) (c : X) (x : G.N) :
    V.agg (fun y : {y // q y = c} => H.R y.1 (f x)) =
      V.agg (fun z : {z // q (f z) = c} => G.R z.1 x) := by
  let e : Iso (Σ y : {y // q y = c}, {z // f z = y.1}) {z // q (f z) = c} :=
    ⟨fun p => ⟨p.2.1, by rw [p.2.2]; exact p.1.2⟩,
     fun z => ⟨⟨f z.1, z.2⟩, ⟨z.1, rfl⟩⟩,
     by
       intro p
       obtain ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ := p
       change f z = y at hz
       subst hz
       rfl,
     fun _ => rfl⟩
  calc V.agg (fun y : {y // q y = c} => H.R y.1 (f x))
      = V.agg (fun y : {y // q y = c} => V.agg (fun z : {z // f z = y.1} => G.R z.1 x)) :=
        V.agg_congr (fun y => hf x y.1)
    _ = V.agg (fun p : (Σ y : {y // q y = c}, {z // f z = y.1}) => G.R p.2.1 x) :=
        (V.agg_sigma (fun (y : {y // q y = c}) (z : {z // f z = y.1}) => G.R z.1 x)).symm
    _ = V.agg (fun z : {z // q (f z) = c} => G.R z.1 x) :=
        V.agg_iso e (fun z => G.R z.1 x)

/-- Solutions compose. -/
theorem solves_comp {G H K : Sys V} {f : G.N → H.N} {g : H.N → K.N} (hf : Solves G H f)
    (hg : Solves H K g) : Solves G K (fun x => g (f x)) :=
  fun x c => (hg (f x) c).trans (solves_fiber hf g c x)

section Glue

variable {H K K' : Sys V} (f : H.N → K.N) (g : H.N → K'.N)

/-- Glue `K` and `K'` along the images of `H`. -/
def glueRel : K.N ⊕ K'.N → K.N ⊕ K'.N → Prop :=
  fun s t => ∃ h, s = .inl (f h) ∧ t = .inr (g h)

def glueN : Type := Quot (glueRel f g)

/-- The value of `c` as a member of a glued node, computed on either side. -/
def glueVal (c : glueN f g) : K.N ⊕ K'.N → V.W
  | .inl k => V.agg (fun k' : {k' : K.N // Quot.mk (glueRel f g) (.inl k') = c} => K.R k'.1 k)
  | .inr k => V.agg (fun k' : {k' : K'.N // Quot.mk (glueRel f g) (.inr k') = c} => K'.R k'.1 k)

variable {f g}

theorem glueVal_wd (hf : Solves H K f) (hg : Solves H K' g) (c : glueN f g) (h : H.N) :
    glueVal f g c (.inl (f h)) = glueVal f g c (.inr (g h)) :=
  calc V.agg (fun k' : {k' : K.N // Quot.mk (glueRel f g) (.inl k') = c} => K.R k'.1 (f h))
      = V.agg (fun n : {n : H.N // Quot.mk (glueRel f g) (.inl (f n)) = c} => H.R n.1 h) :=
        solves_fiber hf (fun k' => Quot.mk (glueRel f g) (.inl k')) c h
    _ = V.agg (fun n : {n : H.N // Quot.mk (glueRel f g) (.inr (g n)) = c} => H.R n.1 h) :=
        V.agg_iff (fun n => Quot.mk (glueRel f g) (.inl (f n)) = c)
          (fun n => Quot.mk (glueRel f g) (.inr (g n)) = c)
          (fun n => Iff.of_eq (congrArg (· = c)
            (Quot.sound (⟨n, rfl, rfl⟩ : glueRel f g (.inl (f n)) (.inr (g n))))))
          (fun n => H.R n h)
    _ = V.agg (fun k' : {k' : K'.N // Quot.mk (glueRel f g) (.inr k') = c} => K'.R k'.1 (g h)) :=
        (solves_fiber hg (fun k' => Quot.mk (glueRel f g) (.inr k')) c h).symm

/-- The glued system. -/
def glue (hf : Solves H K f) (hg : Solves H K' g) : Sys V where
  N := glueN f g
  R c := Quot.lift (glueVal f g c) (fun s t hst => by
    obtain ⟨h, rfl, rfl⟩ := hst
    exact glueVal_wd hf hg c h)

theorem solves_inl (hf : Solves H K f) (hg : Solves H K' g) :
    Solves K (glue hf hg) (fun k => Quot.mk (glueRel f g) (.inl k)) := fun _ _ => rfl

theorem solves_inr (hf : Solves H K f) (hg : Solves H K' g) :
    Solves K' (glue hf hg) (fun k => Quot.mk (glueRel f g) (.inr k)) := fun _ _ => rfl

end Glue

/-! ## 3. The kind -/

structure Pt (V : CVal) where
  sys : Sys V
  pt : sys.N

/-- Two pointed systems are identified when some solutions send them to one node. -/
def Pt.Same (p q : Pt V) : Prop :=
  ∃ (K : Sys V) (f : p.sys.N → K.N) (g : q.sys.N → K.N),
    Solves p.sys K f ∧ Solves q.sys K g ∧ f p.pt = g q.pt

theorem Pt.same_refl (p : Pt V) : p.Same p := ⟨p.sys, id, id, solves_id _, solves_id _, rfl⟩

theorem Pt.same_symm {p q : Pt V} (h : p.Same q) : q.Same p := by
  obtain ⟨K, f, g, hf, hg, e⟩ := h
  exact ⟨K, g, f, hg, hf, e.symm⟩

theorem Pt.same_trans {p q r : Pt V} (h1 : p.Same q) (h2 : q.Same r) : p.Same r := by
  obtain ⟨K, f, g, hf, hg, e⟩ := h1
  obtain ⟨K', g', k, hg', hk, e'⟩ := h2
  refine ⟨glue hg hg', fun x => Quot.mk (glueRel g g') (.inl (f x)),
    fun x => Quot.mk (glueRel g g') (.inr (k x)),
    solves_comp hf (solves_inl hg hg'), solves_comp hk (solves_inr hg hg'), ?_⟩
  show Quot.mk (glueRel g g') (.inl (f p.pt)) = Quot.mk (glueRel g g') (.inr (k r.pt))
  rw [e, ← e']
  exact Quot.sound ⟨q.pt, rfl, rfl⟩

instance Pt.setoid (V : CVal) : Setoid (Pt V) :=
  ⟨Pt.Same, ⟨Pt.same_refl, Pt.same_symm, Pt.same_trans⟩⟩

/-- The kind over `V`: all shapes, one context. -/
def UV (V : CVal) : Type 1 := Quotient (Pt.setoid V)

/-- The solution of a system: node `x` goes to the system pointed at `x`. -/
def dec (G : Sys V) (x : G.N) : UV V := Quotient.mk _ ⟨G, x⟩

/-- A node and its image under a solution are the same object. -/
theorem dec_image {G K : Sys V} {f : G.N → K.N} (hf : Solves G K f) (x : G.N) :
    dec G x = dec K (f x) :=
  Quotient.sound ⟨K, f, id, hf, solves_id K, rfl⟩

/-- The value with which `b` answers as a member of `a`. -/
def UV.E (b a : UV V) : V.W :=
  Quotient.lift (fun p : Pt V => V.agg (fun z : {z // dec p.sys z = b} => p.sys.R z.1 p.pt))
    (fun p q hpq => by
      obtain ⟨K, f, g, hf, hg, e⟩ := hpq
      calc V.agg (fun z : {z // dec p.sys z = b} => p.sys.R z.1 p.pt)
          = V.agg (fun z : {z // dec K (f z) = b} => p.sys.R z.1 p.pt) :=
            V.agg_iff (fun z => dec p.sys z = b) (fun z => dec K (f z) = b)
              (fun z => Iff.of_eq (congrArg (· = b) (dec_image hf z))) (fun z => p.sys.R z p.pt)
        _ = V.agg (fun y : {y // dec K y = b} => K.R y.1 (f p.pt)) :=
            (solves_fiber hf (dec K) b p.pt).symm
        _ = V.agg (fun y : {y // dec K y = b} => K.R y.1 (g q.pt)) := by rw [e]
        _ = V.agg (fun z : {z // dec K (g z) = b} => q.sys.R z.1 q.pt) :=
            solves_fiber hg (dec K) b q.pt
        _ = V.agg (fun z : {z // dec q.sys z = b} => q.sys.R z.1 q.pt) :=
            V.agg_iff (fun z => dec K (g z) = b) (fun z => dec q.sys z = b)
              (fun z => Iff.of_eq (congrArg (· = b) (dec_image hg z).symm))
              (fun z => q.sys.R z q.pt)) a

/-- In the kind, the members of the value of `x` are the values of the members of `x`. -/
theorem dec_solves (G : Sys V) (x : G.N) (b : UV V) :
    UV.E b (dec G x) = V.agg (fun z : {z // dec G z = b} => G.R z.1 x) := rfl

/-- `f` solves `G` in the kind. -/
def SolvesU (G : Sys V) (f : G.N → UV V) : Prop :=
  ∀ x b, UV.E b (f x) = V.agg (fun z : {z // f z = b} => G.R z.1 x)

theorem dec_solution (G : Sys V) : SolvesU G (dec G) := dec_solves G

/-- **Every solution in the kind is `dec`.**  The solution and a representative of
    its value are sent, as the objects they denote, into one small system. -/
theorem solution_unique (G : Sys V) {f : G.N → UV V} (hf : SolvesU G f) (x : G.N) :
    f x = dec G x := by
  obtain ⟨q, hq⟩ := Quotient.exists_rep (f x)
  let img : G.N ⊕ q.sys.N → UV V := fun s => Sum.elim f (dec q.sys) s
  let r : G.N ⊕ q.sys.N → G.N ⊕ q.sys.N → Prop := fun s t => img s = img t
  let img' : Quot r → UV V := Quot.lift img (fun _ _ h => h)
  have inj : ∀ d d' : Quot r, img' d = img' d' → d = d' := by
    intro d d'
    induction d using Quot.ind
    induction d' using Quot.ind
    exact fun h => Quot.sound h
  let K : Sys V := ⟨Quot r, fun d' d => UV.E (img' d') (img' d)⟩
  have hl : Solves G K (fun z => Quot.mk r (.inl z)) := by
    intro z d'
    show UV.E (img' d') (f z) = _
    rw [hf z (img' d')]
    exact V.agg_iff (fun z' => f z' = img' d') (fun z' => Quot.mk r (.inl z') = d')
      (fun z' => ⟨fun h => inj _ _ h, fun h => by subst h; rfl⟩) (fun z' => G.R z' z)
  have hr : Solves q.sys K (fun w => Quot.mk r (.inr w)) := by
    intro w d'
    show UV.E (img' d') (dec q.sys w) = _
    rw [dec_solves]
    exact V.agg_iff (fun w' => dec q.sys w' = img' d') (fun w' => Quot.mk r (.inr w') = d')
      (fun w' => ⟨fun h => inj _ _ h, fun h => by subst h; rfl⟩) (fun w' => q.sys.R w' w)
  have hx : Pt.Same ⟨G, x⟩ q :=
    ⟨K, _, _, hl, hr, Quot.sound (show f x = dec q.sys q.pt from hq.symm)⟩
  exact ((Quotient.sound hx).trans hq).symm

/-- Every object of the kind is the value of a solution. -/
theorem dec_complete (a : UV V) : ∃ (G : Sys V) (x : G.N), dec G x = a :=
  Quotient.ind (motive := fun a => ∃ (G : Sys V) (x : G.N), dec G x = a)
    (fun p => ⟨p.sys, p.pt, rfl⟩) a

/-- **GLU for the kind over any complete value structure**: every system has
    exactly one solution, and every object is the value of a solution. -/
theorem glu (V : CVal) :
    (∀ G : Sys V, SolvesU G (dec G) ∧ ∀ f, SolvesU G f → ∀ x, f x = dec G x) ∧
    ∀ a : UV V, ∃ (G : Sys V) (x : G.N), dec G x = a :=
  ⟨fun G => ⟨dec_solution G, fun _ hf x => solution_unique G hf x⟩, dec_complete⟩

/-- **Identity is having a common image.** -/
theorem dec_eq_iff (G H : Sys V) (x : G.N) (y : H.N) :
    dec G x = dec H y ↔ ∃ (K : Sys V) (f : G.N → K.N) (g : H.N → K.N),
      Solves G K f ∧ Solves H K g ∧ f x = g y :=
  ⟨fun h => @Quotient.exact _ (Pt.setoid V) ⟨G, x⟩ ⟨H, y⟩ h,
    fun h => @Quotient.sound _ (Pt.setoid V) ⟨G, x⟩ ⟨H, y⟩ h⟩

/-! ## 4. Shadows: maps between value structures -/

/-- A map of value structures keeping the aggregate. -/
structure CHom (V V' : CVal) where
  φ : V.W → V'.W
  agg : ∀ {ι : Type} (f : ι → V.W), φ (V.agg f) = V'.agg (fun i => φ (f i))

variable {V' V'' : CVal}

def Sys.map (h : CHom V V') (G : Sys V) : Sys V' := ⟨G.N, fun z x => h.φ (G.R z x)⟩

theorem solves_map (h : CHom V V') {G H : Sys V} {f : G.N → H.N} (hf : Solves G H f) :
    Solves (G.map h) (H.map h) f := fun x b => by
  show h.φ (H.R b (f x)) = V'.agg (fun z : {z // f z = b} => h.φ (G.R z.1 x))
  rw [hf x b, h.agg]

/-- The shadow of the kind along a map of value structures. -/
def UV.map (h : CHom V V') : UV V → UV V' :=
  Quotient.lift (fun p : Pt V => dec (p.sys.map h) p.pt) (fun _ _ hpq => by
    obtain ⟨K, f, g, hf, hg, e⟩ := hpq
    exact Quotient.sound ⟨K.map h, f, g, solves_map h hf, solves_map h hg, e⟩)

/-- The shadow of a solution is the solution of the shadow. -/
theorem UV.map_dec (h : CHom V V') (G : Sys V) (x : G.N) :
    UV.map h (dec G x) = dec (G.map h) x := rfl

def CHom.id (V : CVal) : CHom V V := ⟨fun w => w, fun _ => rfl⟩

def CHom.comp (h₂ : CHom V' V'') (h₁ : CHom V V') : CHom V V'' :=
  ⟨fun w => h₂.φ (h₁.φ w), fun f => by rw [h₁.agg, h₂.agg]⟩

theorem UV.map_id (a : UV V) : UV.map (CHom.id V) a = a :=
  Quotient.ind (motive := fun a => UV.map (CHom.id V) a = a) (fun _ => rfl) a

theorem UV.map_comp (h₂ : CHom V' V'') (h₁ : CHom V V') (a : UV V) :
    UV.map (h₂.comp h₁) a = UV.map h₂ (UV.map h₁ a) :=
  Quotient.ind (motive := fun a => UV.map (h₂.comp h₁) a = UV.map h₂ (UV.map h₁ a))
    (fun _ => rfl) a

/-! ## 5. The sharp instance: identity is bisimilarity -/

/-- A bisimulation between two sharp systems. -/
def IsBisim (G H : Sys sharp) (S : G.N → H.N → Prop) : Prop :=
  ∀ x y, S x y →
    (∀ x', G.R x' x → ∃ y', H.R y' y ∧ S x' y') ∧ (∀ y', H.R y' y → ∃ x', G.R x' x ∧ S x' y')

theorem sharp_mem (G : Sys sharp) (x : G.N) (b : UV sharp) :
    UV.E b (dec G x) ↔ ∃ z, G.R z x ∧ dec G z = b :=
  ⟨fun ⟨⟨z, hz⟩, h⟩ => ⟨z, h, hz⟩, fun ⟨z, h, hz⟩ => ⟨⟨z, hz⟩, h⟩⟩

/-- Two sharp solutions into one system relate their sources by a bisimulation. -/
theorem bisim_of_image {G H K : Sys sharp} {f : G.N → K.N} {g : H.N → K.N}
    (hf : Solves G K f) (hg : Solves H K g) : IsBisim G H (fun x y => f x = g y) := by
  intro x y hxy
  constructor
  · intro x' hx'
    have h1 : K.R (f x') (g y) := by
      rw [← hxy]
      exact Eq.mpr (hf x (f x')) ⟨⟨x', rfl⟩, hx'⟩
    obtain ⟨⟨y', hy'⟩, hr⟩ := Eq.mp (hg y (f x')) h1
    exact ⟨y', hr, hy'.symm⟩
  · intro y' hy'
    have h1 : K.R (g y') (f x) := by
      rw [hxy]
      exact Eq.mpr (hg y (g y')) ⟨⟨y', rfl⟩, hy'⟩
    obtain ⟨⟨x', hx'⟩, hr⟩ := Eq.mp (hf x (g y')) h1
    exact ⟨x', hr, hx'⟩

def bisimRel {G H : Sys sharp} (S : G.N → H.N → Prop) : G.N ⊕ H.N → G.N ⊕ H.N → Prop :=
  fun s t => ∃ x y, S x y ∧ s = .inl x ∧ t = .inr y

def bisimVal {G H : Sys sharp} (S : G.N → H.N → Prop) (c : Quot (bisimRel S)) :
    G.N ⊕ H.N → Prop
  | .inl x => ∃ x' : {x' : G.N // Quot.mk (bisimRel S) (.inl x') = c}, G.R x'.1 x
  | .inr y => ∃ y' : {y' : H.N // Quot.mk (bisimRel S) (.inr y') = c}, H.R y'.1 y

theorem bisimVal_wd {G H : Sys sharp} {S : G.N → H.N → Prop} (hS : IsBisim G H S)
    (c : Quot (bisimRel S)) {x : G.N} {y : H.N} (hxy : S x y) :
    bisimVal S c (.inl x) = bisimVal S c (.inr y) := by
  apply propext
  constructor
  · rintro ⟨⟨x', hx'⟩, hr⟩
    obtain ⟨y', hy', hs⟩ := (hS x y hxy).1 x' hr
    exact ⟨⟨y', (Quot.sound ⟨x', y', hs, rfl, rfl⟩).symm.trans hx'⟩, hy'⟩
  · rintro ⟨⟨y', hy'⟩, hr⟩
    obtain ⟨x', hx', hs⟩ := (hS x y hxy).2 y' hr
    exact ⟨⟨x', (Quot.sound ⟨x', y', hs, rfl, rfl⟩).trans hy'⟩, hx'⟩

/-- Glue two sharp systems along a bisimulation. -/
def bisimGlue (G H : Sys sharp) (S : G.N → H.N → Prop) (hS : IsBisim G H S) : Sys sharp where
  N := Quot (bisimRel S)
  R c := Quot.lift (bisimVal S c) (fun s t hst => by
    obtain ⟨x, y, hxy, rfl, rfl⟩ := hst
    exact bisimVal_wd hS c hxy)

/-- **In the sharp kind, identity is bisimilarity.** -/
theorem sharp_same_iff (G H : Sys sharp) (x : G.N) (y : H.N) :
    dec G x = dec H y ↔ ∃ S : G.N → H.N → Prop, IsBisim G H S ∧ S x y := by
  constructor
  · intro h
    obtain ⟨K, f, g, hf, hg, e⟩ := Quotient.exact h
    exact ⟨fun x y => f x = g y, bisim_of_image hf hg, e⟩
  · rintro ⟨S, hS, hxy⟩
    exact Quotient.sound ⟨bisimGlue G H S hS, fun x => Quot.mk _ (.inl x),
      fun y => Quot.mk _ (.inr y), fun _ _ => rfl, fun _ _ => rfl,
      Quot.sound ⟨x, y, hxy, rfl, rfl⟩⟩

/-! ## 6. Identity as a relation, for every value structure -/

/-- The value with which a node of `G` or `H` answers into the class of `c` under `S`. -/
def classVal {G H : Sys V} (S : G.N ⊕ H.N → G.N ⊕ H.N → Prop) (c : G.N ⊕ H.N) :
    G.N ⊕ H.N → V.W
  | .inl x => V.agg (fun z : {z : G.N // S (.inl z) c} => G.R z.1 x)
  | .inr y => V.agg (fun w : {w : H.N // S (.inr w) c} => H.R w.1 y)

/-- A bisimulation in the sense of Larsen–Skou: an equivalence on the nodes of `G`
    and `H` under which related nodes answer with the same value into every class. -/
structure LSBisim (G H : Sys V) (S : G.N ⊕ H.N → G.N ⊕ H.N → Prop) : Prop where
  refl : ∀ s, S s s
  symm : ∀ {s t}, S s t → S t s
  trans : ∀ {s t u}, S s t → S t u → S s u
  val : ∀ {s t}, S s t → ∀ c, classVal S c s = classVal S c t

/-- Into the class of `c`, a node answers as its image answers in a common image. -/
theorem classVal_img {G H K : Sys V} {f : G.N → K.N} {g : H.N → K.N} (hf : Solves G K f)
    (hg : Solves H K g) (c s : G.N ⊕ H.N) :
    classVal (fun s t => Sum.elim f g s = Sum.elim f g t) c s =
      K.R (Sum.elim f g c) (Sum.elim f g s) := by
  cases s with
  | inl x => exact (hf x (Sum.elim f g c)).symm
  | inr y => exact (hg y (Sum.elim f g c)).symm

/-- A class value does not depend on the representative of the class. -/
theorem classVal_congr {G H : Sys V} {S : G.N ⊕ H.N → G.N ⊕ H.N → Prop} (hS : LSBisim G H S)
    {c c' : G.N ⊕ H.N} (hc : S c c') (s : G.N ⊕ H.N) : classVal S c s = classVal S c' s := by
  cases s with
  | inl x =>
    exact V.agg_iff (fun z => S (.inl z) c) (fun z => S (.inl z) c')
      (fun _ => ⟨fun h => hS.trans h hc, fun h => hS.trans h (hS.symm hc)⟩) (fun z => G.R z x)
  | inr y =>
    exact V.agg_iff (fun w => S (.inr w) c) (fun w => S (.inr w) c')
      (fun _ => ⟨fun h => hS.trans h hc, fun h => hS.trans h (hS.symm hc)⟩) (fun w => H.R w y)

/-- **Identity, as a relation, for every complete value structure**: two nodes are
    the same object exactly when a Larsen–Skou bisimulation relates them. -/
theorem same_iff_ls (G H : Sys V) (x : G.N) (y : H.N) :
    dec G x = dec H y ↔ ∃ S, LSBisim G H S ∧ S (.inl x) (.inr y) := by
  constructor
  · intro h
    obtain ⟨K, f, g, hf, hg, e⟩ := (dec_eq_iff G H x y).1 h
    refine ⟨fun s t => Sum.elim f g s = Sum.elim f g t,
      ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2, fun hst c => ?_⟩, e⟩
    rw [classVal_img hf hg, classVal_img hf hg, hst]
  · rintro ⟨S, hS, hxy⟩
    let st : Setoid (G.N ⊕ H.N) := ⟨S, ⟨hS.refl, hS.symm, hS.trans⟩⟩
    let K : Sys V := ⟨Quotient st, fun d' d => Quotient.lift₂ (s₁ := st) (s₂ := st)
      (fun c s => classVal S c s)
      (fun _ _ _ _ hc hs => (classVal_congr hS hc _).trans (hS.val hs _)) d' d⟩
    have hl : Solves G K (fun z => Quotient.mk st (.inl z)) := by
      intro z d
      induction d using Quotient.ind with
      | _ c =>
        exact V.agg_iff (fun z' => S (.inl z') c)
          (fun z' => Quotient.mk st (.inl z') = Quotient.mk st c)
          (fun _ => ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩) (fun z' => G.R z' z)
    have hr : Solves H K (fun w => Quotient.mk st (.inr w)) := by
      intro w d
      induction d using Quotient.ind with
      | _ c =>
        exact V.agg_iff (fun w' => S (.inr w') c)
          (fun w' => Quotient.mk st (.inr w') = Quotient.mk st c)
          (fun _ => ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩) (fun w' => H.R w' w)
    exact (dec_eq_iff G H x y).2 ⟨K, _, _, hl, hr, Quotient.sound hxy⟩

end PZFC.Values
