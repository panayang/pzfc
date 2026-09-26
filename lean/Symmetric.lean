/-
  Symmetry with values (notes/38).  Mathlib-free.

  Values, names and a group of symmetries together.  A system with symmetries is a
  system (`Values`) whose nodes a group moves, keeping the values of membership,
  and whose atoms carry names that the group moves too.  Solutions commute with the
  symmetries and keep names.  The kind is built as in `Values`: pointed systems,
  identified when some solutions send them to one node.

  §1  names with symmetries; systems with symmetries; solutions; gluing two
      solutions out of one system;
  §2  the kind: GLU holds; the group acts on the objects, keeps the values of
      membership, and moves the names.
  (`lean-mathlib/RandomChoice.lean`: Russell's socks with weights.)
-/

import Kinds
import Values

namespace PZFC.Symmetric

open PZFC.Values
open PZFC.Kinds (Grp)

universe u

/-! ## 1. Systems with symmetries -/

/-- Names, moved by a group of symmetries. -/
structure GLab (Γ : Grp) where
  L : Type
  lact : Γ.G → L → L
  lact_one : ∀ l, lact Γ.one l = l
  lact_mul : ∀ g h l, lact (Γ.mul g h) l = lact g (lact h l)

/-- A system with symmetries: the group moves the nodes and keeps the values of
    membership; atoms carry names, moved along. -/
structure GSys (V : CVal) (Γ : Grp) (Λ : GLab Γ) extends Sys V where
  act : Γ.G → N → N
  act_one : ∀ x, act Γ.one x = x
  act_mul : ∀ g h x, act (Γ.mul g h) x = act g (act h x)
  R_act : ∀ g z x, R (act g z) (act g x) = R z x
  lab : N → Option Λ.L
  lab_act : ∀ g x, lab (act g x) = (lab x).map (Λ.lact g)

variable {V : CVal} {Γ : Grp} {Λ : GLab Γ}

theorem GSys.act_inv_act (G : GSys V Γ Λ) (g : Γ.G) (x : G.N) :
    G.act (Γ.inv g) (G.act g x) = x := by
  rw [← G.act_mul, Γ.inv_mul, G.act_one]

theorem GSys.act_act_inv (G : GSys V Γ Λ) (g : Γ.G) (x : G.N) :
    G.act g (G.act (Γ.inv g) x) = x := by
  rw [← G.act_mul, Γ.mul_inv, G.act_one]

/-- Re-indexing an aggregate along an invertible map. -/
theorem agg_act (V : CVal) {A : Type} (a a' : A → A) (h1 : ∀ x, a' (a x) = x)
    (h2 : ∀ x, a (a' x) = x) (P Q : A → Prop) (hPQ : ∀ x, P x → Q (a x))
    (hQP : ∀ x, Q x → P (a' x)) (F : A → V.W) :
    V.agg (fun z : {z // Q z} => F z.1) = V.agg (fun z : {z // P z} => F (a z.1)) :=
  (V.agg_iso (⟨fun z => ⟨a z.1, hPQ z.1 z.2⟩, fun z => ⟨a' z.1, hQP z.1 z.2⟩,
    fun z => Subtype.ext (h1 z.1), fun z => Subtype.ext (h2 z.1)⟩ :
      Iso {z // P z} {z // Q z}) (fun z => F z.1)).symm

/-- A solution with symmetries: it solves the values, commutes with the symmetries,
    and keeps names. -/
def GSolves (G H : GSys V Γ Λ) (f : G.N → H.N) : Prop :=
  Solves G.toSys H.toSys f ∧ (∀ g x, f (G.act g x) = H.act g (f x)) ∧ ∀ x, H.lab (f x) = G.lab x

theorem gsolves_id (G : GSys V Γ Λ) : GSolves G G id :=
  ⟨solves_id _, fun _ _ => rfl, fun _ => rfl⟩

theorem gsolves_comp {G H K : GSys V Γ Λ} {f : G.N → H.N} {g : H.N → K.N}
    (hf : GSolves G H f) (hg : GSolves H K g) : GSolves G K (fun x => g (f x)) :=
  ⟨solves_comp hf.1 hg.1, fun a x => by
    show g (f (G.act a x)) = K.act a (g (f x))
    rw [hf.2.1, hg.2.1], fun x => by
    show K.lab (g (f x)) = G.lab x
    rw [hg.2.2, hf.2.2]⟩

section Glue

variable {H K K' : GSys V Γ Λ} {f : H.N → K.N} {f' : H.N → K'.N}

def glueActRaw (g : Γ.G) : K.N ⊕ K'.N → glueN f f'
  | .inl k => Quot.mk _ (.inl (K.act g k))
  | .inr k => Quot.mk _ (.inr (K'.act g k))

/-- The symmetries on the glued nodes. -/
def glueAct (hf : GSolves H K f) (hf' : GSolves H K' f') (g : Γ.G) :
    glueN f f' → glueN f f' :=
  Quot.lift (glueActRaw g) (fun s t hst => by
    obtain ⟨h, rfl, rfl⟩ := hst
    show Quot.mk (glueRel f f') (.inl (K.act g (f h))) =
      Quot.mk (glueRel f f') (.inr (K'.act g (f' h)))
    rw [← hf.2.1, ← hf'.2.1]
    exact Quot.sound ⟨H.act g h, rfl, rfl⟩)

def glueLabRaw : K.N ⊕ K'.N → Option Λ.L
  | .inl k => K.lab k
  | .inr k => K'.lab k

/-- The names of the glued nodes. -/
def glueLab (hf : GSolves H K f) (hf' : GSolves H K' f') : glueN f f' → Option Λ.L :=
  Quot.lift glueLabRaw (fun s t hst => by
    obtain ⟨h, rfl, rfl⟩ := hst
    show K.lab (f h) = K'.lab (f' h)
    rw [hf.2.2, hf'.2.2])

theorem glueAct_inv (hf : GSolves H K f) (hf' : GSolves H K' f') (g : Γ.G)
    (c : glueN f f') : glueAct hf hf' (Γ.inv g) (glueAct hf hf' g c) = c := by
  induction c using Quot.ind with
  | mk s =>
    cases s with
    | inl k => exact congrArg (fun k => Quot.mk (glueRel f f') (.inl k)) (K.act_inv_act g k)
    | inr k => exact congrArg (fun k => Quot.mk (glueRel f f') (.inr k)) (K'.act_inv_act g k)

theorem glueAct_inv' (hf : GSolves H K f) (hf' : GSolves H K' f') (g : Γ.G)
    (c : glueN f f') : glueAct hf hf' g (glueAct hf hf' (Γ.inv g) c) = c := by
  induction c using Quot.ind with
  | mk s =>
    cases s with
    | inl k => exact congrArg (fun k => Quot.mk (glueRel f f') (.inl k)) (K.act_act_inv g k)
    | inr k => exact congrArg (fun k => Quot.mk (glueRel f f') (.inr k)) (K'.act_act_inv g k)

/-- The glued values are kept by the symmetries. -/
theorem glue_R_act (hf : GSolves H K f) (hf' : GSolves H K' f') (g : Γ.G)
    (c x : glueN f f') :
    (glue hf.1 hf'.1).R (glueAct hf hf' g c) (glueAct hf hf' g x) = (glue hf.1 hf'.1).R c x := by
  induction x using Quot.ind with
  | mk s =>
    cases s with
    | inl k =>
      show V.agg (fun k' : {k' : K.N // Quot.mk (glueRel f f') (.inl k') = glueAct hf hf' g c} =>
          K.R k'.1 (K.act g k)) =
        V.agg (fun k' : {k' : K.N // Quot.mk (glueRel f f') (.inl k') = c} => K.R k'.1 k)
      refine (agg_act V (K.act g) (K.act (Γ.inv g)) (K.act_inv_act g) (K.act_act_inv g)
        (fun k' => Quot.mk (glueRel f f') (.inl k') = c)
        (fun k' => Quot.mk (glueRel f f') (.inl k') = glueAct hf hf' g c)
        (fun _ hk => congrArg (glueAct hf hf' g) hk)
        (fun _ hk => (congrArg (glueAct hf hf' (Γ.inv g)) hk).trans (glueAct_inv hf hf' g c))
        (fun k' => K.R k' (K.act g k))).trans ?_
      exact V.agg_congr (fun k' => K.R_act g k'.1 k)
    | inr k =>
      show V.agg (fun k' : {k' : K'.N // Quot.mk (glueRel f f') (.inr k') = glueAct hf hf' g c} =>
          K'.R k'.1 (K'.act g k)) =
        V.agg (fun k' : {k' : K'.N // Quot.mk (glueRel f f') (.inr k') = c} => K'.R k'.1 k)
      refine (agg_act V (K'.act g) (K'.act (Γ.inv g)) (K'.act_inv_act g) (K'.act_act_inv g)
        (fun k' => Quot.mk (glueRel f f') (.inr k') = c)
        (fun k' => Quot.mk (glueRel f f') (.inr k') = glueAct hf hf' g c)
        (fun _ hk => congrArg (glueAct hf hf' g) hk)
        (fun _ hk => (congrArg (glueAct hf hf' (Γ.inv g)) hk).trans (glueAct_inv hf hf' g c))
        (fun k' => K'.R k' (K'.act g k))).trans ?_
      exact V.agg_congr (fun k' => K'.R_act g k'.1 k)

/-- The glued system with symmetries. -/
def gglue (hf : GSolves H K f) (hf' : GSolves H K' f') : GSys V Γ Λ where
  toSys := glue hf.1 hf'.1
  act := glueAct hf hf'
  act_one := fun c => by
    induction c using Quot.ind with
    | mk s =>
      cases s with
      | inl k => exact congrArg (fun k => Quot.mk (glueRel f f') (.inl k)) (K.act_one k)
      | inr k => exact congrArg (fun k => Quot.mk (glueRel f f') (.inr k)) (K'.act_one k)
  act_mul := fun g h c => by
    induction c using Quot.ind with
    | mk s =>
      cases s with
      | inl k => exact congrArg (fun k => Quot.mk (glueRel f f') (.inl k)) (K.act_mul g h k)
      | inr k => exact congrArg (fun k => Quot.mk (glueRel f f') (.inr k)) (K'.act_mul g h k)
  R_act := glue_R_act hf hf'
  lab := glueLab hf hf'
  lab_act := fun g c => by
    induction c using Quot.ind with
    | mk s =>
      cases s with
      | inl k => exact K.lab_act g k
      | inr k => exact K'.lab_act g k

theorem gsolves_inl (hf : GSolves H K f) (hf' : GSolves H K' f') :
    GSolves K (gglue hf hf') (fun k => Quot.mk (glueRel f f') (.inl k)) :=
  ⟨solves_inl hf.1 hf'.1, fun _ _ => rfl, fun _ => rfl⟩

theorem gsolves_inr (hf : GSolves H K f) (hf' : GSolves H K' f') :
    GSolves K' (gglue hf hf') (fun k => Quot.mk (glueRel f f') (.inr k)) :=
  ⟨solves_inr hf.1 hf'.1, fun _ _ => rfl, fun _ => rfl⟩

end Glue

/-! ## 2. The kind -/

structure GPt (V : CVal) (Γ : Grp) (Λ : GLab Γ) where
  sys : GSys V Γ Λ
  pt : sys.N

/-- Two pointed systems are identified when some solutions send them to one node. -/
def GPt.Same (p q : GPt V Γ Λ) : Prop :=
  ∃ (K : GSys V Γ Λ) (f : p.sys.N → K.N) (g : q.sys.N → K.N),
    GSolves p.sys K f ∧ GSolves q.sys K g ∧ f p.pt = g q.pt

theorem GPt.same_refl (p : GPt V Γ Λ) : p.Same p :=
  ⟨p.sys, id, id, gsolves_id _, gsolves_id _, rfl⟩

theorem GPt.same_symm {p q : GPt V Γ Λ} (h : p.Same q) : q.Same p := by
  obtain ⟨K, f, g, hf, hg, e⟩ := h
  exact ⟨K, g, f, hg, hf, e.symm⟩

theorem GPt.same_trans {p q r : GPt V Γ Λ} (h1 : p.Same q) (h2 : q.Same r) : p.Same r := by
  obtain ⟨K, f, g, hf, hg, e⟩ := h1
  obtain ⟨K', g', k, hg', hk, e'⟩ := h2
  refine ⟨gglue hg hg', fun x => Quot.mk (glueRel g g') (.inl (f x)),
    fun x => Quot.mk (glueRel g g') (.inr (k x)),
    gsolves_comp hf (gsolves_inl hg hg'), gsolves_comp hk (gsolves_inr hg hg'), ?_⟩
  show Quot.mk (glueRel g g') (.inl (f p.pt)) = Quot.mk (glueRel g g') (.inr (k r.pt))
  rw [e, ← e']
  exact Quot.sound ⟨q.pt, rfl, rfl⟩

instance GPt.setoid (V : CVal) (Γ : Grp) (Λ : GLab Γ) : Setoid (GPt V Γ Λ) :=
  ⟨GPt.Same, ⟨GPt.same_refl, GPt.same_symm, GPt.same_trans⟩⟩

/-- The kind with values `V`, symmetries `Γ` and names `Λ` (all shapes). -/
def UG (V : CVal) (Γ : Grp) (Λ : GLab Γ) : Type 1 := Quotient (GPt.setoid V Γ Λ)

/-- The solution of a system: node `x` goes to the system pointed at `x`. -/
def gdec (G : GSys V Γ Λ) (x : G.N) : UG V Γ Λ := Quotient.mk _ ⟨G, x⟩

theorem gdec_image {G K : GSys V Γ Λ} {f : G.N → K.N} (hf : GSolves G K f) (x : G.N) :
    gdec G x = gdec K (f x) :=
  Quotient.sound ⟨K, f, id, hf, gsolves_id K, rfl⟩

/-- The value with which `b` answers as a member of `a`. -/
def UG.E (b a : UG V Γ Λ) : V.W :=
  Quotient.lift (fun p : GPt V Γ Λ => V.agg (fun z : {z // gdec p.sys z = b} => p.sys.R z.1 p.pt))
    (fun p q hpq => by
      obtain ⟨K, f, g, hf, hg, e⟩ := hpq
      calc V.agg (fun z : {z // gdec p.sys z = b} => p.sys.R z.1 p.pt)
          = V.agg (fun z : {z // gdec K (f z) = b} => p.sys.R z.1 p.pt) :=
            V.agg_iff (fun z => gdec p.sys z = b) (fun z => gdec K (f z) = b)
              (fun z => Iff.of_eq (congrArg (· = b) (gdec_image hf z)))
              (fun z => p.sys.R z p.pt)
        _ = V.agg (fun y : {y // gdec K y = b} => K.R y.1 (f p.pt)) :=
            (solves_fiber hf.1 (gdec K) b p.pt).symm
        _ = V.agg (fun y : {y // gdec K y = b} => K.R y.1 (g q.pt)) := by rw [e]
        _ = V.agg (fun z : {z // gdec K (g z) = b} => q.sys.R z.1 q.pt) :=
            solves_fiber hg.1 (gdec K) b q.pt
        _ = V.agg (fun z : {z // gdec q.sys z = b} => q.sys.R z.1 q.pt) :=
            V.agg_iff (fun z => gdec K (g z) = b) (fun z => gdec q.sys z = b)
              (fun z => Iff.of_eq (congrArg (· = b) (gdec_image hg z).symm))
              (fun z => q.sys.R z q.pt)) a

/-- A symmetry, acting on the objects. -/
def UG.act (g : Γ.G) : UG V Γ Λ → UG V Γ Λ :=
  Quotient.lift (fun p : GPt V Γ Λ => gdec p.sys (p.sys.act g p.pt)) (fun p q hpq => by
    obtain ⟨K, f, h, hf, hh, e⟩ := hpq
    exact Quotient.sound ⟨K, f, h, hf, hh, by rw [hf.2.1, hh.2.1, e]⟩)

/-- The name of an object, if it is an atom. -/
def UG.lab : UG V Γ Λ → Option Λ.L :=
  Quotient.lift (fun p : GPt V Γ Λ => p.sys.lab p.pt) (fun p q hpq => by
    obtain ⟨K, f, h, hf, hh, e⟩ := hpq
    show p.sys.lab p.pt = q.sys.lab q.pt
    rw [← hf.2.2, ← hh.2.2, e])

theorem gdec_solves (G : GSys V Γ Λ) (x : G.N) (b : UG V Γ Λ) :
    UG.E b (gdec G x) = V.agg (fun z : {z // gdec G z = b} => G.R z.1 x) := rfl

theorem UG.act_gdec (g : Γ.G) (G : GSys V Γ Λ) (x : G.N) :
    UG.act g (gdec G x) = gdec G (G.act g x) := rfl

theorem UG.lab_gdec (G : GSys V Γ Λ) (x : G.N) : UG.lab (gdec G x) = G.lab x := rfl

theorem UG.act_one (a : UG V Γ Λ) : UG.act Γ.one a = a :=
  Quotient.ind (motive := fun a => UG.act Γ.one a = a)
    (fun p => congrArg (gdec p.sys) (p.sys.act_one p.pt)) a

theorem UG.act_mul (g h : Γ.G) (a : UG V Γ Λ) : UG.act (Γ.mul g h) a = UG.act g (UG.act h a) :=
  Quotient.ind (motive := fun a => UG.act (Γ.mul g h) a = UG.act g (UG.act h a))
    (fun p => congrArg (gdec p.sys) (p.sys.act_mul g h p.pt)) a

theorem UG.act_inv_act (g : Γ.G) (a : UG V Γ Λ) : UG.act (Γ.inv g) (UG.act g a) = a :=
  Quotient.ind (motive := fun a => UG.act (Γ.inv g) (UG.act g a) = a)
    (fun p => congrArg (gdec p.sys) (p.sys.act_inv_act g p.pt)) a

/-- The symmetries move names. -/
theorem UG.lab_act (g : Γ.G) (a : UG V Γ Λ) : UG.lab (UG.act g a) = (UG.lab a).map (Λ.lact g) :=
  Quotient.ind (motive := fun a => UG.lab (UG.act g a) = (UG.lab a).map (Λ.lact g))
    (fun p => p.sys.lab_act g p.pt) a

/-- **The symmetries keep the values of membership.** -/
theorem UG.E_act (g : Γ.G) (b a : UG V Γ Λ) : UG.E (UG.act g b) (UG.act g a) = UG.E b a := by
  refine Quotient.ind (motive := fun a => UG.E (UG.act g b) (UG.act g a) = UG.E b a)
    (fun p => ?_) a
  show V.agg (fun z : {z // gdec p.sys z = UG.act g b} => p.sys.R z.1 (p.sys.act g p.pt)) =
    V.agg (fun z : {z // gdec p.sys z = b} => p.sys.R z.1 p.pt)
  refine (agg_act V (p.sys.act g) (p.sys.act (Γ.inv g)) (p.sys.act_inv_act g)
    (p.sys.act_act_inv g) (fun z => gdec p.sys z = b) (fun z => gdec p.sys z = UG.act g b)
    (fun z hz => by
      show UG.act g (gdec p.sys z) = UG.act g b
      rw [hz])
    (fun z hz => by
      show UG.act (Γ.inv g) (gdec p.sys z) = b
      rw [hz, UG.act_inv_act])
    (fun z => p.sys.R z (p.sys.act g p.pt))).trans ?_
  exact V.agg_congr (fun z => p.sys.R_act g z.1 p.pt)

/-- `f` solves `G` in the kind: values, symmetries and names. -/
def GSolvesU (G : GSys V Γ Λ) (f : G.N → UG V Γ Λ) : Prop :=
  (∀ x b, UG.E b (f x) = V.agg (fun z : {z // f z = b} => G.R z.1 x)) ∧
  (∀ g x, f (G.act g x) = UG.act g (f x)) ∧ ∀ x, UG.lab (f x) = G.lab x

theorem gdec_solution (G : GSys V Γ Λ) : GSolvesU G (gdec G) :=
  ⟨gdec_solves G, fun _ _ => rfl, fun _ => rfl⟩

/-- **Every solution in the kind is `gdec`.** -/
theorem gsolution_unique (G : GSys V Γ Λ) {f : G.N → UG V Γ Λ} (hf : GSolvesU G f) (x : G.N) :
    f x = gdec G x := by
  obtain ⟨q, hq⟩ := Quotient.exists_rep (f x)
  let img : G.N ⊕ q.sys.N → UG V Γ Λ := fun s => Sum.elim f (gdec q.sys) s
  let r : G.N ⊕ q.sys.N → G.N ⊕ q.sys.N → Prop := fun s t => img s = img t
  let img' : Quot r → UG V Γ Λ := Quot.lift img (fun _ _ h => h)
  have inj : ∀ d d' : Quot r, img' d = img' d' → d = d' := by
    intro d d'
    induction d using Quot.ind
    induction d' using Quot.ind
    exact fun h => Quot.sound h
  let actS : Γ.G → G.N ⊕ q.sys.N → G.N ⊕ q.sys.N := fun g s =>
    Sum.elim (fun z => .inl (G.act g z)) (fun w => .inr (q.sys.act g w)) s
  have img_act : ∀ g s, img (actS g s) = UG.act g (img s) := by
    intro g s
    cases s with
    | inl z => exact hf.2.1 g z
    | inr w => rfl
  let actK : Γ.G → Quot r → Quot r := fun g =>
    Quot.lift (fun s => Quot.mk r (actS g s)) (fun s t h => Quot.sound (show
      img (actS g s) = img (actS g t) by rw [img_act, img_act]; exact congrArg (UG.act g) h))
  have img'_act : ∀ g d, img' (actK g d) = UG.act g (img' d) := by
    intro g d
    induction d using Quot.ind
    exact img_act g _
  let K : GSys V Γ Λ :=
    { N := Quot r
      R := fun d' d => UG.E (img' d') (img' d)
      act := actK
      act_one := fun d => inj _ _ (by rw [img'_act, UG.act_one])
      act_mul := fun g h d => inj _ _ (by simp only [img'_act, UG.act_mul])
      R_act := fun g d' d => by
        show UG.E (img' (actK g d')) (img' (actK g d)) = UG.E (img' d') (img' d)
        rw [img'_act, img'_act, UG.E_act]
      lab := fun d => UG.lab (img' d)
      lab_act := fun g d => by
        show UG.lab (img' (actK g d)) = (UG.lab (img' d)).map (Λ.lact g)
        rw [img'_act, UG.lab_act] }
  have hl : GSolves G K (fun z => Quot.mk r (.inl z)) := by
    refine ⟨fun z d' => ?_, fun _ _ => rfl, fun z => hf.2.2 z⟩
    show UG.E (img' d') (f z) = _
    rw [hf.1 z (img' d')]
    exact V.agg_iff (fun z' => f z' = img' d') (fun z' => Quot.mk r (.inl z') = d')
      (fun z' => ⟨fun h => inj _ _ h, fun h => by subst h; rfl⟩) (fun z' => G.R z' z)
  have hr : GSolves q.sys K (fun w => Quot.mk r (.inr w)) := by
    refine ⟨fun w d' => ?_, fun _ _ => rfl, fun _ => rfl⟩
    show UG.E (img' d') (gdec q.sys w) = _
    rw [gdec_solves]
    exact V.agg_iff (fun w' => gdec q.sys w' = img' d') (fun w' => Quot.mk r (.inr w') = d')
      (fun w' => ⟨fun h => inj _ _ h, fun h => by subst h; rfl⟩) (fun w' => q.sys.R w' w)
  have hx : GPt.Same ⟨G, x⟩ q :=
    ⟨K, _, _, hl, hr, Quot.sound (show f x = gdec q.sys q.pt from hq.symm)⟩
  exact ((Quotient.sound hx).trans hq).symm

theorem gdec_complete (a : UG V Γ Λ) : ∃ (G : GSys V Γ Λ) (x : G.N), gdec G x = a :=
  Quotient.ind (motive := fun a => ∃ (G : GSys V Γ Λ) (x : G.N), gdec G x = a)
    (fun p => ⟨p.sys, p.pt, rfl⟩) a

/-- **GLU with values, symmetries and names**: every system has exactly one solution,
    and every object is the value of a solution. -/
theorem gglu (V : CVal) (Γ : Grp) (Λ : GLab Γ) :
    (∀ G : GSys V Γ Λ, GSolvesU G (gdec G) ∧ ∀ f, GSolvesU G f → ∀ x, f x = gdec G x) ∧
    ∀ a : UG V Γ Λ, ∃ (G : GSys V Γ Λ) (x : G.N), gdec G x = a :=
  ⟨fun G => ⟨gdec_solution G, fun _ hf x => gsolution_unique G hf x⟩, gdec_complete⟩

end PZFC.Symmetric
