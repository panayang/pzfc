/-
  The weighted kind (notes/34).  The construction is `Values` (mathlib-free, one
  construction for every complete value structure); here are the weights and what
  happens along the value axis.

  §1  weights: `[0, ∞]` with its sums is a complete value structure, so the kind
      over it — the weighted kind — satisfies GLU (`Values.glu`);
  §2  the value axis: the support is a shadow from weights to sharp answers; it
      forgets multiplicity; the sharp kind embeds in the weighted one with
      weights exactly 0 or 1, and the shadow undoes the embedding — along values,
      the classical origin is a retract.
-/

import Values
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open scoped ENNReal

namespace PZFC.WeightedKind

open PZFC.Values

/-! ## 1. Weights -/

/-- Weights: the family's weights add up. -/
noncomputable abbrev weights : CVal where
  W := ℝ≥0∞
  agg f := ∑' i, f i
  agg_iso e f := (⟨e.to, e.inv, e.inv_to, e.to_inv⟩ : _ ≃ _).tsum_eq f
  agg_unit _ := tsum_eq_single () (fun _ hb => (hb rfl).elim)
  agg_sigma f := ENNReal.tsum_sigma f

/-- **GLU for the weighted kind**: every weighted system has exactly one solution,
    and every weighted object is the value of one. -/
theorem weighted_glu :
    (∀ G : Sys weights, SolvesU G (dec G) ∧ ∀ f, SolvesU G f → ∀ x, f x = dec G x) ∧
    ∀ a : UV weights, ∃ (G : Sys weights) (x : G.N), dec G x = a :=
  glu weights

/-! ## 2. The value axis: support, multiplicity, and the origin as a retract -/

/-- The support: a weight seen only as zero or not. -/
noncomputable def supp : CHom weights sharp where
  φ w := w ≠ 0
  agg f := propext (by
    show (∑' i, f i) ≠ 0 ↔ ∃ i, f i ≠ 0
    rw [Ne, ENNReal.tsum_eq_zero, not_forall])

/-- A leaf `e`, a node `a1` holding it once, and a node `a2` holding it twice. -/
inductive Three
  | e | a1 | a2

noncomputable def mult : Sys weights where
  N := Three
  R z x := match z, x with
    | .e, .a1 => (1 : ℝ≥0∞)
    | .e, .a2 => 2
    | _, _ => 0

theorem mult_weight (x : Three) :
    UV.E (dec mult .e) (dec mult x) = mult.R .e x := by
  show ∑' z : {z // dec mult z = dec mult .e}, mult.R z.1 x = mult.R .e x
  refine tsum_eq_single (⟨.e, rfl⟩ : {z // dec mult z = dec mult .e}) ?_
  rintro ⟨z, hz⟩ hne
  cases z with
  | e => exact absurd rfl hne
  | a1 => cases x <;> rfl
  | a2 => cases x <;> rfl

/-- The shadow of `mult`: a leaf, and one node holding it. -/
def twoLevel : Sys sharp := ⟨Bool, fun b c => b = false ∧ c = true⟩

def squash : Three → Bool
  | .e => false
  | _ => true

theorem squash_solves : Solves (mult.map supp) twoLevel squash := by
  intro x b
  apply propext
  show (b = false ∧ squash x = true) ↔ ∃ z : {z // squash z = b}, mult.R z.1 x ≠ 0
  constructor
  · rintro ⟨rfl, hx⟩
    refine ⟨⟨.e, rfl⟩, ?_⟩
    cases x with
    | e => exact Bool.noConfusion hx
    | a1 => exact one_ne_zero
    | a2 => exact two_ne_zero
  · rintro ⟨⟨z, rfl⟩, hR⟩
    cases z <;> cases x <;> first | exact ⟨rfl, rfl⟩ | exact (hR rfl).elim

/-- **The shadow forgets multiplicity**: a member counted once and the same member
    counted twice are different weighted objects with one shadow. -/
theorem shadow_forgets :
    dec mult .a1 ≠ dec mult .a2 ∧ UV.map supp (dec mult .a1) = UV.map supp (dec mult .a2) := by
  refine ⟨fun h => ?_, (dec_image squash_solves .a1).trans (dec_image squash_solves .a2).symm⟩
  have h1 := mult_weight .a1
  have h2 := mult_weight .a2
  rw [h] at h1
  have h12 : (1 : ℝ≥0∞) = 2 := h1.symm.trans h2
  exact ENNReal.one_lt_two.ne h12

open scoped Classical in
/-- A sharp image, weighted: `t'` counts once as a member of `t` exactly when its
    value is a member of the value of `t`. -/
noncomputable def imgSys {T : Type} (v : T → UV sharp) : Sys weights :=
  ⟨T, fun t' t => if UV.E (v t') (v t) then 1 else 0⟩

open scoped Classical in
/-- Over an injective image closed under members, the weight of `b` is 1 or 0. -/
theorem sum_img {T : Type} (v : T → UV sharp) (hv : ∀ t t', v t = v t' → t = t')
    (hcl : ∀ t b, UV.E b (v t) → ∃ t', v t' = b) (t : T) (b : UV sharp) :
    ∑' t' : {t' // v t' = b}, (if UV.E (v t'.1) (v t) then (1 : ℝ≥0∞) else 0) =
      if UV.E b (v t) then 1 else 0 := by
  by_cases hb : ∃ t₀, v t₀ = b
  · obtain ⟨t₀, h₀⟩ := hb
    rw [tsum_eq_single ⟨t₀, h₀⟩ (fun ⟨t', h'⟩ hne =>
      absurd (Subtype.ext (hv _ _ (h'.trans h₀.symm))) hne)]
    rw [h₀]
  · have : IsEmpty {t' // v t' = b} := ⟨fun ⟨t', h'⟩ => hb ⟨t', h'⟩⟩
    rw [tsum_empty, if_neg (fun h => hb (hcl t b h))]

/-- Weighted sharp images: an injective map between them, over the values, solves. -/
theorem img_solves {T T' : Type} (v : T → UV sharp) (v' : T' → UV sharp)
    (hv : ∀ t t', v t = v t' → t = t') (hv' : ∀ t t', v' t = v' t' → t = t')
    (hcl : ∀ t b, UV.E b (v t) → ∃ t', v t' = b) (ι : T → T') (hι : ∀ t, v' (ι t) = v t) :
    Solves (imgSys v) (imgSys v') ι := by
  intro t d'
  have e := weights.agg_iff (fun t' => ι t' = d') (fun t' => v t' = v' d')
    (fun t' => ⟨fun h => (hι t').symm.trans (congrArg v' h), fun h => hv' _ _ ((hι t').trans h)⟩)
    (fun t' => (imgSys v).R t' t)
  refine Eq.trans ?_ e.symm
  show (imgSys v').R d' (ι t) = ∑' t' : {t' // v t' = v' d'}, (imgSys v).R t'.1 t
  unfold imgSys
  dsimp only
  rw [hι t]
  exact (sum_img v hv hcl t (v' d')).symm

/-- The nodes of a sharp system with the same value, identified. -/
def colN (G : Sys sharp) : Type := Quot (fun z z' : G.N => dec G z = dec G z')

def colVal (G : Sys sharp) : colN G → UV sharp := Quot.lift (dec G) (fun _ _ h => h)

theorem colVal_inj (G : Sys sharp) (c c' : colN G) (h : colVal G c = colVal G c') : c = c' := by
  induction c using Quot.ind
  induction c' using Quot.ind
  exact Quot.sound h

theorem colVal_closed (G : Sys sharp) (c : colN G) (b : UV sharp)
    (h : UV.E b (colVal G c)) : ∃ c', colVal G c' = b := by
  induction c using Quot.ind with
  | mk z =>
    obtain ⟨⟨z', hz'⟩, -⟩ := h
    exact ⟨Quot.mk _ z', hz'⟩

/-- **The embedding of the sharp kind into the weighted kind**: collapse a sharp
    system to its values, and count each member once. -/
noncomputable def embed : UV sharp → UV weights :=
  Quotient.lift (fun p : Pt sharp => dec (imgSys (colVal p.sys)) (Quot.mk _ p.pt))
    (fun p q hpq => by
      have hpq' : dec p.sys p.pt = dec q.sys q.pt := Quotient.sound hpq
      let w : colN p.sys ⊕ colN q.sys → UV sharp := Sum.elim (colVal p.sys) (colVal q.sys)
      let v' : Quot (fun s t => w s = w t) → UV sharp := Quot.lift w (fun _ _ h => h)
      have hv' : ∀ d d', v' d = v' d' → d = d' := by
        intro d d'
        induction d using Quot.ind
        induction d' using Quot.ind
        exact fun h => Quot.sound h
      have h1 := img_solves (colVal p.sys) v' (colVal_inj p.sys) hv' (colVal_closed p.sys)
        (fun c => Quot.mk _ (.inl c)) (fun _ => rfl)
      have h2 := img_solves (colVal q.sys) v' (colVal_inj q.sys) hv' (colVal_closed q.sys)
        (fun c => Quot.mk _ (.inr c)) (fun _ => rfl)
      exact (dec_image h1 _).trans
        ((congrArg (dec (imgSys v'))
          (@Quot.sound _ (fun s t => w s = w t) (.inl (Quot.mk _ p.pt)) (.inr (Quot.mk _ q.pt))
            hpq')).trans (dec_image h2 _).symm))

/-- The collapse projection is a sharp solution into the shadow of the weighted collapse. -/
theorem col_proj_solves (G : Sys sharp) :
    Solves G ((imgSys (colVal G)).map supp) (fun z => Quot.mk _ z) := by
  classical
  intro z c'
  apply propext
  show ((if UV.E (colVal G c') (dec G z) then (1 : ℝ≥0∞) else 0) ≠ 0) ↔
    ∃ z' : {z' // Quot.mk _ z' = c'}, G.R z'.1 z
  constructor
  · intro h
    have hm : UV.E (colVal G c') (dec G z) := by
      by_contra hn
      exact h (if_neg hn)
    obtain ⟨z', hR, hz'⟩ := (sharp_mem G z _).1 hm
    exact ⟨⟨z', colVal_inj G _ _ hz'⟩, hR⟩
  · rintro ⟨⟨z', hz'⟩, hR⟩
    have hm : UV.E (colVal G c') (dec G z) := by
      subst hz'
      exact (sharp_mem G z _).2 ⟨z', hR, rfl⟩
    rw [if_pos hm]
    exact one_ne_zero

/-- **Along values, the classical origin is a retract**: embed a sharp object with
    weights 0 or 1, take the support, and the object comes back. -/
theorem shadow_embed (a : UV sharp) : UV.map supp (embed a) = a := by
  refine Quotient.ind (motive := fun a => UV.map supp (embed a) = a) (fun p => ?_) a
  show dec ((imgSys (colVal p.sys)).map supp) (Quot.mk _ p.pt) = dec p.sys p.pt
  exact (dec_image (col_proj_solves p.sys) p.pt).symm

theorem embed_inj {a b : UV sharp} (h : embed a = embed b) : a = b := by
  rw [← shadow_embed a, ← shadow_embed b, h]

theorem embed_col (G : Sys sharp) (c : colN G) :
    dec (imgSys (colVal G)) c = embed (colVal G c) := by
  induction c using Quot.ind
  rfl

open scoped Classical in
/-- **The embedded weights are exactly 0 or 1**: a sharp member counts once, a
    non-member not at all. -/
theorem embed_mem (a b : UV sharp) :
    UV.E (embed b) (embed a) = if UV.E b a then 1 else 0 := by
  refine Quotient.ind (motive := fun a => UV.E (embed b) (embed a) = if UV.E b a then 1 else 0)
    (fun p => ?_) a
  have e := weights.agg_iff (fun c => dec (imgSys (colVal p.sys)) c = embed b)
    (fun c => colVal p.sys c = b)
    (fun c => ⟨fun h => embed_inj ((embed_col p.sys c).symm.trans h),
      fun h => (embed_col p.sys c).trans (congrArg embed h)⟩)
    (fun c => (imgSys (colVal p.sys)).R c (Quot.mk _ p.pt))
  refine e.trans ?_
  exact sum_img (colVal p.sys) (colVal_inj p.sys) (colVal_closed p.sys) (Quot.mk _ p.pt) b

end PZFC.WeightedKind
