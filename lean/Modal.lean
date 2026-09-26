/-
  Convergence of possibilities (notes/57).  Mathlib-free.

  Worlds with an extension relation (reflexive, transitive).  In a world,
  "necessarily p" means p in every extension; "possibly p" means p in some.

  §1  frames, necessity, possibility
  §2  the principle .2 (possibly-necessary implies necessarily-possible) holds for
      every valuation exactly when the frame is confluent: any two extensions of a
      world have a common further extension.  So .2 is gluing, at the level of
      what can become true
  §3  in a confluent frame, what can become permanent on two branches can become
      permanent together
  §4  a branching frame: two branches make permanent commitments that can never
      be brought together; .2 fails
  §5  linear time is a special case of gluing (notes/60): the principle .3 holds for
      every valuation exactly when the frame is connected (any two extensions of a
      world are comparable); a connected frame is confluent; so .3 implies .2
-/

namespace PZFC.Modal

/-! ## 1. Frames -/

/-- Worlds with an extension relation. -/
structure Frame where
  W : Type
  R : W → W → Prop
  refl : ∀ w, R w w
  trans : ∀ {u v w : W}, R u v → R v w → R u w

variable (F : Frame)

/-- Necessarily: in every extension. -/
def Box (p : F.W → Prop) (w : F.W) : Prop := ∀ v, F.R w v → p v

/-- Possibly: in some extension. -/
def Dia (p : F.W → Prop) (w : F.W) : Prop := ∃ v, F.R w v ∧ p v

/-- Any two extensions of a world have a common further extension. -/
def Confluent : Prop := ∀ u v w : F.W, F.R u v → F.R u w → ∃ x, F.R v x ∧ F.R w x

/-- The principle .2 at every world and for every valuation. -/
def Dot2 : Prop := ∀ (p : F.W → Prop) (u : F.W), Dia F (Box F p) u → Box F (Dia F p) u

/-! ## 2. .2 is confluence -/

theorem dot2_of_confluent (hc : Confluent F) : Dot2 F := by
  rintro p u ⟨v, huv, hbox⟩ w huw
  obtain ⟨x, hvx, hwx⟩ := hc u v w huv huw
  exact ⟨x, hwx, hbox x hvx⟩

theorem confluent_of_dot2 (hd : Dot2 F) : Confluent F := by
  intro u v w huv huw
  have hbox : Box F (fun x => F.R v x) v := fun y hy => hy
  obtain ⟨x, hwx, hvx⟩ := hd (fun x => F.R v x) u ⟨v, huv, hbox⟩ w huw
  exact ⟨x, hvx, hwx⟩

/-- **.2 holds for every valuation exactly when the frame is confluent.** -/
theorem dot2_iff_confluent : Dot2 F ↔ Confluent F :=
  ⟨confluent_of_dot2 F, dot2_of_confluent F⟩

/-! ## 3. Permanent commitments come together in a confluent frame -/

theorem box_persists {p : F.W → Prop} {v x : F.W} (h : Box F p v) (hvx : F.R v x) :
    Box F p x := fun y hy => h y (F.trans hvx hy)

/-- In a confluent frame: if p can become permanent and q can become permanent, then
    both can become permanent together. -/
theorem commitments_join (hc : Confluent F) (p q : F.W → Prop) (u : F.W)
    (hp : Dia F (Box F p) u) (hq : Dia F (Box F q) u) :
    Dia F (Box F (fun x => p x ∧ q x)) u := by
  obtain ⟨v, huv, hv⟩ := hp
  obtain ⟨w, huw, hw⟩ := hq
  obtain ⟨x, hvx, hwx⟩ := hc u v w huv huw
  refine ⟨x, F.trans huv hvx, fun y hy => ⟨?_, ?_⟩⟩
  · exact box_persists F hv hvx y hy
  · exact box_persists F hw hwx y hy

/-! ## 4. A branching frame -/

/-- A root with two branches, `true` and `false`, that never meet. -/
inductive Node | root | left | right
  deriving DecidableEq

def branchR : Node → Node → Prop
  | .root, _ => True
  | .left, .left => True
  | .right, .right => True
  | _, _ => False

def branching : Frame where
  W := Node
  R := branchR
  refl w := by cases w <;> trivial
  trans {u v w} huv hvw := by
    cases u <;> cases v <;> cases w <;> simp_all [branchR]

/-- The commitment made on the left branch. -/
def onLeft : Node → Prop := fun x => x = .left

/-- From the root, "left" can become permanent, and so can "not left"; but never both:
    the two branches make permanent commitments that cannot be brought together. -/
theorem branching_commitments :
    Dia branching (Box branching onLeft) .root ∧
    Dia branching (Box branching (fun x => ¬ onLeft x)) .root ∧
    ¬ Dia branching (Box branching (fun x => onLeft x ∧ ¬ onLeft x)) .root := by
  refine ⟨⟨.left, trivial, ?_⟩, ⟨.right, trivial, ?_⟩, ?_⟩
  · intro y hy; cases y <;> simp_all [branching, branchR, onLeft]
  · intro y hy; cases y <;> simp_all [branching, branchR, onLeft]
  · rintro ⟨x, -, hx⟩
    exact (hx x (branching.refl x)).2 (hx x (branching.refl x)).1

/-- So the branching frame is not confluent, and .2 fails in it. -/
theorem branching_not_dot2 : ¬ Dot2 branching := by
  intro hd
  obtain ⟨x, hl, hr⟩ := confluent_of_dot2 branching hd .root .left .right trivial trivial
  cases x <;> simp_all [branching, branchR]

/-! ## 5. Linear time is a special case of gluing -/

/-- Any two extensions of a world are comparable: the extensions form a line. -/
def Connected : Prop := ∀ u v w : F.W, F.R u v → F.R u w → F.R v w ∨ F.R w v

/-- The principle .3 at every world and for every pair of valuations. -/
def Dot3 : Prop := ∀ (p q : F.W → Prop) (u : F.W),
  Box F (fun x => Box F p x → q x) u ∨ Box F (fun x => Box F q x → p x) u

theorem connected_of_dot3 (hd : Dot3 F) : Connected F := by
  intro u v w huv huw
  rcases hd (fun x => F.R v x) (fun x => F.R w x) u with h | h
  · exact Or.inr (h v huv (fun y hy => hy))
  · exact Or.inl (h w huw (fun y hy => hy))

theorem dot3_of_connected (hc : Connected F) : Dot3 F := by
  intro p q u
  refine Classical.byContradiction fun hno => ?_
  have h1 : ¬ Box F (fun x => Box F p x → q x) u := fun h => hno (Or.inl h)
  have h2 : ¬ Box F (fun x => Box F q x → p x) u := fun h => hno (Or.inr h)
  have e1 : ∃ v, F.R u v ∧ Box F p v ∧ ¬ q v :=
    Classical.byContradiction fun hn =>
      h1 (fun v huv hp => Classical.byContradiction fun hq => hn ⟨v, huv, hp, hq⟩)
  have e2 : ∃ w, F.R u w ∧ Box F q w ∧ ¬ p w :=
    Classical.byContradiction fun hn =>
      h2 (fun w huw hq => Classical.byContradiction fun hp => hn ⟨w, huw, hq, hp⟩)
  obtain ⟨v, huv, hpv, hqv⟩ := e1
  obtain ⟨w, huw, hqw, hpw⟩ := e2
  rcases hc u v w huv huw with hvw | hwv
  · exact hpw (hpv w hvw)
  · exact hqv (hqw v hwv)

/-- **.3 holds for every valuation exactly when the frame is connected.** -/
theorem dot3_iff_connected : Dot3 F ↔ Connected F :=
  ⟨connected_of_dot3 F, dot3_of_connected F⟩

/-- A connected frame is confluent: a line of extensions always glues. -/
theorem confluent_of_connected (hc : Connected F) : Confluent F := by
  intro u v w huv huw
  rcases hc u v w huv huw with hvw | hwv
  · exact ⟨w, hvw, F.refl w⟩
  · exact ⟨v, F.refl v, hwv⟩

/-- **Linear time is a special case of gluing**: .3 implies .2. -/
theorem dot2_of_dot3 (hd : Dot3 F) : Dot2 F :=
  dot2_of_confluent F (confluent_of_connected F (connected_of_dot3 F hd))

end PZFC.Modal
