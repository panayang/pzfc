/-
  Askers inside the system (notes/51).  Mathlib-free.

  When askers are inside, one asker's question is part of another asker's
  history: the circumstances "who asks" and "what was asked before" merge.

  §1  non-interference: no asker's question changes what the others get
  §2  in a network of at least two askers, a public behavior in which nobody's
      question changes what the others get is undisturbed, hence has a record
      model; so in a public world, a disturbance always shows as interference
      (my reading changes what you get)
  §3  the hypotheses are needed: a shared flipped memory (public, disturbed,
      interfering) and a private flipped memory per asker (non-interfering,
      disturbed, not public)
  §4  passing records on: what one behavior answers, passed on through a channel;
      records pass through a channel that depends on neither history nor asker;
      a record passed through a shared channel that changes when read is no longer
      a record for the receivers: what they get depends on the others' readings
-/
import Circumstances

namespace PZFC.Net

open PZFC.Circ

variable {K Q A : Type}

/-! ## 1. Non-interference -/

/-- No asker's question changes what any other asker gets. -/
def NonInterfering (b : Beh K Q A) : Prop :=
  ∀ h k k' q' q, k ≠ k' → b (h ++ [(k', q')]) k q = b h k q

/-! ## 2. Publicity turns disturbance into interference -/

/-- One step: in a public, non-interfering behavior with another asker at hand, no question
    changes anything. -/
theorem step_undisturbed (b : Beh K Q A) (hp : Public b) (hn : NonInterfering b)
    (other : ∀ k : K, ∃ k'', k'' ≠ k) (h : List (K × Q)) (e : K × Q) (k : K) (q : Q) :
    b (h ++ [e]) k q = b h k q := by
  obtain ⟨k'', hk''⟩ := other e.1
  calc b (h ++ [e]) k q = b (h ++ [(e.1, e.2)]) k'' q := hp _ k k'' q
    _ = b h k'' q := hn h k'' e.1 e.2 q hk''
    _ = b h k q := hp h k'' k q

theorem append_undisturbed (b : Beh K Q A) (hp : Public b) (hn : NonInterfering b)
    (other : ∀ k : K, ∃ k'', k'' ≠ k) (t : List (K × Q)) :
    ∀ (h : List (K × Q)) (k : K) (q : Q), b (h ++ t) k q = b h k q := by
  induction t with
  | nil => intro h k q; rw [List.append_nil]
  | cons e t ih =>
    intro h k q
    rw [show h ++ e :: t = (h ++ [e]) ++ t by simp, ih (h ++ [e]) k q]
    exact step_undisturbed b hp hn other h e k q

/-- **In a network of at least two askers, public and non-interfering imply undisturbed.** -/
theorem public_nonInterfering_undisturbed (b : Beh K Q A) (hp : Public b)
    (hn : NonInterfering b) (other : ∀ k : K, ∃ k'', k'' ≠ k) : Undisturbed b := by
  intro h h' k q
  have e1 := append_undisturbed b hp hn other h [] k q
  have e2 := append_undisturbed b hp hn other h' [] k q
  simp only [List.nil_append] at e1 e2
  rw [e1, e2]

/-- **In a public world, a disturbance always shows as interference**: some asker's question
    changes what another asker gets. -/
theorem public_disturbed_interferes (b : Beh K Q A) (hp : Public b) (hd : ¬ Undisturbed b)
    (other : ∀ k : K, ∃ k'', k'' ≠ k) : ¬ NonInterfering b :=
  fun hn => hd (public_nonInterfering_undisturbed b hp hn other)

/-- With a first asker, public and non-interfering give a record model. -/
theorem public_nonInterfering_record (k₀ : K) (b : Beh K Q A) (hp : Public b)
    (hn : NonInterfering b) (other : ∀ k : K, ∃ k'', k'' ≠ k) : HasRecordModel b :=
  (record_iff k₀ b).mpr ⟨hp, public_nonInterfering_undisturbed b hp hn other⟩

/-! ## 3. The hypotheses are needed -/

theorem bool_other : ∀ k : Bool, ∃ k'', k'' ≠ k := fun k => ⟨!k, by cases k <;> decide⟩

/-- A shared flipped memory: every reading, by anyone, flips it. -/
def sharedFlip : Beh Bool Unit Bool := fun h _ _ => decide (h.length % 2 = 1)

theorem sharedFlip_public : Public sharedFlip := fun _ _ _ _ => rfl

theorem sharedFlip_disturbed : ¬ Undisturbed sharedFlip := by
  intro hu; exact absurd (hu [(true, ())] [] false ()) (by decide)

/-- One asker's reading changes what the other gets. -/
theorem sharedFlip_interferes : ¬ NonInterfering sharedFlip :=
  public_disturbed_interferes sharedFlip sharedFlip_public sharedFlip_disturbed bool_other

/-- A private flipped memory: each asker's own readings flip what that asker gets. -/
def ownFlip : Beh Bool Unit Bool :=
  fun h k _ => decide ((h.filter (fun e => e.1 == k)).length % 2 = 1)

theorem ownFlip_nonInterfering : NonInterfering ownFlip := by
  intro h k k' q' q hne
  have hb : (k' == k) = false := by cases k <;> cases k' <;> simp_all
  show decide (((h ++ [(k', q')]).filter (fun e => e.1 == k)).length % 2 = 1) =
    decide ((h.filter (fun e => e.1 == k)).length % 2 = 1)
  simp [List.filter_append, hb]

theorem ownFlip_disturbed : ¬ Undisturbed ownFlip := by
  intro hu; exact absurd (hu [(true, ())] [] true ()) (by decide)

theorem ownFlip_not_public : ¬ Public ownFlip := by
  intro hp; exact absurd (hp [(true, ())] true false ()) (by decide)

/-! ## 4. Passing records on -/

/-- Pass on what `a` answers through a channel that may depend on the history and on
    who asks. -/
def transfer {B : Type} (a : Beh K Q A) (ρ : List (K × Q) → K → A → B) : Beh K Q B :=
  fun h k q => ρ h k (a h k q)

/-- **Records pass through a recording channel.** -/
theorem transfer_record {B : Type} (a : Beh K Q A) (ρ : List (K × Q) → K → A → B)
    (ha : HasRecordModel a) (hρ : ∃ g : A → B, ∀ h k x, ρ h k x = g x) :
    HasRecordModel (transfer a ρ) := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨g, hg⟩ := hρ
  exact ⟨fun q => g (r q), fun h k q => by simp only [transfer, hr, hg]⟩

/-- A fixed record: the observed system always answers `true`. -/
def fixedTrue : Beh Bool Unit Bool := fun _ _ _ => true

theorem fixedTrue_record : HasRecordModel fixedTrue := ⟨fun _ => true, fun _ _ _ => rfl⟩

/-- A shared relay that flips its report with every reading, by anyone. -/
def flipRelay : List (Bool × Unit) → Bool → Bool → Bool :=
  fun h _ x => xor x (decide (h.length % 2 = 1))

theorem relayed_public : Public (transfer fixedTrue flipRelay) := fun _ _ _ _ => rfl

theorem relayed_disturbed : ¬ Undisturbed (transfer fixedTrue flipRelay) := by
  intro hu; exact absurd (hu [(true, ())] [] false ()) (by decide)

/-- **A record, passed on through a shared relay that changes when read, is no longer a
    record for the receivers**: one receiver's reading changes what the other gets. -/
theorem relayed_interferes : ¬ NonInterfering (transfer fixedTrue flipRelay) :=
  public_disturbed_interferes _ relayed_public relayed_disturbed bool_other

end PZFC.Net
