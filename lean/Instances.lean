/-
  The shape extension is the sharp instance of the one construction (notes/35).
  Mathlib-free.

  `Shapes` §8 built the anti-founded universe as pointed graphs up to
  bisimilarity; `Values` builds a kind for every complete value structure, as
  pointed systems up to a common image.  At sharp answers the two coincide: a
  bijection between them keeps membership both ways.
-/

import Shapes
import Values

namespace PZFC.Instances

open PZFC.Values

/-- A pointed sharp system, as a pointed graph. -/
def toPG (p : Pt sharp) : Shapes.PG := ⟨p.sys.N, p.sys.R, p.pt⟩

/-- From the sharp kind to the shape extension. -/
def toUA : UV sharp → Shapes.UA :=
  Quotient.lift (fun p => Shapes.UA.mk (toPG p)) (fun p q hpq => by
    have h : dec p.sys p.pt = dec q.sys q.pt := Quotient.sound hpq
    obtain ⟨S, hS, hs⟩ := (sharp_same_iff p.sys q.sys p.pt q.pt).1 h
    exact Shapes.UA.mk_eq ⟨S, hS, hs⟩)

/-- From the shape extension to the sharp kind. -/
def fromUA : Shapes.UA → UV sharp :=
  Quotient.lift (fun G : Shapes.PG => dec (⟨G.N, G.R⟩ : Sys sharp) G.pt) (fun G H hGH => by
    obtain ⟨S, hS, hs⟩ := hGH
    exact (sharp_same_iff ⟨G.N, G.R⟩ ⟨H.N, H.R⟩ G.pt H.pt).2 ⟨S, hS, hs⟩)

theorem from_to (a : UV sharp) : fromUA (toUA a) = a :=
  Quotient.ind (motive := fun a => fromUA (toUA a) = a) (fun _ => rfl) a

theorem to_from (a : Shapes.UA) : toUA (fromUA a) = a :=
  Quotient.ind (motive := fun a => toUA (fromUA a) = a) (fun _ => rfl) a

/-- The bijection sends the solution of a system to the solution of the same graph. -/
theorem toUA_dec (G : Sys sharp) (x : G.N) : toUA (dec G x) = Shapes.UA.dec G.R x := rfl

/-- **The sharp instance of the one construction is the shape extension**: the
    bijection keeps membership both ways. -/
theorem mem_iff (b a : UV sharp) : UV.E b a ↔ Shapes.UA.Mem (toUA b) (toUA a) := by
  refine Quotient.ind (motive := fun a => UV.E b a ↔ Shapes.UA.Mem (toUA b) (toUA a))
    (fun p => ?_) a
  show UV.E b (dec p.sys p.pt) ↔ Shapes.UA.Mem (toUA b) (Shapes.UA.dec p.sys.R p.pt)
  rw [sharp_mem, Shapes.UA.dec_solves p.sys.R p.pt (toUA b)]
  constructor
  · rintro ⟨z, hz, h⟩
    exact ⟨z, hz, by rw [← h]; rfl⟩
  · rintro ⟨z, hz, h⟩
    refine ⟨z, hz, ?_⟩
    have := congrArg fromUA h
    rw [from_to] at this
    exact this

end PZFC.Instances
