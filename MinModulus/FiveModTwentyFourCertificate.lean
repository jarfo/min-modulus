import MinModulus.AbelianMin

namespace MinModulus.FiveModTwentyFourCertificate
open Finset

/-- A candidate multiplicity vector for the normalized tuple. -/
structure Rival where
  k0 : ℕ
  k1 : ℕ
  k2 : ℕ
  k3 : ℕ
  k4 : ℕ

def Rival.vector (r : Rival) : Fin 5 → ℕ := ![r.k0,r.k1,r.k2,r.k3,r.k4]

def Rival.valid (r : Rival) : Bool :=
  decide (r.k0+r.k1+r.k2+r.k3+r.k4=5 ∧
    ¬ (r.k0=1 ∧ r.k1=1 ∧ r.k2=1 ∧ r.k3=1 ∧ r.k4=1))

def Rival.hits (r : Rival) (a b c : ℕ) : Bool :=
  decide ((r.k1+r.k2*a+r.k3*b+r.k4*c)%24=(1+a+b+c)%24)

/-- Each candidate is checked for its total multiplicity and weighted sum;
this finite list is data, not a trusted assertion. -/
def rivals : List Rival := [
  ⟨0,0,0,0,5⟩,
  ⟨0,0,2,2,1⟩,
  ⟨1,1,0,0,3⟩,
  ⟨0,1,0,0,4⟩,
  ⟨1,0,0,0,4⟩,
  ⟨2,3,0,0,0⟩,
  ⟨3,2,0,0,0⟩,
  ⟨0,1,1,1,2⟩,
  ⟨0,1,2,2,0⟩,
  ⟨1,0,1,1,2⟩,
  ⟨1,0,2,2,0⟩,
  ⟨1,3,0,0,1⟩,
  ⟨3,1,0,0,1⟩,
  ⟨0,2,0,0,3⟩,
  ⟨2,0,0,0,3⟩,
  ⟨0,3,1,1,0⟩,
  ⟨3,0,1,1,0⟩,
  ⟨0,3,0,0,2⟩,
  ⟨3,0,0,0,2⟩,
  ⟨0,5,0,0,0⟩,
  ⟨1,4,0,0,0⟩,
  ⟨4,1,0,0,0⟩,
  ⟨5,0,0,0,0⟩,
  ⟨0,4,0,0,1⟩,
  ⟨4,0,0,0,1⟩,
  ⟨1,1,0,2,1⟩,
  ⟨0,1,0,2,2⟩,
  ⟨0,1,1,2,1⟩,
  ⟨0,1,1,3,0⟩,
  ⟨1,0,0,2,2⟩,
  ⟨1,0,1,2,1⟩,
  ⟨1,0,1,3,0⟩,
  ⟨1,1,1,0,2⟩,
  ⟨0,0,1,2,2⟩,
  ⟨1,1,0,1,2⟩,
  ⟨0,1,2,1,1⟩,
  ⟨1,0,2,1,1⟩,
  ⟨0,1,2,0,2⟩,
  ⟨1,0,2,0,2⟩,
  ⟨0,2,0,2,1⟩,
  ⟨0,2,2,0,1⟩,
  ⟨0,1,3,1,0⟩,
  ⟨1,0,3,1,0⟩,
  ⟨0,3,2,0,0⟩,
  ⟨3,0,2,0,0⟩,
  ⟨0,3,0,2,0⟩,
  ⟨3,0,0,2,0⟩,
  ⟨0,0,2,1,2⟩,
  ⟨0,1,0,4,0⟩,
  ⟨1,0,0,4,0⟩,
  ⟨0,0,3,2,0⟩,
  ⟨0,3,0,1,1⟩,
  ⟨1,3,1,0,0⟩,
  ⟨3,0,0,1,1⟩,
  ⟨3,1,1,0,0⟩,
  ⟨0,2,0,1,2⟩,
  ⟨0,2,2,1,0⟩,
  ⟨0,2,1,0,2⟩,
  ⟨0,2,1,2,0⟩,
  ⟨0,3,1,0,1⟩,
  ⟨3,0,1,0,1⟩,
  ⟨1,3,0,1,0⟩,
  ⟨3,1,0,1,0⟩,
  ⟨0,1,0,1,3⟩,
  ⟨1,0,0,1,3⟩,
  ⟨0,1,1,0,3⟩,
  ⟨1,0,1,0,3⟩,
  ⟨0,2,0,3,0⟩,
  ⟨2,0,0,3,0⟩,
  ⟨0,1,0,3,1⟩,
  ⟨0,1,3,0,1⟩,
  ⟨1,0,0,3,1⟩,
  ⟨1,0,3,0,1⟩,
  ⟨1,1,0,3,0⟩,
  ⟨0,2,3,0,0⟩,
  ⟨2,0,3,0,0⟩,
  ⟨0,0,5,0,0⟩,
  ⟨1,1,3,0,0⟩,
  ⟨0,0,0,2,3⟩]

def covered (a b c : ℕ) : Bool :=
  rivals.any fun r ↦ r.valid && r.hits a b c

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation checks all 24³ normalized tuples, including repeated
coordinates. No external computation or additional axiom certifies this fact. -/
theorem all_covered :
    ((List.range 24).all fun a ↦ (List.range 24).all fun b ↦
      (List.range 24).all fun c ↦ covered a b c) = true := by decide

/-- The natural-number checker gives a concrete forbidden multiplicity vector. -/
theorem not_validTuple_of_covered (a b c : ℕ) (hc : covered a b c = true) :
    ¬ ValidTuple (![0,1,(a : ZMod 24),(b : ZMod 24),(c : ZMod 24)]) := by
  intro hg
  simp only [covered, List.any_eq_true, Bool.and_eq_true] at hc
  obtain ⟨r, _, hvalid, hhit⟩ := hc
  simp only [Rival.valid, decide_eq_true_eq] at hvalid
  simp only [Rival.hits, decide_eq_true_eq] at hhit
  have hsum : (∑ i, r.vector i) = 5 := by
    simpa [Rival.vector, Fin.sum_univ_five] using hvalid.1
  have heq : (∑ i, r.vector i • (![0,1,(a : ZMod 24),(b : ZMod 24),(c : ZMod 24)]) i) =
      ∑ i, (![0,1,(a : ZMod 24),(b : ZMod 24),(c : ZMod 24)]) i := by
    have hh : ((r.k1+r.k2*a+r.k3*b+r.k4*c : ℕ) : ZMod 24) =
        ((1+a+b+c : ℕ) : ZMod 24) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hhit
    simpa [Rival.vector, Fin.sum_univ_five, nsmul_eq_mul] using hh
  have hone := hg r.vector hsum heq
  apply hvalid.2
  exact ⟨by simpa [Rival.vector] using hone 0,
    by simpa [Rival.vector] using hone 1,
    by simpa [Rival.vector] using hone 2,
    by simpa [Rival.vector] using hone 3,
    by simpa [Rival.vector] using hone 4⟩

/-- Every normalized five-tuple modulo 24 has a checked multiplicity rival. -/
theorem not_validTuple_normalized (a b c : ZMod 24) :
    ¬ ValidTuple (![0,1,a,b,c]) := by
  have hh := all_covered
  simp only [List.all_eq_true] at hh
  have hc := hh a.val (List.mem_range.mpr a.val_lt)
    b.val (List.mem_range.mpr b.val_lt) c.val (List.mem_range.mpr c.val_lt)
  simpa using not_validTuple_of_covered a.val b.val c.val hc

end MinModulus.FiveModTwentyFourCertificate
