import MinModulus.FiveModTwentyFourCertificate

namespace MinModulus.FiveSmallEvenCertificate
open Finset FiveModTwentyFourCertificate

/-- The weighted-sum congruence for a natural multiplicity candidate. -/
def hits (N : ℕ) (r : Rival) (a b c : ℕ) : Bool :=
  decide ((r.k1+r.k2*a+r.k3*b+r.k4*c)%N=(1+a+b+c)%N)

/-- A listed candidate passes both multiplicity and weighted-sum checks. -/
def covered (N : ℕ) (rs : List Rival) (a b c : ℕ) : Bool :=
  rs.any fun r ↦ r.valid && hits N r a b c

/-- A checked natural candidate contradicts validity at any modulus. -/
theorem not_validTuple_of_covered {N : ℕ} (rs : List Rival)
    (a b c : ℕ) (hc : covered N rs a b c = true) :
    ¬ ValidTuple (![0,1,(a : ZMod N),(b : ZMod N),(c : ZMod N)]) := by
  intro hg
  simp only [covered,List.any_eq_true,Bool.and_eq_true] at hc
  obtain ⟨r,_,hvalid,hhit⟩ := hc
  simp only [Rival.valid,decide_eq_true_eq] at hvalid
  simp only [hits,decide_eq_true_eq] at hhit
  have hsum : (∑ i, r.vector i)=5 := by
    simpa [Rival.vector,Fin.sum_univ_five] using hvalid.1
  have heq : (∑ i, r.vector i • (![0,1,(a : ZMod N),(b : ZMod N),(c : ZMod N)]) i)=
      ∑ i, (![0,1,(a : ZMod N),(b : ZMod N),(c : ZMod N)]) i := by
    have hh : ((r.k1+r.k2*a+r.k3*b+r.k4*c : ℕ) : ZMod N)=
        ((1+a+b+c : ℕ) : ZMod N) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hhit
    simpa [Rival.vector,Fin.sum_univ_five,nsmul_eq_mul] using hh
  have hone := hg r.vector hsum heq
  apply hvalid.2
  exact ⟨by simpa [Rival.vector] using hone 0,
    by simpa [Rival.vector] using hone 1,
    by simpa [Rival.vector] using hone 2,
    by simpa [Rival.vector] using hone 3,
    by simpa [Rival.vector] using hone 4⟩

/-- Exhaustive natural residue coverage excludes every normalized tuple. -/
theorem not_validTuple_normalized {N : ℕ} [NeZero N] (rs : List Rival)
    (hall : ((List.range N).all fun a ↦ (List.range N).all fun b ↦
      (List.range N).all fun c ↦ covered N rs a b c)=true)
    (a b c : ZMod N) : ¬ ValidTuple (![0,1,a,b,c]) := by
  simp only [List.all_eq_true] at hall
  have hc := hall a.val (List.mem_range.mpr a.val_lt)
    b.val (List.mem_range.mpr b.val_lt) c.val (List.mem_range.mpr c.val_lt)
  simpa using not_validTuple_of_covered rs a.val b.val c.val hc

/-- Candidate multiplicities for normalized tuples modulo 18. -/
def rivals18 : List Rival := [
  ⟨0,0,0,0,5⟩,
  ⟨0,1,2,2,0⟩,
  ⟨1,0,2,2,0⟩,
  ⟨1,1,0,0,3⟩,
  ⟨0,1,0,0,4⟩,
  ⟨0,1,1,1,2⟩,
  ⟨1,0,0,0,4⟩,
  ⟨1,0,1,1,2⟩,
  ⟨0,0,2,2,1⟩,
  ⟨0,2,0,0,3⟩,
  ⟨1,3,0,0,1⟩,
  ⟨2,0,0,0,3⟩,
  ⟨3,1,0,0,1⟩,
  ⟨0,3,1,1,0⟩,
  ⟨0,4,0,0,1⟩,
  ⟨1,4,0,0,0⟩,
  ⟨0,3,0,0,2⟩,
  ⟨0,5,0,0,0⟩,
  ⟨2,3,0,0,0⟩,
  ⟨3,0,0,0,2⟩,
  ⟨3,0,1,1,0⟩,
  ⟨4,1,0,0,0⟩,
  ⟨5,0,0,0,0⟩,
  ⟨3,2,0,0,0⟩,
  ⟨4,0,0,0,1⟩,
  ⟨1,1,0,2,1⟩,
  ⟨0,0,0,5,0⟩,
  ⟨0,0,2,3,0⟩,
  ⟨0,1,1,2,1⟩,
  ⟨1,0,1,2,1⟩,
  ⟨1,1,0,1,2⟩,
  ⟨1,1,1,0,2⟩,
  ⟨0,1,2,0,2⟩,
  ⟨1,0,2,0,2⟩,
  ⟨1,1,0,3,0⟩,
  ⟨0,1,0,4,0⟩,
  ⟨1,0,0,4,0⟩,
  ⟨0,1,0,2,2⟩,
  ⟨1,0,0,2,2⟩,
  ⟨0,1,1,3,0⟩,
  ⟨1,0,1,3,0⟩,
  ⟨0,0,1,2,2⟩,
  ⟨0,1,2,1,1⟩,
  ⟨1,0,2,1,1⟩,
  ⟨0,0,2,1,2⟩,
  ⟨0,0,2,0,3⟩,
  ⟨0,0,0,4,1⟩,
  ⟨0,1,0,3,1⟩,
  ⟨1,0,0,3,1⟩,
  ⟨0,1,3,1,0⟩,
  ⟨1,0,3,1,0⟩,
  ⟨0,0,1,0,4⟩,
  ⟨0,0,5,0,0⟩,
  ⟨0,0,0,2,3⟩,
  ⟨0,1,4,0,0⟩,
  ⟨0,2,2,1,0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation checks every normalized triple modulo 18. -/
theorem all_covered18 :
    ((List.range 18).all fun a ↦ (List.range 18).all fun b ↦
      (List.range 18).all fun c ↦ covered 18 rivals18 a b c)=true := by decide


/-- Candidate multiplicities for normalized tuples modulo 20. -/
def rivals20 : List Rival := [
  ⟨0,0,0,0,5⟩,
  ⟨0,0,2,2,1⟩,
  ⟨1,1,0,0,3⟩,
  ⟨1,1,0,2,1⟩,
  ⟨1,4,0,0,0⟩,
  ⟨2,3,0,0,0⟩,
  ⟨3,2,0,0,0⟩,
  ⟨4,1,0,0,0⟩,
  ⟨0,1,1,1,2⟩,
  ⟨0,1,2,2,0⟩,
  ⟨1,0,1,1,2⟩,
  ⟨1,0,2,2,0⟩,
  ⟨0,3,0,0,2⟩,
  ⟨3,0,0,0,2⟩,
  ⟨0,1,0,0,4⟩,
  ⟨1,0,0,0,4⟩,
  ⟨1,3,0,0,1⟩,
  ⟨3,1,0,0,1⟩,
  ⟨0,2,0,0,3⟩,
  ⟨2,0,0,0,3⟩,
  ⟨0,3,1,1,0⟩,
  ⟨3,0,1,1,0⟩,
  ⟨0,4,0,0,1⟩,
  ⟨4,0,0,0,1⟩,
  ⟨0,1,0,2,2⟩,
  ⟨0,1,0,3,1⟩,
  ⟨0,1,1,2,1⟩,
  ⟨1,0,1,2,1⟩,
  ⟨1,0,2,1,1⟩,
  ⟨1,1,1,0,2⟩,
  ⟨1,0,0,2,2⟩,
  ⟨0,1,2,1,1⟩,
  ⟨1,1,0,1,2⟩,
  ⟨0,1,2,0,2⟩,
  ⟨1,0,2,0,2⟩,
  ⟨0,2,0,2,1⟩,
  ⟨0,1,1,3,0⟩,
  ⟨0,2,2,0,1⟩,
  ⟨1,0,1,3,0⟩,
  ⟨0,1,3,1,0⟩,
  ⟨3,0,0,2,0⟩,
  ⟨1,0,3,1,0⟩,
  ⟨0,3,2,0,0⟩,
  ⟨3,0,2,0,0⟩,
  ⟨0,3,0,2,0⟩,
  ⟨0,1,0,4,0⟩,
  ⟨1,0,0,4,0⟩,
  ⟨0,2,0,1,2⟩,
  ⟨0,2,1,0,2⟩,
  ⟨0,2,1,2,0⟩,
  ⟨0,2,2,1,0⟩,
  ⟨1,0,4,0,0⟩,
  ⟨3,1,0,1,0⟩,
  ⟨0,1,0,1,3⟩,
  ⟨3,0,0,1,1⟩,
  ⟨0,1,1,0,3⟩,
  ⟨3,0,1,0,1⟩,
  ⟨3,1,1,0,0⟩,
  ⟨0,0,0,5,0⟩,
  ⟨0,1,3,0,1⟩,
  ⟨1,1,0,3,0⟩,
  ⟨4,0,1,0,0⟩,
  ⟨0,0,3,2,0⟩,
  ⟨0,3,1,0,1⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation checks every normalized triple modulo 20. -/
theorem all_covered20 :
    ((List.range 20).all fun a ↦ (List.range 20).all fun b ↦
      (List.range 20).all fun c ↦ covered 20 rivals20 a b c)=true := by decide


/-- Candidate multiplicities for normalized tuples modulo 22. -/
def rivals22 : List Rival := [
  ⟨0,0,0,0,5⟩,
  ⟨1,1,0,0,3⟩,
  ⟨0,0,0,1,4⟩,
  ⟨0,0,0,2,3⟩,
  ⟨0,0,0,4,1⟩,
  ⟨1,1,1,0,2⟩,
  ⟨0,0,0,3,2⟩,
  ⟨0,0,0,5,0⟩,
  ⟨1,1,0,1,2⟩,
  ⟨1,1,0,2,1⟩,
  ⟨1,1,0,3,0⟩,
  ⟨0,0,1,2,2⟩,
  ⟨1,1,3,0,0⟩,
  ⟨0,0,1,0,4⟩,
  ⟨0,0,1,4,0⟩,
  ⟨0,0,2,0,3⟩,
  ⟨0,0,2,3,0⟩,
  ⟨0,0,3,0,2⟩,
  ⟨0,0,5,0,0⟩,
  ⟨0,0,2,1,2⟩,
  ⟨0,0,2,2,1⟩,
  ⟨0,0,3,2,0⟩,
  ⟨0,0,4,0,1⟩,
  ⟨0,0,4,1,0⟩,
  ⟨1,3,0,0,1⟩,
  ⟨1,3,0,1,0⟩,
  ⟨1,3,1,0,0⟩,
  ⟨3,1,0,0,1⟩,
  ⟨3,1,0,1,0⟩,
  ⟨3,1,1,0,0⟩,
  ⟨1,4,0,0,0⟩,
  ⟨4,1,0,0,0⟩,
  ⟨0,1,1,1,2⟩,
  ⟨0,1,1,2,1⟩,
  ⟨0,1,2,1,1⟩,
  ⟨1,0,1,1,2⟩,
  ⟨1,0,1,2,1⟩,
  ⟨1,0,2,1,1⟩,
  ⟨0,1,0,2,2⟩,
  ⟨1,0,0,2,2⟩,
  ⟨0,1,2,0,2⟩,
  ⟨1,0,2,0,2⟩,
  ⟨0,1,2,2,0⟩,
  ⟨1,0,2,2,0⟩,
  ⟨0,1,0,1,3⟩,
  ⟨0,1,1,0,3⟩,
  ⟨1,0,0,1,3⟩,
  ⟨1,0,1,0,3⟩,
  ⟨0,1,1,3,0⟩,
  ⟨1,0,1,3,0⟩,
  ⟨0,1,0,3,1⟩,
  ⟨1,0,0,3,1⟩,
  ⟨0,1,3,0,1⟩,
  ⟨0,1,3,1,0⟩,
  ⟨0,2,3,0,0⟩,
  ⟨2,0,0,0,3⟩,
  ⟨2,0,0,3,0⟩,
  ⟨0,2,0,0,3⟩,
  ⟨0,2,0,3,0⟩,
  ⟨2,0,3,0,0⟩,
  ⟨1,0,3,0,1⟩,
  ⟨1,0,3,1,0⟩,
  ⟨2,3,0,0,0⟩,
  ⟨3,2,0,0,0⟩,
  ⟨0,2,0,1,2⟩,
  ⟨0,2,0,2,1⟩,
  ⟨0,2,1,0,2⟩,
  ⟨0,2,1,2,0⟩,
  ⟨0,2,2,0,1⟩,
  ⟨0,2,2,1,0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation checks every normalized triple modulo 22. -/
theorem all_covered22 :
    ((List.range 22).all fun a ↦ (List.range 22).all fun b ↦
      (List.range 22).all fun c ↦ covered 22 rivals22 a b c)=true := by decide


/-- Candidate multiplicities for normalized tuples modulo 26. -/
def rivals26 : List Rival := [
  ⟨0,0,0,0,5⟩,
  ⟨1,1,0,0,3⟩,
  ⟨0,0,0,1,4⟩,
  ⟨0,0,0,2,3⟩,
  ⟨0,0,0,4,1⟩,
  ⟨1,1,1,0,2⟩,
  ⟨0,0,0,3,2⟩,
  ⟨0,0,0,5,0⟩,
  ⟨1,1,0,1,2⟩,
  ⟨1,1,0,2,1⟩,
  ⟨1,1,0,3,0⟩,
  ⟨0,0,1,2,2⟩,
  ⟨1,1,3,0,0⟩,
  ⟨0,0,1,0,4⟩,
  ⟨0,0,1,4,0⟩,
  ⟨0,0,2,0,3⟩,
  ⟨0,0,2,3,0⟩,
  ⟨0,0,3,0,2⟩,
  ⟨0,0,5,0,0⟩,
  ⟨0,0,2,1,2⟩,
  ⟨0,0,2,2,1⟩,
  ⟨0,0,3,2,0⟩,
  ⟨0,0,4,0,1⟩,
  ⟨0,0,4,1,0⟩,
  ⟨1,3,0,0,1⟩,
  ⟨1,3,0,1,0⟩,
  ⟨1,3,1,0,0⟩,
  ⟨3,1,0,0,1⟩,
  ⟨3,1,0,1,0⟩,
  ⟨3,1,1,0,0⟩,
  ⟨1,4,0,0,0⟩,
  ⟨4,1,0,0,0⟩,
  ⟨0,1,1,1,2⟩,
  ⟨0,1,1,2,1⟩,
  ⟨0,1,2,1,1⟩,
  ⟨1,0,1,1,2⟩,
  ⟨1,0,1,2,1⟩,
  ⟨1,0,2,1,1⟩,
  ⟨0,1,0,2,2⟩,
  ⟨1,0,0,2,2⟩,
  ⟨0,1,2,0,2⟩,
  ⟨1,0,2,0,2⟩,
  ⟨0,1,1,3,0⟩,
  ⟨1,0,1,3,0⟩,
  ⟨0,1,3,1,0⟩,
  ⟨1,0,3,1,0⟩,
  ⟨0,1,0,1,3⟩,
  ⟨0,1,1,0,3⟩,
  ⟨1,0,0,1,3⟩,
  ⟨1,0,1,0,3⟩,
  ⟨0,1,2,2,0⟩,
  ⟨1,0,2,2,0⟩,
  ⟨0,1,0,3,1⟩,
  ⟨0,1,3,0,1⟩,
  ⟨1,0,0,3,1⟩,
  ⟨1,0,3,0,1⟩,
  ⟨2,3,0,0,0⟩,
  ⟨3,2,0,0,0⟩,
  ⟨0,2,0,0,3⟩,
  ⟨0,2,0,3,0⟩,
  ⟨0,2,3,0,0⟩,
  ⟨2,0,0,0,3⟩,
  ⟨2,0,0,3,0⟩,
  ⟨2,0,3,0,0⟩,
  ⟨0,1,0,0,4⟩,
  ⟨0,1,0,4,0⟩,
  ⟨0,1,4,0,0⟩,
  ⟨1,0,0,0,4⟩,
  ⟨1,0,0,4,0⟩,
  ⟨1,0,4,0,0⟩,
  ⟨0,5,0,0,0⟩,
  ⟨5,0,0,0,0⟩,
  ⟨0,3,0,0,2⟩,
  ⟨3,0,0,0,2⟩,
  ⟨0,2,0,2,1⟩,
  ⟨0,2,2,0,1⟩,
  ⟨0,4,0,0,1⟩,
  ⟨4,0,0,0,1⟩,
  ⟨0,3,0,1,1⟩,
  ⟨0,3,1,0,1⟩,
  ⟨0,3,1,1,0⟩,
  ⟨3,0,0,1,1⟩,
  ⟨3,0,1,0,1⟩,
  ⟨3,0,1,1,0⟩,
  ⟨0,2,0,1,2⟩,
  ⟨0,2,1,0,2⟩,
  ⟨0,2,1,2,0⟩,
  ⟨0,2,2,1,0⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel evaluation checks every normalized triple modulo 26. -/
theorem all_covered26 :
    ((List.range 26).all fun a ↦ (List.range 26).all fun b ↦
      (List.range 26).all fun c ↦ covered 26 rivals26 a b c)=true := by decide


end MinModulus.FiveSmallEvenCertificate
