import MinModulus.SixModFiftySixData
import MinModulus.CyclicUnitNormalization

namespace MinModulus.SixFortyTwoCertificate
open Finset
open MinModulus.SixModFiftySixCertificate (Rival)

def unitRivals : List Rival := [
  ⟨0,2,1,1,2,0⟩,
  ⟨0,2,1,2,0,1⟩,
  ⟨0,2,2,0,1,1⟩,
  ⟨0,3,0,1,1,1⟩,
  ⟨3,0,1,1,1,0⟩,
  ⟨0,0,2,1,1,2⟩,
  ⟨1,1,0,2,2,0⟩,
  ⟨0,1,1,0,2,2⟩,
  ⟨1,0,2,2,0,1⟩,
  ⟨0,1,0,2,1,2⟩,
  ⟨0,1,1,1,0,3⟩,
  ⟨1,0,2,1,2,0⟩,
  ⟨1,0,3,0,1,1⟩,
  ⟨1,1,0,3,0,1⟩,
  ⟨1,1,1,0,3,0⟩,
  ⟨0,1,2,1,2,0⟩,
  ⟨0,1,2,2,0,1⟩,
  ⟨0,1,3,0,1,1⟩,
  ⟨3,1,0,1,1,0⟩,
  ⟨0,2,0,2,2,0⟩,
  ⟨0,2,0,3,0,1⟩,
  ⟨3,0,2,0,1,0⟩,
  ⟨0,2,1,0,3,0⟩,
  ⟨1,0,1,1,0,3⟩,
  ⟨1,0,0,2,1,2⟩,
  ⟨1,0,1,0,2,2⟩,
  ⟨2,0,1,0,3,0⟩,
  ⟨1,3,0,1,1,0⟩,
  ⟨0,2,2,0,0,2⟩,
  ⟨2,0,0,3,0,1⟩,
  ⟨3,0,1,2,0,0⟩,
  ⟨0,3,0,0,2,1⟩,
  ⟨0,3,0,1,0,2⟩,
  ⟨0,3,2,0,1,0⟩,
  ⟨0,3,1,2,0,0⟩,
  ⟨3,0,0,0,2,1⟩,
  ⟨3,0,0,1,0,2⟩,
  ⟨0,4,0,1,1,0⟩,
  ⟨4,0,0,1,1,0⟩,
  ⟨0,1,0,1,2,2⟩,
  ⟨3,1,1,0,1,0⟩,
  ⟨1,3,0,1,0,1⟩,
  ⟨1,0,2,2,1,0⟩,
  ⟨1,3,0,0,2,0⟩,
  ⟨3,1,0,2,0,0⟩,
  ⟨1,1,0,0,2,2⟩,
  ⟨0,1,3,0,2,0⟩,
  ⟨1,0,0,2,0,3⟩,
  ⟨0,1,3,1,0,1⟩,
  ⟨1,1,3,1,0,0⟩,
  ⟨1,0,3,1,0,1⟩,
  ⟨0,0,2,1,2,1⟩,
  ⟨3,0,2,1,0,0⟩,
  ⟨0,0,3,1,2,0⟩,
  ⟨0,0,3,2,0,1⟩,
  ⟨0,0,2,2,0,2⟩,
  ⟨0,0,1,2,1,2⟩,
  ⟨0,1,1,3,0,1⟩,
  ⟨1,0,1,3,0,1⟩,
  ⟨0,1,1,2,2,0⟩,
  ⟨0,1,1,0,1,3⟩,
  ⟨1,0,3,0,2,0⟩,
  ⟨0,3,0,0,1,2⟩,
  ⟨0,4,0,1,0,1⟩,
  ⟨1,0,0,2,2,1⟩,
  ⟨0,0,0,2,1,3⟩,
  ⟨4,0,1,0,1,0⟩,
  ⟨0,1,0,2,0,3⟩,
  ⟨1,0,1,0,3,1⟩,
  ⟨1,0,1,0,1,3⟩,
  ⟨0,0,1,0,2,3⟩,
  ⟨0,1,2,2,1,0⟩,
  ⟨1,3,1,0,0,1⟩,
  ⟨0,1,1,0,3,1⟩,
  ⟨0,0,0,1,2,3⟩,
  ⟨0,1,2,0,3,0⟩,
  ⟨1,2,0,0,3,0⟩,
  ⟨2,1,0,0,3,0⟩,
  ⟨1,0,0,1,3,1⟩,
  ⟨3,1,1,0,0,1⟩,
  ⟨1,0,0,1,2,2⟩,
  ⟨0,2,0,1,3,0⟩,
  ⟨0,2,2,2,0,0⟩,
  ⟨1,0,1,2,2,0⟩,
  ⟨0,0,3,2,1,0⟩,
  ⟨0,1,0,2,2,1⟩,
  ⟨0,1,0,1,3,1⟩,
  ⟨1,1,0,1,3,0⟩,
  ⟨3,0,0,0,3,0⟩,
  ⟨2,0,0,3,1,0⟩,
  ⟨1,1,0,0,1,3⟩,
  ⟨2,0,3,0,1,0⟩,
  ⟨0,0,2,0,2,2⟩,
  ⟨0,2,0,0,2,2⟩,
  ⟨0,2,0,1,0,3⟩,
  ⟨0,1,1,3,1,0⟩,
  ⟨0,4,2,0,0,0⟩,
  ⟨1,0,0,0,2,3⟩,
  ⟨1,1,0,3,1,0⟩,
  ⟨0,1,0,3,2,0⟩,
  ⟨0,1,3,2,0,0⟩,
  ⟨1,0,0,2,3,0⟩,
  ⟨0,0,0,1,3,2⟩
]

def unitHits (r : Rival) (a b c d : ℕ) : Bool :=
  decide ((r.k1+r.k2*a+r.k3*b+r.k4*c+r.k5*d)%42=(1+a+b+c+d)%42)

def unitCovered (a b c d : ℕ) : Bool :=
  unitRivals.any fun r ↦ r.valid && unitHits r a b c d

def nonunitRivals : List Rival := [
  ⟨3,0,1,1,1,0⟩,
  ⟨0,1,1,1,0,3⟩,
  ⟨0,3,0,1,1,1⟩,
  ⟨1,0,3,0,1,1⟩,
  ⟨1,1,1,0,3,0⟩,
  ⟨1,1,0,3,0,1⟩,
  ⟨0,0,2,1,1,2⟩,
  ⟨1,1,0,2,2,0⟩,
  ⟨1,0,2,1,2,0⟩,
  ⟨1,0,2,2,0,1⟩,
  ⟨0,1,0,2,1,2⟩,
  ⟨0,1,1,0,2,2⟩,
  ⟨0,2,1,2,0,1⟩,
  ⟨0,2,1,1,2,0⟩,
  ⟨0,2,2,0,1,1⟩,
  ⟨0,1,1,0,3,1⟩,
  ⟨3,0,1,1,0,1⟩,
  ⟨3,1,0,1,1,0⟩,
  ⟨0,1,3,0,1,1⟩,
  ⟨0,1,1,0,1,3⟩,
  ⟨0,3,1,0,1,1⟩,
  ⟨3,1,0,1,0,1⟩,
  ⟨0,0,2,1,2,1⟩,
  ⟨0,1,2,1,2,0⟩,
  ⟨3,0,0,2,1,0⟩,
  ⟨3,0,1,2,0,0⟩,
  ⟨0,0,2,0,2,2⟩,
  ⟨0,2,2,0,2,0⟩,
  ⟨0,0,1,2,1,2⟩,
  ⟨1,3,0,1,1,0⟩,
  ⟨1,0,1,1,0,3⟩,
  ⟨0,1,0,2,2,1⟩,
  ⟨1,0,0,2,1,2⟩,
  ⟨1,3,1,0,1,0⟩,
  ⟨1,0,1,0,2,2⟩,
  ⟨0,1,0,1,2,2⟩,
  ⟨3,0,2,0,1,0⟩,
  ⟨0,1,0,2,0,3⟩,
  ⟨0,0,2,1,0,3⟩,
  ⟨3,0,1,0,2,0⟩,
  ⟨0,3,0,1,2,0⟩,
  ⟨0,2,1,2,1,0⟩,
  ⟨0,2,2,1,0,1⟩,
  ⟨0,1,2,2,0,1⟩,
  ⟨1,0,1,3,0,1⟩,
  ⟨1,1,0,3,1,0⟩,
  ⟨1,0,3,1,0,1⟩,
  ⟨1,0,0,1,2,2⟩,
  ⟨1,1,0,1,3,0⟩,
  ⟨0,2,2,0,0,2⟩,
  ⟨1,0,1,2,2,0⟩,
  ⟨1,0,2,2,1,0⟩,
  ⟨0,2,0,0,2,2⟩,
  ⟨1,0,1,0,1,3⟩,
  ⟨0,1,3,1,0,1⟩,
  ⟨0,0,2,2,0,2⟩,
  ⟨0,1,2,2,1,0⟩,
  ⟨0,0,1,2,2,1⟩,
  ⟨0,1,0,1,3,1⟩,
  ⟨1,2,0,0,3,0⟩,
  ⟨0,3,0,0,3,0⟩,
  ⟨0,1,2,0,0,3⟩,
  ⟨0,2,0,2,2,0⟩,
  ⟨1,0,3,0,0,2⟩,
  ⟨0,0,3,0,1,2⟩,
  ⟨0,0,3,0,0,3⟩,
  ⟨0,2,0,1,0,3⟩,
  ⟨0,3,0,0,2,1⟩,
  ⟨0,3,0,1,0,2⟩,
  ⟨0,3,0,2,0,1⟩,
  ⟨2,0,3,0,1,0⟩,
  ⟨0,0,1,1,2,2⟩,
  ⟨0,2,2,1,1,0⟩,
  ⟨2,0,3,1,0,0⟩,
  ⟨1,0,0,2,2,1⟩,
  ⟨2,0,0,1,3,0⟩,
  ⟨0,0,2,2,1,1⟩,
  ⟨0,1,1,2,2,0⟩,
  ⟨1,1,0,0,2,2⟩,
  ⟨0,2,1,0,3,0⟩,
  ⟨2,0,1,0,3,0⟩,
  ⟨0,2,0,0,1,3⟩,
  ⟨0,3,1,0,0,2⟩,
  ⟨1,1,0,0,1,3⟩,
  ⟨1,3,1,0,0,1⟩,
  ⟨1,0,0,1,1,3⟩,
  ⟨1,3,1,1,0,0⟩,
  ⟨1,0,1,3,1,0⟩,
  ⟨1,0,1,0,3,1⟩,
  ⟨1,0,1,1,3,0⟩,
  ⟨0,3,1,1,0,1⟩,
  ⟨1,0,0,1,3,1⟩,
  ⟨0,1,0,1,1,3⟩,
  ⟨1,1,3,1,0,0⟩,
  ⟨0,1,0,0,3,2⟩,
  ⟨0,2,3,0,0,1⟩,
  ⟨1,0,3,1,1,0⟩,
  ⟨1,1,3,0,1,0⟩,
  ⟨0,0,0,2,2,2⟩,
  ⟨0,1,0,3,1,1⟩,
  ⟨2,1,3,0,0,0⟩,
  ⟨0,3,2,1,0,0⟩,
  ⟨1,3,0,1,0,1⟩,
  ⟨0,1,2,0,3,0⟩,
  ⟨0,0,2,0,3,1⟩,
  ⟨1,0,3,0,2,0⟩,
  ⟨0,0,2,2,2,0⟩,
  ⟨1,0,2,0,3,0⟩,
  ⟨3,1,1,0,1,0⟩,
  ⟨0,0,0,1,2,3⟩,
  ⟨1,1,0,1,0,3⟩,
  ⟨0,0,1,0,2,3⟩,
  ⟨0,1,0,2,3,0⟩,
  ⟨3,0,1,0,1,1⟩,
  ⟨0,0,3,2,0,1⟩,
  ⟨0,1,1,3,0,1⟩,
  ⟨0,0,1,3,1,1⟩,
  ⟨0,1,3,0,2,0⟩,
  ⟨1,0,0,2,3,0⟩,
  ⟨0,0,0,0,5,1⟩,
  ⟨0,0,0,3,3,0⟩,
  ⟨0,0,1,1,3,1⟩,
  ⟨0,0,3,1,0,2⟩
]

def nonunitHits (r : Rival) (a b c d e : ℕ) : Bool :=
  decide ((r.k1*a+r.k2*b+r.k3*c+r.k4*d+r.k5*e)%42=(a+b+c+d+e)%42)

def nonunitCovered (a b c d e : ℕ) : Bool :=
  nonunitRivals.any fun r ↦ r.valid && nonunitHits r a b c d e

def unitRow (a : ℕ) : Bool :=
  (List.range (41-a)).all fun y ↦
    let b := a+1+y
    (List.range (41-b)).all fun z ↦
      let c := b+1+z
      (List.range (41-c)).all fun t ↦ unitCovered a b c (c+1+t)

def nonunitRow (a : ℕ) : Bool :=
  if Nat.gcd a 42=1 then true else
  (List.range (41-a)).all fun y ↦
    let b := a+1+y
    if Nat.gcd b 42=1 then true else
    (List.range (41-b)).all fun z ↦
      let c := b+1+z
      if Nat.gcd c 42=1 then true else
      (List.range (41-c)).all fun t ↦
        let d := c+1+t
        if Nat.gcd d 42=1 then true else
        (List.range (41-d)).all fun u ↦
          let e := d+1+u
          if Nat.gcd e 42=1 then true else nonunitCovered a b c d e

def unitBlock (lo hi : ℕ) : Bool :=
  (List.range (hi-lo)).all fun x ↦ unitRow (lo+x)

def nonunitBlock (lo hi : ℕ) : Bool :=
  (List.range (hi-lo)).all fun x ↦ nonunitRow (lo+x)

theorem not_validTuple_of_unitCovered (a b c d : ℕ)
    (hc : unitCovered a b c d=true) : ¬ ValidTuple (![((0) : ZMod 42),((1) : ZMod 42),((a) : ZMod 42),((b) : ZMod 42),((c) : ZMod 42),((d) : ZMod 42)]) := by
  intro hg
  simp only [unitCovered,List.any_eq_true,Bool.and_eq_true] at hc
  obtain ⟨r,_,hvalid,hhit⟩ := hc
  simp only [Rival.valid,decide_eq_true_eq] at hvalid
  simp only [unitHits,decide_eq_true_eq] at hhit
  have hsum : (∑ i, r.vector i)=6 := by
    simpa [Rival.vector,Fin.sum_univ_succ,add_assoc] using hvalid.1
  have heq : (∑ i, r.vector i • (![((0) : ZMod 42),((1) : ZMod 42),((a) : ZMod 42),((b) : ZMod 42),((c) : ZMod 42),((d) : ZMod 42)]) i)=∑ i, (![((0) : ZMod 42),((1) : ZMod 42),((a) : ZMod 42),((b) : ZMod 42),((c) : ZMod 42),((d) : ZMod 42)]) i := by
    have hh : ((r.k1+r.k2*a+r.k3*b+r.k4*c+r.k5*d : ℕ) : ZMod 42)=((1+a+b+c+d : ℕ) : ZMod 42) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hhit
    simpa [Rival.vector,Fin.sum_univ_succ,nsmul_eq_mul,add_assoc] using hh
  have hone := hg r.vector hsum heq
  apply hvalid.2
  exact ⟨by simpa [Rival.vector] using hone 0,
    by simpa [Rival.vector] using hone 1,
    by simpa [Rival.vector] using hone 2,
    by simpa [Rival.vector] using hone 3,
    by simpa [Rival.vector] using hone 4,
    by simpa [Rival.vector] using hone 5⟩

theorem unitRow_of_block (lo hi a : ℕ) (h : unitBlock lo hi=true)
    (hlo : lo≤a) (hhi : a<hi) : unitRow a=true := by
  simp only [unitBlock,List.all_eq_true] at h
  have hh := h (a-lo) (List.mem_range.mpr (by omega))
  simpa only [show lo+(a-lo)=a by omega] using hh

theorem not_validTuple_of_nonunitCovered (a b c d e : ℕ)
    (hc : nonunitCovered a b c d e=true) : ¬ ValidTuple (![((0) : ZMod 42),((a) : ZMod 42),((b) : ZMod 42),((c) : ZMod 42),((d) : ZMod 42),((e) : ZMod 42)]) := by
  intro hg
  simp only [nonunitCovered,List.any_eq_true,Bool.and_eq_true] at hc
  obtain ⟨r,_,hvalid,hhit⟩ := hc
  simp only [Rival.valid,decide_eq_true_eq] at hvalid
  simp only [nonunitHits,decide_eq_true_eq] at hhit
  have hsum : (∑ i, r.vector i)=6 := by
    simpa [Rival.vector,Fin.sum_univ_succ,add_assoc] using hvalid.1
  have heq : (∑ i, r.vector i • (![((0) : ZMod 42),((a) : ZMod 42),((b) : ZMod 42),((c) : ZMod 42),((d) : ZMod 42),((e) : ZMod 42)]) i)=∑ i, (![((0) : ZMod 42),((a) : ZMod 42),((b) : ZMod 42),((c) : ZMod 42),((d) : ZMod 42),((e) : ZMod 42)]) i := by
    have hh : ((r.k1*a+r.k2*b+r.k3*c+r.k4*d+r.k5*e : ℕ) : ZMod 42)=((a+b+c+d+e : ℕ) : ZMod 42) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hhit
    simpa [Rival.vector,Fin.sum_univ_succ,nsmul_eq_mul,add_assoc] using hh
  have hone := hg r.vector hsum heq
  apply hvalid.2
  exact ⟨by simpa [Rival.vector] using hone 0,
    by simpa [Rival.vector] using hone 1,
    by simpa [Rival.vector] using hone 2,
    by simpa [Rival.vector] using hone 3,
    by simpa [Rival.vector] using hone 4,
    by simpa [Rival.vector] using hone 5⟩

theorem nonunitRow_of_block (lo hi a : ℕ) (h : nonunitBlock lo hi=true)
    (hlo : lo≤a) (hhi : a<hi) : nonunitRow a=true := by
  simp only [nonunitBlock,List.all_eq_true] at h
  have hh := h (a-lo) (List.mem_range.mpr (by omega))
  simpa only [show lo+(a-lo)=a by omega] using hh

theorem not_validTuple_unit_sorted (hcover : unitBlock 2 42=true)
    (a b c d : ℕ) (ha : 2≤a) (hab : a<b) (hbc : b<c) (hcd : c<d) (hd : d<42) :
    ¬ ValidTuple (![0,1,(a : ZMod 42),(b : ZMod 42),(c : ZMod 42),(d : ZMod 42)]) := by
  have hh := unitRow_of_block 2 42 a hcover ha (by omega)
  simp only [unitRow,List.all_eq_true] at hh
  have hh := hh (b-(a+1)) (List.mem_range.mpr (by omega))
  simp only [show a+1+(b-(a+1))=b by omega] at hh
  have hh := hh (c-(b+1)) (List.mem_range.mpr (by omega))
  simp only [show b+1+(c-(b+1))=c by omega] at hh
  have hh := hh (d-(c+1)) (List.mem_range.mpr (by omega))
  simp only [show c+1+(d-(c+1))=d by omega] at hh
  exact not_validTuple_of_unitCovered a b c d hh

theorem not_validTuple_nonunit_sorted (hcover : nonunitBlock 1 42=true)
    (a b c d e : ℕ) (ha : 1≤a) (hab : a<b) (hbc : b<c) (hcd : c<d) (hde : d<e) (he : e<42)
    (hga : Nat.gcd a 42≠1) (hgb : Nat.gcd b 42≠1) (hgc : Nat.gcd c 42≠1)
    (hgd : Nat.gcd d 42≠1) (hge : Nat.gcd e 42≠1) :
    ¬ ValidTuple (![0,(a : ZMod 42),(b : ZMod 42),(c : ZMod 42),(d : ZMod 42),(e : ZMod 42)]) := by
  have hh := nonunitRow_of_block 1 42 a hcover ha (by omega)
  simp only [nonunitRow,if_neg hga,List.all_eq_true] at hh
  have hh := hh (b-(a+1)) (List.mem_range.mpr (by omega))
  simp only [show a+1+(b-(a+1))=b by omega,if_neg hgb,List.all_eq_true] at hh
  have hh := hh (c-(b+1)) (List.mem_range.mpr (by omega))
  simp only [show b+1+(c-(b+1))=c by omega,if_neg hgc,List.all_eq_true] at hh
  have hh := hh (d-(c+1)) (List.mem_range.mpr (by omega))
  simp only [show c+1+(d-(c+1))=d by omega,if_neg hgd,List.all_eq_true] at hh
  have hh := hh (e-(d+1)) (List.mem_range.mpr (by omega))
  simp only [show d+1+(e-(d+1))=e by omega,if_neg hge] at hh
  exact not_validTuple_of_nonunitCovered a b c d e hh



end MinModulus.SixFortyTwoCertificate
