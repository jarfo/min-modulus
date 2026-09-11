import MinModulus.AbelianMin

namespace MinModulus.SixModFiftySixCertificate
open Finset

/-- Natural multiplicity data; every candidate is checked by the kernel. -/
structure Rival where
  k0 : ℕ
  k1 : ℕ
  k2 : ℕ
  k3 : ℕ
  k4 : ℕ
  k5 : ℕ

def Rival.vector (r : Rival) : Fin 6 → ℕ := ![r.k0,r.k1,r.k2,r.k3,r.k4,r.k5]
def Rival.valid (r : Rival) : Bool :=
  decide (r.k0+r.k1+r.k2+r.k3+r.k4+r.k5=6 ∧
    ¬ (r.k0=1 ∧ r.k1=1 ∧ r.k2=1 ∧ r.k3=1 ∧ r.k4=1 ∧ r.k5=1))
def Rival.hits (r : Rival) (a b c d : ℕ) : Bool :=
  decide ((r.k1+r.k2*a+r.k3*b+r.k4*c+r.k5*d)%56=(1+a+b+c+d)%56)
def rivals : List Rival := [
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
  ⟨0,0,0,2,1,3⟩,
  ⟨0,0,1,0,2,3⟩,
  ⟨0,1,0,1,2,2⟩,
  ⟨3,1,1,0,1,0⟩,
  ⟨3,1,0,2,0,0⟩,
  ⟨3,0,2,1,0,0⟩,
  ⟨0,1,0,2,0,3⟩,
  ⟨0,1,1,0,1,3⟩,
  ⟨1,3,0,1,0,1⟩,
  ⟨0,0,1,2,1,2⟩,
  ⟨1,0,2,2,1,0⟩,
  ⟨1,0,0,2,0,3⟩,
  ⟨1,0,0,2,2,1⟩,
  ⟨1,0,1,0,3,1⟩,
  ⟨0,0,3,2,0,1⟩,
  ⟨1,1,0,0,2,2⟩,
  ⟨1,3,0,0,2,0⟩,
  ⟨1,0,3,1,0,1⟩,
  ⟨0,3,0,0,1,2⟩,
  ⟨1,0,3,0,2,0⟩,
  ⟨0,0,3,1,2,0⟩,
  ⟨0,0,2,1,2,1⟩,
  ⟨0,1,1,2,2,0⟩,
  ⟨0,1,3,0,2,0⟩,
  ⟨0,4,0,1,0,1⟩,
  ⟨1,1,0,1,0,3⟩,
  ⟨0,1,2,0,3,0⟩,
  ⟨1,1,0,1,3,0⟩,
  ⟨1,1,3,1,0,0⟩,
  ⟨0,1,3,1,0,1⟩,
  ⟨1,1,3,0,1,0⟩,
  ⟨1,0,0,1,2,2⟩,
  ⟨2,1,0,0,3,0⟩,
  ⟨0,1,1,0,3,1⟩,
  ⟨0,2,2,2,0,0⟩,
  ⟨1,0,1,0,1,3⟩,
  ⟨1,1,0,3,1,0⟩,
  ⟨0,1,1,3,0,1⟩,
  ⟨0,1,2,2,1,0⟩,
  ⟨1,0,1,3,0,1⟩,
  ⟨1,1,0,0,1,3⟩,
  ⟨1,0,1,2,2,0⟩,
  ⟨1,0,0,1,3,1⟩,
  ⟨0,1,0,2,2,1⟩,
  ⟨3,1,1,0,0,1⟩,
  ⟨1,3,1,0,0,1⟩,
  ⟨0,3,2,0,0,1⟩,
  ⟨3,0,1,0,0,2⟩,
  ⟨4,0,1,0,1,0⟩,
  ⟨0,1,1,3,1,0⟩,
  ⟨0,1,0,1,3,1⟩,
  ⟨0,0,1,2,2,1⟩,
  ⟨0,0,0,1,2,3⟩,
  ⟨0,0,2,2,2,0⟩,
  ⟨1,0,3,0,0,2⟩,
  ⟨0,2,0,1,3,0⟩,
  ⟨0,1,2,0,0,3⟩,
  ⟨0,0,0,2,2,2⟩,
  ⟨3,1,0,1,0,1⟩,
  ⟨0,0,2,0,2,2⟩,
  ⟨0,0,2,2,0,2⟩,
  ⟨1,0,0,3,0,2⟩,
  ⟨2,0,0,3,1,0⟩,
  ⟨1,2,0,3,0,0⟩,
  ⟨1,0,1,3,1,0⟩,
  ⟨1,3,1,0,1,0⟩,
  ⟨3,1,1,1,0,0⟩,
  ⟨2,3,0,1,0,0⟩,
  ⟨1,3,0,0,1,1⟩,
  ⟨3,2,0,0,1,0⟩,
  ⟨1,2,0,0,3,0⟩,
  ⟨2,1,0,3,0,0⟩,
  ⟨0,2,0,0,2,2⟩,
  ⟨3,1,0,0,2,0⟩,
  ⟨1,3,0,2,0,0⟩,
  ⟨1,3,2,0,0,0⟩,
  ⟨2,3,0,0,1,0⟩,
  ⟨3,1,0,0,0,2⟩,
  ⟨3,2,0,1,0,0⟩,
  ⟨4,0,0,2,0,0⟩,
  ⟨0,4,0,0,2,0⟩,
  ⟨0,0,2,0,3,1⟩,
  ⟨2,3,1,0,0,0⟩,
  ⟨3,1,2,0,0,0⟩,
  ⟨0,0,1,3,0,2⟩,
  ⟨0,1,0,3,2,0⟩,
  ⟨2,0,3,0,1,0⟩,
  ⟨2,1,3,0,0,0⟩,
  ⟨1,2,0,0,0,3⟩,
  ⟨0,1,0,1,1,3⟩,
  ⟨1,0,3,1,1,0⟩,
  ⟨1,0,0,1,1,3⟩,
  ⟨3,2,0,0,0,1⟩,
  ⟨0,1,3,1,1,0⟩,
  ⟨0,2,0,1,0,3⟩,
  ⟨1,3,0,0,0,2⟩,
  ⟨1,0,0,0,3,2⟩,
  ⟨0,1,2,3,0,0⟩,
  ⟨0,0,3,2,1,0⟩,
  ⟨0,1,0,0,2,3⟩,
  ⟨1,0,3,2,0,0⟩,
  ⟨0,0,3,0,1,2⟩,
  ⟨5,0,0,0,1,0⟩,
  ⟨1,5,0,0,0,0⟩,
  ⟨5,1,0,0,0,0⟩,
  ⟨0,0,2,1,0,3⟩,
  ⟨0,0,1,1,2,2⟩,
  ⟨3,1,0,0,1,1⟩,
  ⟨1,1,1,3,0,0⟩,
  ⟨1,1,0,0,3,1⟩,
  ⟨1,3,1,1,0,0⟩,
  ⟨0,0,0,3,1,2⟩,
  ⟨1,1,3,0,0,1⟩,
  ⟨0,1,0,3,0,2⟩,
  ⟨1,0,0,3,1,1⟩,
  ⟨0,0,2,2,1,1⟩,
  ⟨0,1,0,3,1,1⟩,
  ⟨1,0,1,1,3,0⟩,
  ⟨0,1,1,1,3,0⟩,
  ⟨0,3,2,1,0,0⟩,
  ⟨3,0,0,0,1,2⟩,
  ⟨0,1,0,0,3,2⟩,
  ⟨1,0,0,2,3,0⟩,
  ⟨1,1,1,0,0,3⟩,
  ⟨1,0,2,3,0,0⟩,
  ⟨3,0,2,0,0,1⟩,
  ⟨0,3,1,0,0,2⟩,
  ⟨1,0,2,0,3,0⟩,
  ⟨0,1,0,0,5,0⟩,
  ⟨0,0,2,1,3,0⟩,
  ⟨0,1,0,0,0,5⟩,
  ⟨0,0,1,3,2,0⟩,
  ⟨1,0,0,0,1,4⟩,
  ⟨1,2,3,0,0,0⟩,
  ⟨1,4,0,0,0,1⟩,
  ⟨0,0,0,2,3,1⟩,
  ⟨0,1,1,0,4,0⟩,
  ⟨0,1,3,0,0,2⟩,
  ⟨4,1,0,0,1,0⟩,
  ⟨0,0,0,0,3,3⟩,
  ⟨0,0,0,3,0,3⟩,
  ⟨0,1,0,4,1,0⟩,
  ⟨0,2,0,0,3,1⟩,
  ⟨0,5,0,0,1,0⟩,
  ⟨1,0,0,3,2,0⟩,
  ⟨1,0,0,4,0,1⟩,
  ⟨1,1,0,4,0,0⟩,
  ⟨2,0,0,1,0,3⟩,
  ⟨0,0,1,2,3,0⟩,
  ⟨0,0,1,4,1,0⟩,
  ⟨0,1,0,0,1,4⟩,
  ⟨0,1,0,0,4,1⟩,
  ⟨0,1,0,1,0,4⟩,
  ⟨0,1,0,1,4,0⟩,
  ⟨0,1,4,1,0,0⟩,
  ⟨0,5,0,0,0,1⟩,
  ⟨0,5,0,1,0,0⟩,
  ⟨1,0,0,0,5,0⟩,
  ⟨1,0,0,1,4,0⟩,
  ⟨1,0,0,4,1,0⟩,
  ⟨1,0,1,4,0,0⟩,
  ⟨1,1,0,0,4,0⟩,
  ⟨5,0,0,1,0,0⟩,
  ⟨5,0,1,0,0,0⟩]
def covered (a b c d : ℕ) : Bool :=
  rivals.any fun r ↦ r.valid && r.hits a b c d

def coveredRow (a : ℕ) : Bool :=
  (List.range (55-a)).all fun y ↦
    let b := a+1+y
    (List.range (55-b)).all fun z ↦
      let c := b+1+z
      (List.range (55-c)).all fun t ↦ covered a b c (c+1+t)

def coveredBlock (lo hi : ℕ) : Bool :=
  (List.range (hi-lo)).all fun x ↦ coveredRow (lo+x)

/-- A checked interval includes every row whose index lies inside it. -/
theorem coveredRow_of_block (lo hi a : ℕ) (h : coveredBlock lo hi=true)
    (hlo : lo ≤ a) (hhi : a < hi) : coveredRow a=true := by
  simp only [coveredBlock,List.all_eq_true] at h
  have hh := h (a-lo) (List.mem_range.mpr (by omega))
  simpa only [show lo+(a-lo)=a by omega] using hh

theorem not_validTuple_of_covered (a b c d : ℕ) (hc : covered a b c d = true) :
    ¬ ValidTuple (![0,1,(a : ZMod 56),(b : ZMod 56),(c : ZMod 56),(d : ZMod 56)]) := by
  intro hg
  simp only [covered,List.any_eq_true,Bool.and_eq_true] at hc
  obtain ⟨r,_,hvalid,hhit⟩ := hc
  simp only [Rival.valid,decide_eq_true_eq] at hvalid
  simp only [Rival.hits,decide_eq_true_eq] at hhit
  have hsum : (∑ i, r.vector i)=6 := by
    simpa [Rival.vector,Fin.sum_univ_succ,add_assoc] using hvalid.1
  have heq : (∑ i, r.vector i • (![0,1,(a : ZMod 56),(b : ZMod 56),(c : ZMod 56),(d : ZMod 56)]) i)=
      ∑ i, (![0,1,(a : ZMod 56),(b : ZMod 56),(c : ZMod 56),(d : ZMod 56)]) i := by
    have hh : ((r.k1+r.k2*a+r.k3*b+r.k4*c+r.k5*d : ℕ) : ZMod 56)=
        ((1+a+b+c+d : ℕ) : ZMod 56) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hhit
    simpa [Rival.vector,Fin.sum_univ_succ,nsmul_eq_mul,add_assoc] using hh
  have hone := hg r.vector hsum heq
  apply hvalid.2
  exact ⟨by simpa [Rival.vector] using hone 0,
    by simpa [Rival.vector] using hone 1,
    by simpa [Rival.vector] using hone 2,
    by simpa [Rival.vector] using hone 3,
    by simpa [Rival.vector] using hone 4,
    by simpa [Rival.vector] using hone 5⟩

theorem not_validTuple_sorted
    (hcover : ((List.range 54).all fun x ↦
      let a := x+2
      (List.range (55-a)).all fun y ↦
        let b := a+1+y
        (List.range (55-b)).all fun z ↦
          let c := b+1+z
          (List.range (55-c)).all fun t ↦
            covered a b c (c+1+t)) = true)
    (a b c d : ℕ) (ha : 2 ≤ a) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hd : d < 56) :
    ¬ ValidTuple (![0,1,(a : ZMod 56),(b : ZMod 56),(c : ZMod 56),(d : ZMod 56)]) := by
  simp only [List.all_eq_true] at hcover
  have hh := hcover (a-2) (List.mem_range.mpr (by omega))
  simp only [show a-2+2=a by omega] at hh
  have hh := hh (b-(a+1)) (List.mem_range.mpr (by omega))
  simp only [show a+1+(b-(a+1))=b by omega] at hh
  have hh := hh (c-(b+1)) (List.mem_range.mpr (by omega))
  simp only [show b+1+(c-(b+1))=c by omega] at hh
  have hh := hh (d-(c+1)) (List.mem_range.mpr (by omega))
  simp only [show c+1+(d-(c+1))=d by omega] at hh
  exact not_validTuple_of_covered a b c d hh

end MinModulus.SixModFiftySixCertificate
