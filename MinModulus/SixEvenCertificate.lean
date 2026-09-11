import MinModulus.SortedValidTuples
import MinModulus.SixModFiftySixData

namespace MinModulus

theorem exists_unit_difference_of_two_quotient_tests
    {n N p : ℕ} [NeZero N] [NeZero p]
    (hd2 : 2 ∣ N) (hdp : p ∣ N) (hN : N < 2^(n+1))
    (hp : (1 : ZMod p) ≠ 0)
    (hunit : ∀ x y : ZMod N,
      ZMod.castHom hd2 (ZMod 2) x ≠ 0 →
      ZMod.castHom hdp (ZMod p) y ≠ 0 →
      IsUnit x ∨ IsUnit y ∨ IsUnit (x-y))
    (g : Fin (n+1) → ZMod N) (hg : ValidTuple g) :
    ∃ i j, IsUnit (g j-g i) := by
  obtain ⟨a,ha⟩ := exists_nonzero_cast_difference_of_valid_subbinary hd2 g hg hN (by decide)
  obtain ⟨b,hb⟩ := exists_nonzero_cast_difference_of_valid_subbinary hdp g hg hN hp
  rcases hunit (g a-g 0) (g b-g 0) ha hb with h | h | h
  · exact ⟨0,a,h⟩
  · exact ⟨0,b,h⟩
  · exact ⟨b,a,by simpa only [sub_sub_sub_cancel_right] using h⟩

theorem not_validTuple_six_of_two_quotient_sorted_exclusion
    {N p : ℕ} [NeZero N] [NeZero p] [Nontrivial (ZMod N)]
    (hd2 : 2 ∣ N) (hdp : p ∣ N) (hN1 : 1<N) (hN : N<64)
    (hp : (1 : ZMod p) ≠ 0)
    (hunit : ∀ x y : ZMod N,
      ZMod.castHom hd2 (ZMod 2) x ≠ 0 →
      ZMod.castHom hdp (ZMod p) y ≠ 0 →
      IsUnit x ∨ IsUnit y ∨ IsUnit (x-y))
    (hsorted : ∀ a b c d : ℕ, 2≤a → a<b → b<c → c<d → d<N →
      ¬ ValidTuple (![0,1,(a : ZMod N),(b : ZMod N),(c : ZMod N),(d : ZMod N)]))
    (g : Fin 6 → ZMod N) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨i,j,hu⟩ := exists_unit_difference_of_two_quotient_tests hd2 hdp hN hp hunit g hg
  obtain ⟨w,hw,h0,h1⟩ := exists_normalized_valid_of_unit_difference g hg i j hu
  exact not_validTuple_six_normalized_of_sorted_exclusion hN1 hsorted w h0 h1 hw

namespace SixEvenCertificate
open Finset
open MinModulus.SixModFiftySixCertificate (Rival)

def hits (N : ℕ) (r : Rival) (a b c d : ℕ) : Bool :=
  decide ((r.k1+r.k2*a+r.k3*b+r.k4*c+r.k5*d)%N=(1+a+b+c+d)%N)

def covered (N : ℕ) (rivals : List Rival) (a b c d : ℕ) : Bool :=
  rivals.any fun r ↦ r.valid && hits N r a b c d

def coveredRow (N : ℕ) (rivals : List Rival) (a : ℕ) : Bool :=
  (List.range (N-1-a)).all fun y ↦
    let b := a+1+y
    (List.range (N-1-b)).all fun z ↦
      let c := b+1+z
      (List.range (N-1-c)).all fun t ↦ covered N rivals a b c (c+1+t)

def coveredBlock (N : ℕ) (rivals : List Rival) (lo hi : ℕ) : Bool :=
  (List.range (hi-lo)).all fun x ↦ coveredRow N rivals (lo+x)

theorem coveredRow_of_block (N : ℕ) (rivals : List Rival) (lo hi a : ℕ)
    (h : coveredBlock N rivals lo hi=true) (hlo : lo≤a) (hhi : a<hi) :
    coveredRow N rivals a=true := by
  simp only [coveredBlock,List.all_eq_true] at h
  have hh := h (a-lo) (List.mem_range.mpr (by omega))
  simpa only [show lo+(a-lo)=a by omega] using hh

theorem not_validTuple_of_covered (N : ℕ) (rivals : List Rival) (a b c d : ℕ)
    (hc : covered N rivals a b c d=true) :
    ¬ ValidTuple (![0,1,(a : ZMod N),(b : ZMod N),(c : ZMod N),(d : ZMod N)]) := by
  intro hg
  simp only [covered,List.any_eq_true,Bool.and_eq_true] at hc
  obtain ⟨r,_,hvalid,hhit⟩ := hc
  simp only [Rival.valid,decide_eq_true_eq] at hvalid
  simp only [hits,decide_eq_true_eq] at hhit
  have hsum : (∑ i, r.vector i)=6 := by
    simpa [Rival.vector,Fin.sum_univ_succ,add_assoc] using hvalid.1
  have heq : (∑ i, r.vector i • (![0,1,(a : ZMod N),(b : ZMod N),(c : ZMod N),(d : ZMod N)]) i)=
      ∑ i, (![0,1,(a : ZMod N),(b : ZMod N),(c : ZMod N),(d : ZMod N)]) i := by
    have hh : ((r.k1+r.k2*a+r.k3*b+r.k4*c+r.k5*d : ℕ) : ZMod N)=
        ((1+a+b+c+d : ℕ) : ZMod N) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hhit
    simpa [Rival.vector,Fin.sum_univ_succ,nsmul_eq_mul,add_assoc] using hh
  have hone := hg r.vector hsum heq
  apply hvalid.2
  exact ⟨by simpa [Rival.vector] using hone 0,
    by simpa [Rival.vector] using hone 1,
    by simpa [Rival.vector] using hone 2,
    by simpa [Rival.vector] using hone 3,
    by simpa [Rival.vector] using hone 4,
    by simpa [Rival.vector] using hone 5⟩

theorem not_validTuple_sorted (N : ℕ) (rivals : List Rival)
    (hcover : coveredBlock N rivals 2 N=true)
    (a b c d : ℕ) (ha : 2≤a) (hab : a<b) (hbc : b<c) (hcd : c<d) (hd : d<N) :
    ¬ ValidTuple (![0,1,(a : ZMod N),(b : ZMod N),(c : ZMod N),(d : ZMod N)]) := by
  have hh := coveredRow_of_block N rivals 2 N a hcover ha (by omega)
  simp only [coveredRow,List.all_eq_true] at hh
  have hh := hh (b-(a+1)) (List.mem_range.mpr (by omega))
  simp only [show a+1+(b-(a+1))=b by omega] at hh
  have hh := hh (c-(b+1)) (List.mem_range.mpr (by omega))
  simp only [show b+1+(c-(b+1))=c by omega] at hh
  have hh := hh (d-(c+1)) (List.mem_range.mpr (by omega))
  simp only [show c+1+(d-(c+1))=d by omega] at hh
  exact not_validTuple_of_covered N rivals a b c d hh

end SixEvenCertificate




end MinModulus
