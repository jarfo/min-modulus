import MinModulus.OneEscapeCycleSize

/-!
# Full-depth fork rivals from actual two-chain data

Two separate binary chains realize every joint coin count between their
initial count and their total integer weight. Nonstandard weights at the
original tuple sum therefore give an actual rival, without quotient lifting.

At N=(2^L-1)*2^A with A+L<2^A, an A-arm merging into an L-chain at a
position B with A<=B<L cannot be valid. Actual distinct predecessors
extract the discrepancy's full order 2^A. Cyclicity then gives a bounded
coefficient t; when t>0 the rival weights are t-1 and 2^(B-A)*(2^A-t).
When t=0 the long chain is a zero-sum fibre and short-chain refinement
already contradicts the same strict budget. No unit assumption is used.

Affine reindexing and a direct exceptional G3 consumer are included.
This closes the full-dyadic-depth fork family, not arbitrary acyclic
one-escape extraction or forks with a shorter arm than the dyadic depth.
The same three unrestricted global gates remain open.
-/

namespace MinModulus
open Finset

/-- Binary refinement in two separate chains reaches every joint coin
count between the initial count and the sum of the two integer weights. -/
theorem exists_two_chain_representations_of_joint_budget
    {A L X Y K : ℕ} (u v : ℕ → ℕ)
    (hu : val A u=X) (hv : val L v=Y)
    (hlow : dsum A u+dsum L v ≤ K) (hhigh : K ≤ X+Y) :
    ∃ u' v' : ℕ → ℕ, val A u'=X ∧ val L v'=Y ∧ dsum A u'+dsum L v'=K := by
  let U := min X (K-dsum L v)
  have huX : dsum A u ≤ X := by simpa only [hu] using dsum_le_val A u
  have hvY : dsum L v ≤ Y := by simpa only [hv] using dsum_le_val L v
  have huU : dsum A u ≤ U := by dsimp only [U]; omega
  have hUX : U ≤ X := min_le_left _ _
  have hvV : dsum L v ≤ K-U := by dsimp only [U]; omega
  have hVY : K-U ≤ Y := by dsimp only [U]; omega
  obtain ⟨u',hu',hdu⟩ := exists_dsum_eq ⟨u,hu,huU⟩ hUX
  obtain ⟨v',hv',hdv⟩ := exists_dsum_eq ⟨v,hv,hvV⟩ hVY
  refine ⟨u',v',hu',hv',?_⟩
  rw [hdu,hdv]
  dsimp only [U]
  omega

/-- Two nonstandard binary weights at the actual tuple sum give an
original-modulus rival as soon as their coin intervals reach full length.
The first chain's integer weight is preserved during refinement, so the
rival cannot become the all-ones multiset. -/
theorem not_validTuple_of_two_chain_integer_weights
    {A L X Y : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (A+L) → G) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (u v : ℕ → ℕ) (hu : val A u=X) (hv : val L v=Y)
    (hlow : dsum A u+dsum L v ≤ A+L) (hhigh : A+L ≤ X+Y)
    (hneq : X ≠ 2^A-1)
    (hsum : X • x+Y • y=(2^A-1) • x+(2^L-1) • y) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨u',v',hu',hv',hcard⟩ := exists_two_chain_representations_of_joint_budget u v hu hv hlow hhigh
  let c : Fin (A+L) → ℕ := Fin.addCases (fun i ↦ u' i.val) (fun i ↦ v' i.val)
  have hc : (∑ i, c i)=A+L := by
    rw [Fin.sum_univ_add]
    simpa only [c,Fin.addCases_left,Fin.addCases_right,Fin.sum_univ_eq_sum_range,dsum] using hcard
  have hchain_sum (k : ℕ) (z : G) : (∑ i : Fin k, 2^i.val • z)=(2^k-1) • z := by
    rw [← Finset.sum_smul,sum_binary_powers]
  have hcoeff_sum (k : ℕ) (w : ℕ → ℕ) (z : G) :
      (∑ i : Fin k, w i.val • (2^i.val • z))=val k w • z := by
    simp only [smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun i ↦ w i*2^i) k
  have hcsum : (∑ i, c i • g i)=∑ i, g i := by
    rw [Fin.sum_univ_add,Fin.sum_univ_add]
    simp only [c,Fin.addCases_left,Fin.addCases_right,hleft,hright]
    rw [hcoeff_sum,hcoeff_sum,hu',hv',hchain_sum,hchain_sum,hsum]
  have hone := hg c hc hcsum
  have hones : ∀ i < A, u' i=1 := by
    intro i hi
    simpa only [c,Fin.addCases_left] using hone (Fin.castAdd L (⟨i,hi⟩ : Fin A))
  apply hneq
  rw [← hu']
  unfold val
  calc
    _=∑ i ∈ Finset.range A, 2^i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hones i (Finset.mem_range.mp hi),one_mul]
    _=2^A-1 := sum_two_pow A

/-- Any two weights below their binary ranges start with at most the
total chain length in coins. No greedy-count or census premise remains. -/
theorem not_validTuple_of_two_chain_small_integer_weights
    {A L X Y : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (A+L) → G) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hX : X < 2^A) (hY : Y < 2^L) (hhigh : A+L ≤ X+Y)
    (hneq : X ≠ 2^A-1)
    (hsum : X • x+Y • y=(2^A-1) • x+(2^L-1) • y) : ¬ ValidTuple g := by
  obtain ⟨u,_,hu,hdu⟩ := exists_rep_le A X hX
  obtain ⟨v,_,hv,hdv⟩ := exists_rep_le L Y hY
  exact not_validTuple_of_two_chain_integer_weights g x y hleft hright u v hu hv
    (by omega) hhigh hneq hsum

/-- An element of full kernel order represents every canonically scaled
element with a coefficient below that order, including nonunit seeds. -/
theorem exists_bounded_coefficient_of_full_cyclic_kernel_order
    {d M : ℕ} [NeZero d] [NeZero (M*d)]
    (z y : ZMod (M*d)) (hz : addOrderOf z=d) :
    ∃ t : ℕ, t<d ∧ t • z=M • y := by
  obtain ⟨τ,hτ,hτone⟩ := exists_cyclic_subgroup_hom_of_addOrderOf z hz
  have hzero : ZMod.castHom (dvd_mul_right M d) (ZMod M) (M • y)=0 := by
    rw [map_nsmul]
    simp [nsmul_eq_mul]
  obtain ⟨w,hw⟩ := exists_cyclic_hom_preimage_of_castHom_eq_zero τ hτ (M • y) hzero
  refine ⟨w.val,w.val_lt,?_⟩
  rw [← hτone,← map_nsmul]
  simpa [nsmul_eq_mul] using hw

/-- A calibrated fork at the uncapped dyadic endpoint has a rival whenever
its short arm's binary weight exceeds the whole tuple length. The zero
coefficient case is a genuine zero-sum fibre; positive coefficients give
two bounded, nonstandard integer weights and a full-length refinement. -/
theorem not_validTuple_of_calibrated_full_depth_fork
    {A B L : ℕ} (hAB : A ≤ B) (hBL : B < L) (hsize : A+L < 2^A)
    {G : Type*} [AddCommGroup G]
    (g : Fin (A+L) → G) (x y z : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hx : x=2^(B-A) • y+z) (hkill : 2^A • z=0)
    (hcal : ∃ t : ℕ, t<2^A ∧ t • z=(2^L-1) • y) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨t,ht,hcal⟩ := hcal
  by_cases ht0 : t=0
  · have hyzero : (2^L-1) • y=0 := by simpa only [ht0,zero_smul] using hcal.symm
    let f : Fin (L+A) → G := fun i ↦ g (finAddFlip i)
    have hf : ValidTuple f := validTuple_embedding finAddFlip.toEmbedding g hg
    have hfzero : (∑ i : Fin L, f (Fin.castAdd A i))=0 := by
      simp only [f,finAddFlip_apply_castAdd,hright]
      rw [← Finset.sum_smul,sum_binary_powers,hyzero]
    have hfchain : ∀ i : Fin A, f (Fin.natAdd L i)=2^i.val • x := by
      intro i
      simpa only [f,finAddFlip_apply_natAdd] using hleft i
    have hb := two_pow_chain_le_length_of_valid_zero_sum_fibre (by omega) f hf hfzero x hfchain
    omega
  · have htpos : 0 < t := by omega
    have hdpos : 0 < 2^A := by positivity
    have hvpos : 0 < 2^(B-A) := by positivity
    have hvd : 2^(B-A)*2^A=2^B := by rw [← pow_add,Nat.sub_add_cancel hAB]
    let X := t-1
    let Y := 2^(B-A)*(2^A-t)
    have hX : X < 2^A := by dsimp only [X]; omega
    have hY : Y < 2^L := by
      have hlt : Y < 2^B := by
        dsimp only [Y]
        rw [← hvd]
        exact Nat.mul_lt_mul_of_pos_left (by omega) hvpos
      have hp := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : B ≤ L)
      omega
    have hhigh : A+L ≤ X+Y := by
      have hle : 2^A-t ≤ Y := by dsimp only [Y]; nlinarith
      dsimp only [X]
      omega
    have hneq : X ≠ 2^A-1 := by dsimp only [X]; omega
    have hcoef : X*2^(B-A)+Y=(2^A-1)*2^(B-A) := by
      dsimp only [X,Y]
      calc
        _=((t-1)+(2^A-t))*2^(B-A) := by ring
        _=_ := by congr 1; omega
    have htz : X • z+z=(2^L-1) • y := by
      rw [← succ_nsmul,show X+1=t by dsimp only [X]; omega,hcal]
    have hdz : (2^A-1) • z+z=0 := by
      rw [← succ_nsmul,Nat.sub_add_cancel (by omega : 1 ≤ 2^A),hkill]
    have hsum : X • x+Y • y=(2^A-1) • x+(2^L-1) • y := by
      have hleftsum : X • x+Y • y=((2^A-1)*2^(B-A)) • y+X • z := by
        rw [hx,smul_add,smul_smul]
        calc
          _=(X*2^(B-A)) • y+Y • y+X • z := by abel
          _=_ := by rw [← add_nsmul,hcoef]
      apply add_right_cancel (b := z)
      rw [hleftsum,hx,smul_add,smul_smul]
      calc
        _=((2^A-1)*2^(B-A)) • y+(X • z+z) := by abel
        _=((2^A-1)*2^(B-A)) • y+(2^L-1) • y := by rw [htz]
        _=((2^A-1)*2^(B-A)) • y+((2^A-1) • z+z)+(2^L-1) • y := by rw [hdz,add_zero]
        _=_ := by abel
    exact not_validTuple_of_two_chain_small_integer_weights g x y hleft hright hX hY hhigh hneq hsum hg

/-- The actual distinct predecessors at a fork extract the full dyadic
order of its seed discrepancy. No unit multiplier or exact-order premise
is needed beyond validity and the actual merge relation. -/
theorem addOrderOf_fork_discrepancy_of_valid
    {A B L : ℕ} (hA : 0 < A) (hAB : A ≤ B) (hBL : B < L)
    {G : Type*} [AddCommGroup G]
    (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hmerge : 2^A • x=2^B • y) : addOrderOf (x-2^(B-A) • y)=2^A := by
  have hkill : 2^A • (x-2^(B-A) • y)=0 := by
    rw [smul_sub,smul_smul,← pow_add,show A+(B-A)=B by omega,hmerge,sub_self]
  have hnot : 2^(A-1) • (x-2^(B-A) • y) ≠ 0 := by
    intro hz
    rw [smul_sub,smul_smul,← pow_add,show A-1+(B-A)=B-1 by omega,sub_eq_zero] at hz
    let i : Fin A := ⟨A-1,by omega⟩
    let j : Fin L := ⟨B-1,by omega⟩
    have heq : g (Fin.castAdd L i)=g (Fin.natAdd A j) := by
      rw [hleft,hright]
      exact hz
    have he := congrArg Fin.val (validTuple_injective g hg heq)
    simp only [Fin.val_castAdd,Fin.val_natAdd,i,j] at he
    omega
  have hAform : A-1+1=A := by omega
  have h := addOrderOf_eq_prime_pow (p := 2) (n := A-1) hnot (by rwa [hAform])
  simpa only [hAform] using h

/-- Full-depth acyclic fork exclusion at the uncapped endpoint. All
seeds and multipliers are arbitrary: validity extracts the discrepancy's
full kernel order, cyclicity extracts its bounded calibration coefficient,
and two-chain refinement constructs the actual rival. -/
theorem not_validTuple_of_full_depth_fork
    {A B L : ℕ} (hAB : A ≤ B) (hBL : B < L) (hsize : A+L < 2^A)
    (g : Fin (A+L) → ZMod ((2^L-1)*2^A))
    (x y : ZMod ((2^L-1)*2^A))
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hmerge : 2^A • x=2^B • y) : ¬ ValidTuple g := by
  intro hg
  have hA : 0 < A := by
    by_contra hnot
    have hA0 : A=0 := by omega
    simp only [hA0,pow_zero,zero_add] at hsize
    omega
  have hM : 0 < 2^L-1 := by
    have hpow : 2 ≤ 2^L := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ L)
    omega
  letI : NeZero (2^A) := ⟨by positivity⟩
  letI : NeZero ((2^L-1)*2^A) := ⟨Nat.mul_ne_zero hM.ne' (NeZero.ne _)⟩
  let z := x-2^(B-A) • y
  have hz : addOrderOf z=2^A := addOrderOf_fork_discrepancy_of_valid hA hAB hBL g hg x y hleft hright hmerge
  have hkill : 2^A • z=0 := by simpa only [hz] using addOrderOf_nsmul_eq_zero z
  obtain ⟨t,ht,hcal⟩ := exists_bounded_coefficient_of_full_cyclic_kernel_order z y hz
  exact not_validTuple_of_calibrated_full_depth_fork hAB hBL hsize g x y z hleft hright
    (by dsimp only [z]; abel) hkill ⟨t,ht,hcal⟩ hg

/-- Full-depth fork exclusion survives arbitrary reindexing, translation,
and nonunit seeds. The merge is stated on the translated actual chains. -/
theorem not_validTuple_of_affine_full_depth_fork
    {A B L N : ℕ} (hAB : A ≤ B) (hBL : B < L) (hsize : A+L < 2^A)
    (hN : N=(2^L-1)*2^A)
    (g : Fin (A+L) → ZMod N) (E : Equiv.Perm (Fin (A+L)))
    (b x y : ZMod N)
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hmerge : 2^A • x=2^B • y) : ¬ ValidTuple g := by
  subst N
  intro hg
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  exact not_validTuple_of_full_depth_fork hAB hBL hsize _ x y hleft hright hmerge hv

/-- Away from a power dimension, the exceptional modulus has the full
dyadic-depth factorization required by the fork obstruction. -/
theorem exceptional_modulus_eq_full_depth_fork_factor
    {A L : ℕ} (hn : 3 ≤ A+L) (hA : A=Nat.log 2 (A+L)+1)
    (hnpow : 2^Nat.log 2 (A+L) ≠ A+L) :
    2*globalBound (A+L-1)=(2^L-1)*2^A := by
  have hlog : Nat.log 2 (A+L-1)=Nat.log 2 (A+L) := by
    have h := (Nat.log_eq_log_succ_iff (b := 2) (n := A+L-1)
      (by omega) (by omega)).mpr
      (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ A+L)] using hnpow)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ A+L)] using h
  have hpn : 2*2^(A+L-1)=2^(A+L) := by
    rw [← pow_succ',Nat.sub_add_cancel (by omega : 1 ≤ A+L)]
  have hpA : 2*2^Nat.log 2 (A+L)=2^A := by
    calc
      _=2^(Nat.log 2 (A+L)+1) := (pow_succ' _ _).symm
      _=2^A := congrArg (fun e ↦ 2^e) hA.symm
  rw [globalBound,hlog,Nat.mul_sub_left_distrib,hpn,hpA]
  rw [Nat.mul_sub_right_distrib,one_mul,pow_add]
  rw [Nat.mul_comm (2^A) (2^L)]

/-- Direct exceptional G3 exclusion for actual forks whose shorter arm
has the full dyadic depth. Order, calibration, and the rival are extracted;
there is no unit, independent carry, or finite verification hypothesis. -/
theorem not_validTuple_exceptional_of_full_depth_fork
    {A B L : ℕ} (hAB : A ≤ B) (hBL : B < L)
    (hA : A=Nat.log 2 (A+L)+1) (hnpow : 2^Nat.log 2 (A+L) ≠ A+L)
    (g : Fin (A+L) → ZMod (2*globalBound (A+L-1)))
    (E : Equiv.Perm (Fin (A+L))) (b x y : ZMod (2*globalBound (A+L-1)))
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hmerge : 2^A • x=2^B • y) : ¬ ValidTuple g := by
  have hn : 3 ≤ A+L := by omega
  have hsize : A+L < 2^A := by
    have h := Nat.lt_pow_succ_log_self (by omega : 1 < (2 : ℕ)) (A+L)
    simpa only [Nat.succ_eq_add_one,← hA] using h
  exact not_validTuple_of_affine_full_depth_fork hAB hBL hsize
    (exceptional_modulus_eq_full_depth_fork_factor hn hA hnpow) g E b x y hleft hright hmerge

end MinModulus
