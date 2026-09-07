import MinModulus.FullDepthFork

/-!
# Complete exceptional-lift obstruction for actual merging forks

For shallower arms, failure of the first calibrated weight pair forces
at least three common-tail coordinates. That pays for four top coins in
the complementary pair; the other case saves a coin below the all-ones
endpoint. Both weight identities are additive, and all coin budgets are
proved uniformly. No binary pattern search is a proof premise.

Odd calibration is extracted from actual subbinary cyclic validity:
an even coefficient would force every coordinate into the even subgroup,
whose subset-cube lower bound contradicts subbinary size. All seed
multipliers, including nonunits, are allowed.

The final G3 theorem combines short-arm prefix bounds, full-depth forks,
shallower-arm rivals, and exact-order exclusion of excessive depth. It
requires only actual two-chain data and the merge, not a depth, unit,
calibration, or coin-budget hypothesis. Extracting this fork from arbitrary
acyclic one-escape data remains open; the three global gates remain open.
-/

namespace MinModulus
open Finset

/-- Below c top coins, greedy binary construction costs at most w+c-1
coins on indices 0,...,w. This is a constructive upper bound. -/
theorem exists_binary_rep_below_top_multiple
    {w c X : ℕ} (hc : 0 < c) (hX : X < c*2^w) :
    ∃ u, Supp (w+1) u ∧ val (w+1) u=X ∧ dsum (w+1) u ≤ w+c-1 := by
  have hp : 0 < 2^w := by positivity
  have hq : X/2^w < c := (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [Nat.mul_comm] using hX)
  obtain ⟨u,hs,hu,hdu⟩ := exists_rep_le w (X%2^w) (Nat.mod_lt _ hp)
  obtain ⟨hv,hvalue,hcard⟩ := update_top w (X/2^w) u hs
  refine ⟨_,hv,?_,?_⟩
  · rw [hvalue,hu]
    simpa only [Nat.mul_comm] using Nat.mod_add_div X (2^w)
  · rw [hcard]
    omega

/-- Missing the all-ones endpoint saves one more binary coin. -/
theorem exists_binary_rep_below_top_multiple_sub_one
    {w c X : ℕ} (hw : 0 < w) (hc : 0 < c) (hX : X < c*2^w-1) :
    ∃ u, Supp (w+1) u ∧ val (w+1) u=X ∧ dsum (w+1) u ≤ w+c-2 := by
  have hp : 0 < 2^w := by positivity
  have hq : X/2^w < c := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  by_cases hsmall : X/2^w+1 < c
  · obtain ⟨u,hs,hu,hdu⟩ := exists_rep_le w (X%2^w) (Nat.mod_lt _ hp)
    obtain ⟨hv,hvalue,hcard⟩ := update_top w (X/2^w) u hs
    refine ⟨_,hv,?_,?_⟩
    · rw [hvalue,hu]
      simpa only [Nat.mul_comm] using Nat.mod_add_div X (2^w)
    · rw [hcard]
      omega
  · have hqe : X/2^w+1=c := by omega
    have hrem : X%2^w < 2^w-1 := by
      have heq := Nat.mod_add_div X (2^w)
      have hprod : c*2^w=2^w*(X/2^w)+2^w := by rw [← hqe]; ring
      omega
    obtain ⟨u,hs,hu,hdu⟩ := exists_rep_lt w (X%2^w) hrem
    obtain ⟨hv,hvalue,hcard⟩ := update_top w (X/2^w) u hs
    refine ⟨_,hv,?_,?_⟩
    · rw [hvalue,hu]
      simpa only [Nat.mul_comm] using Nat.mod_add_div X (2^w)
    · rw [hcard]
      omega

/-- If the first inverse-based weight pair cannot reach full length,
the common tail necessarily has at least three coordinates. -/
theorem three_le_fork_tail_of_first_weights_too_small
    {A B L r t : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hAr : A < r)
    (ht : 0 < t) (htd : t < 2^A)
    (hsmall : (t-1)+(2^(B-A)*(2^A-t)+2^(r-A)-1) < A+L) : B+3 ≤ L := by
  have hd := two_mul_add_two_le_two_pow_of_three_le A hA
  have hv : B-A+1 ≤ 2^(B-A) := by have h := Nat.lt_two_pow_self (n := B-A); omega
  have hh : 2 ≤ 2^(r-A) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ r-A)
  have hq : 0 < 2^A-t := by omega
  have hqt : 2^A-t+t=2^A := by omega
  have hvpos : 0 < 2^(B-A) := by positivity
  have hvsub : 2^(B-A)-1+1=2^(B-A) := by omega
  have hqsub : (2^A-t)-1+1=2^A-t := by omega
  have hprod : 2^(B-A)+(2^A-t) ≤ 2^(B-A)*(2^A-t)+1 := by
    nlinarith [Nat.zero_le ((2^(B-A)-1)*((2^A-t)-1))]
  omega

/-- An odd factor between two powers of two is necessarily one. -/
theorem eq_exponents_and_one_of_two_pow_mul_odd
    {a b t : ℕ} (ht : Odd t) (heq : 2^a*t=2^b) : a=b ∧ t=1 := by
  induction a generalizing b with
  | zero =>
    simp only [pow_zero,one_mul] at heq
    cases b with
    | zero => simp only [pow_zero] at heq; exact ⟨rfl,heq⟩
    | succ b =>
      obtain ⟨k,hk⟩ := ht
      rw [pow_succ'] at heq
      omega
  | succ a ih =>
    cases b with
    | zero =>
      rw [pow_zero,pow_succ',Nat.mul_assoc] at heq
      omega
    | succ b =>
      simp only [pow_succ',Nat.mul_assoc] at heq
      have heq' : 2^a*t=2^b := by omega
      obtain ⟨hab,ht⟩ := ih heq'
      exact ⟨by omega,ht⟩

/-- At the exceptional power gap, equality of the two dyadic products
would make the FIRST weight pair large enough. Its failure therefore
rules out the only borderline complementary coin count. -/
theorem shallow_fork_products_ne_of_first_weights_too_small
    {A B L r t : ℕ} (hAB : A ≤ B) (hAr : A < r) (ht : Odd t)
    (hn : A+L < 2^r)
    (hsmall : (t-1)+(2^(B-A)*(2^A-t)+2^(r-A)-1) < A+L) :
    2^(B-A)*t ≠ 2^(r-A) := by
  intro heq
  obtain ⟨hab,htone⟩ := eq_exponents_and_one_of_two_pow_mul_odd ht heq
  have hBr : B=r := by omega
  subst t
  have hd : 0 < 2^A := by positivity
  have hprod : 2^(B-A)*(2^A-1)+2^(r-A)=2^r := by
    rw [hBr, Nat.mul_sub_left_distrib,mul_one]
    have hp : 2^(r-A)*2^A=2^r := by rw [← pow_add,Nat.sub_add_cancel (by omega : A ≤ r)]
    have hle : 2^(r-A) ≤ 2^(r-A)*2^A := Nat.le_mul_of_pos_right _ hd
    omega
  norm_num only [Nat.sub_self,zero_add] at hsmall
  rw [hprod] at hsmall
  omega

/-- Uniform shallow-arm arithmetic: if the first pair has insufficient
total weight, the complementary pair has enough weight and admits a
binary representation within the exact original coin budget. -/
theorem exists_complementary_shallow_fork_coin_budget
    {A B L r t : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBL : B < L)
    (hAr : A < r) (hrn : r < A+L) (hn : A+L < 2^r)
    (ht : Odd t) (htd : t < 2^A)
    (hsmall : (t-1)+(2^(B-A)*(2^A-t)+2^(r-A)-1) < A+L) :
    ∃ u v : ℕ → ℕ,
      val A u=2^A-t-1 ∧
      val L v=2^(L+1)+2^(B-A)*t-2^(r-A)-1 ∧
      dsum A u+dsum L v ≤ A+L ∧
      A+L ≤ (2^A-t-1)+(2^(L+1)+2^(B-A)*t-2^(r-A)-1) := by
  have htpos := ht.pos
  have hL : 2 ≤ L := by omega
  have htop : 0 < 2^(L-1) := by positivity
  have hLpow : 2^(L+1)=4*2^(L-1) := by
    have hLform : L+1=(L-1)+2 := by omega
    rw [hLform,pow_add]
    norm_num
    omega
  have hhalf : 2^(r-A) ≤ 2^(L-1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2L : 2^L=2*2^(L-1) := by
    have hLform : L=(L-1)+1 := by omega
    conv_lhs => rw [hLform,pow_succ']
  have hnL : A+L < 2^L := by
    have h := two_mul_le_two_pow L
    omega
  have hhigh : A+L ≤ (2^A-t-1)+(2^(L+1)+2^(B-A)*t-2^(r-A)-1) := by
    omega
  have hX : 2^A-t-1 < 2^A-1 := by omega
  obtain ⟨u,_,hu,hdu⟩ := exists_rep_lt A (2^A-t-1) hX
  have hne := shallow_fork_products_ne_of_first_weights_too_small hAB hAr ht hn hsmall
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hY : 2^(L+1)+2^(B-A)*t-2^(r-A)-1 < 4*2^(L-1)-1 := by omega
    obtain ⟨v,_,hv,hdv⟩ := exists_binary_rep_below_top_multiple_sub_one
      (by omega : 0 < L-1) (by omega : 0 < (4 : ℕ)) hY
    have hLform : L-1+1=L := by omega
    rw [hLform] at hv hdv
    exact ⟨u,v,hu,hv,by omega,hhigh⟩
  · have htail := three_le_fork_tail_of_first_weights_too_small hA hAB hAr htpos htd hsmall
    let T := 2^(B-A)*t-2^(r-A)-1
    have hvpos : 0 < 2^(B-A) := by positivity
    have hvt : 2^(B-A)*t < 2^B := by
      have hp : 2^(B-A)*2^A=2^B := by rw [← pow_add,Nat.sub_add_cancel hAB]
      rw [← hp]
      exact Nat.mul_lt_mul_of_pos_left htd hvpos
    have hT : T < 2^B := by
      dsimp only [T]
      exact lt_of_le_of_lt ((Nat.sub_le _ _).trans (Nat.sub_le _ _)) hvt
    obtain ⟨v,hvs,hv,hdv⟩ := exists_rep_le B T hT
    have hpad : Supp (L-1) v := supp_mono (by omega) hvs
    obtain ⟨_,hvalue,hcard⟩ := update_top (L-1) 4 v hpad
    have hLform : L-1+1=L := by omega
    rw [hLform,val_pad (by omega : B ≤ L-1) hvs] at hvalue
    rw [hLform,dsum_pad (by omega : B ≤ L-1) hvs] at hcard
    refine ⟨u,Function.update v (L-1) 4,hu,?_,?_,hhigh⟩
    · rw [hvalue,hv]
      dsimp only [T]
      omega
    · rw [hcard]
      omega

/-- The two inverse-calibrated weight choices BOTH have the actual
distinguished sum. This identity is additive and does not require a unit
seed, cyclicity, validity, or an odd calibration coefficient. -/
theorem calibrated_fork_two_weight_sum_identities
    {d v D H P t : ℕ} (hDH : D+H=P) (hH : 0 < H)
    (ht : 0 < t) (htd : t < d)
    {G : Type*} [AddCommGroup G] (x y z : G)
    (hx : x=v • y+z) (hkill : d • z=0) (hcal : t • z=D • y) :
    ((t-1) • x+(v*(d-t)+H-1) • y=(d-1) • x+(P-1) • y) ∧
    ((d-t-1) • x+(2*P+v*t-H-1) • y=(d-1) • x+(P-1) • y) := by
  have hd : 0 < d := by omega
  have hP : 0 < P := by omega
  have hprod1 : (t-1)*v+v*(d-t)=(d-1)*v := by
    calc
      _=((t-1)+(d-t))*v := by ring
      _=_ := by congr 1; omega
  have hprod2 : (d-t-1)*v+v*t=(d-1)*v := by
    calc
      _=((d-t-1)+t)*v := by ring
      _=_ := by congr 1; omega
  have hc1 : (t-1)*v+(v*(d-t)+H-1)+D=(d-1)*v+(P-1) := by omega
  have hc2 : (d-t-1)*v+(2*P+v*t-H-1)=(d-1)*v+(P-1)+D := by omega
  have hdz : (d-1) • z+z=0 := by
    rw [← succ_nsmul,Nat.sub_add_cancel (by omega : 1 ≤ d),hkill]
  constructor
  · have htz : (t-1) • z+z=D • y := by
      rw [← succ_nsmul,Nat.sub_add_cancel (by omega : 1 ≤ t),hcal]
    apply add_right_cancel (b := z)
    rw [hx,smul_add,smul_add,smul_smul,smul_smul]
    calc
      _=((t-1)*v) • y+(v*(d-t)+H-1) • y+((t-1) • z+z) := by abel
      _=((d-1)*v+(P-1)) • y := by rw [htz,← add_nsmul,← add_nsmul,hc1]
      _=((d-1)*v) • y+(P-1) • y := by rw [add_nsmul]
      _=((d-1)*v) • y+((d-1) • z+z)+(P-1) • y := by rw [hdz,add_zero]
      _=_ := by abel
  · have htz : ((d-t-1) • z+z)+t • z=0 := by
      rw [← succ_nsmul,← add_nsmul,show d-t-1+1+t=d by omega,hkill]
    apply add_right_cancel (b := z+t • z)
    rw [hx,smul_add,smul_add,smul_smul,smul_smul]
    calc
      _=((d-t-1)*v) • y+(2*P+v*t-H-1) • y+(((d-t-1) • z+z)+t • z) := by abel
      _=((d-1)*v+(P-1)+D) • y := by rw [htz,add_zero,← add_nsmul,hc2]
      _=((d-1)*v) • y+(P-1) • y+D • y := by rw [add_nsmul,add_nsmul]
      _=((d-1)*v) • y+((d-1) • z+z)+(P-1) • y+t • z := by rw [hdz,add_zero,hcal]
      _=_ := by abel

/-- Uniform rival extraction for every shallow arm of length at least
three with an odd actual calibration coefficient. No inverse search,
binary pattern, or coin-budget premise is left to the caller. -/
theorem not_validTuple_of_odd_calibrated_shallow_fork
    {A B L r : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBL : B < L)
    (hAr : A < r) (hrn : r < A+L) (hn : A+L < 2^r)
    {G : Type*} [AddCommGroup G]
    (g : Fin (A+L) → G) (x y z : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hx : x=2^(B-A) • y+z) (hkill : 2^A • z=0)
    (hcal : ∃ t : ℕ, t<2^A ∧ Odd t ∧ t • z=(2^L-2^(r-A)) • y) :
    ¬ ValidTuple g := by
  obtain ⟨t,htd,ht,hcal⟩ := hcal
  have htpos := ht.pos
  have hL : 2 ≤ L := by omega
  have hh : 2^(r-A) ≤ 2^(L-1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hhL : 2^(r-A) ≤ 2^L := Nat.pow_le_pow_right (by omega) (by omega)
  have hpL : 2^L=2*2^(L-1) := by
    have hform : L=(L-1)+1 := by omega
    conv_lhs => rw [hform,pow_succ']
  have hidentities := calibrated_fork_two_weight_sum_identities
    (Nat.sub_add_cancel hhL) (by positivity : 0 < 2^(r-A)) htpos htd x y z hx hkill hcal
  by_cases hhigh : A+L ≤ (t-1)+(2^(B-A)*(2^A-t)+2^(r-A)-1)
  · have hX : t-1 < 2^A := by omega
    have hvpos : 0 < 2^(B-A) := by positivity
    have hprod : 2^(B-A)*(2^A-t) < 2^B := by
      have hp : 2^(B-A)*2^A=2^B := by rw [← pow_add,Nat.sub_add_cancel hAB]
      rw [← hp]
      exact Nat.mul_lt_mul_of_pos_left (by omega) hvpos
    have hBpow : 2^B ≤ 2^(L-1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hY : 2^(B-A)*(2^A-t)+2^(r-A)-1 < 2^L := by omega
    exact not_validTuple_of_two_chain_small_integer_weights g x y hleft hright hX hY hhigh
      (by omega) hidentities.1
  · have hsmall : (t-1)+(2^(B-A)*(2^A-t)+2^(r-A)-1) < A+L := by omega
    obtain ⟨u,v,hu,hv,hcard,hweight⟩ := exists_complementary_shallow_fork_coin_budget
      hA hAB hBL hAr hrn hn ht htd hsmall
    apply not_validTuple_of_two_chain_integer_weights g x y hleft hright u v hu hv hcard hweight
      (by omega)
    simpa only [pow_succ',Nat.mul_comm] using hidentities.2

/-- In a finite cyclic group, annihilation by one factor forces the
natural representative to be divisible by the complementary factor. -/
theorem factor_dvd_val_of_nsmul_eq_zero
    {N d M : ℕ} [NeZero N] (hN : N=d*M) (x : ZMod N)
    (hx : M • x=0) : d ∣ x.val := by
  have hNpos := Nat.pos_of_ne_zero (NeZero.ne N)
  have hM : 0 < M := by nlinarith
  have hdvd : N ∣ M*x.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_mul,ZMod.natCast_zmod_val,nsmul_eq_mul] using hx
  have hdvd' : M*d ∣ M*x.val :=
    (show M*d ∣ N by rw [hN,Nat.mul_comm]).trans hdvd
  exact Nat.dvd_of_mul_dvd_mul_left hM hdvd'

/-- An entirely even actual tuple cannot be subbinary: halving all its
coordinates and applying the subset-cube bound already costs 2^n. -/
theorem not_all_even_values_of_valid_subbinary_tuple
    {n N : ℕ} [NeZero N] (hn : 0 < n) (hN : Even N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < 2^n) :
    ¬ (∀ i, Even (g i).val) := by
  intro heven
  obtain ⟨M,hM⟩ := hN
  have hNM : N=2*M := by omega
  clear hM
  subst N
  have hMpos : 0 < M := by have h := Nat.pos_of_ne_zero (NeZero.ne (2*M)); omega
  letI : NeZero M := ⟨hMpos.ne'⟩
  have hb := two_pow_pred_le_half_of_validTuple_even_values g hg heven
  have hpow : 2^n=2*2^(n-1) := by
    have hnform : n=n-1+1 := by omega
    conv_lhs => rw [hnform,pow_succ']
  omega

/-- At an even cyclic kernel index, a valid subbinary two-chain tuple
forces its ACTUAL calibration coefficient to be odd. An even coefficient
annihilates the long seed at half the modulus, putting the entire tuple
in the even coset and contradicting the subset-cube bound. -/
theorem odd_fork_calibration_of_valid_subbinary_tuple
    {A L D v t : ℕ} (hA : 0 < A) (hD : Even D)
    [NeZero (D*2^A)] (hsmall : D*2^A < 2^(A+L))
    (g : Fin (A+L) → ZMod (D*2^A)) (hg : ValidTuple g)
    (x y z : ZMod (D*2^A))
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hx : x=v • y+z) (hkill : 2^A • z=0) (hcal : t • z=D • y) : Odd t := by
  rcases Nat.even_or_odd t with ht | ht
  · obtain ⟨s,hs⟩ := ht
    have htform : t=2*s := by omega
    have hApow : 2^A=2*2^(A-1) := by
      have hAform : A=A-1+1 := by omega
      conv_lhs => rw [hAform,pow_succ']
    have hykill : (2^(A-1)*D) • y=0 := by
      have heq := congrArg (fun w ↦ 2^(A-1) • w) hcal
      rw [smul_smul,smul_smul] at heq
      have hfactor : 2^(A-1)*t=s*2^A := by rw [htform,hApow]; ring
      rw [hfactor,mul_smul,hkill,smul_zero] at heq
      exact heq.symm
    have hNhalf : D*2^A=2*(2^(A-1)*D) := by rw [hApow]; ring
    have hyEven : Even y.val := even_iff_two_dvd.mpr (factor_dvd_val_of_nsmul_eq_zero hNhalf y hykill)
    have hzEven : Even z.val := even_iff_two_dvd.mpr
      (hD.two_dvd.trans (factor_dvd_val_of_nsmul_eq_zero rfl z hkill))
    have hN2 : 2 ∣ D*2^A := hD.two_dvd.trans (dvd_mul_right D (2^A))
    let φ := ZMod.castHom hN2 (ZMod 2)
    have hy0 : φ y=0 := by
      change ZMod.castHom hN2 (ZMod 2) y=0
      rw [ZMod.castHom_apply,← ZMod.natCast_val,ZMod.natCast_eq_zero_iff]
      exact hyEven.two_dvd
    have hz0 : φ z=0 := by
      change ZMod.castHom hN2 (ZMod 2) z=0
      rw [ZMod.castHom_apply,← ZMod.natCast_val,ZMod.natCast_eq_zero_iff]
      exact hzEven.two_dvd
    have hx0 : φ x=0 := by rw [hx,map_add,map_nsmul,hy0,hz0,smul_zero,add_zero]
    have hparity : ∀ i, φ (g i)=0 := by
      intro i
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · rw [hleft,map_nsmul,hx0,smul_zero]
      · rw [hright,map_nsmul,hy0,smul_zero]
    have heven : ∀ i, Even (g i).val := by
      intro i
      have hi := hparity i
      change ZMod.castHom hN2 (ZMod 2) (g i)=0 at hi
      rw [ZMod.castHom_apply,← ZMod.natCast_val,ZMod.natCast_eq_zero_iff] at hi
      exact even_iff_two_dvd.mpr hi
    exact False.elim (not_all_even_values_of_valid_subbinary_tuple (by omega)
      (even_iff_two_dvd.mpr hN2) g hg hsmall heven)
  · exact ht

/-- Every shallow fork with at least three short-arm coordinates is
excluded at a forbidden power gap. Validity extracts both the exact
kernel order and the ODD calibration coefficient; neither is a premise. -/
theorem not_validTuple_of_shallow_fork_power_gap
    {A B L r : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBL : B < L)
    (hAr : A < r) (hrn : r < A+L) (hn : A+L < 2^r)
    (g : Fin (A+L) → ZMod ((2^L-2^(r-A))*2^A))
    (x y : ZMod ((2^L-2^(r-A))*2^A))
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hmerge : 2^A • x=2^B • y) : ¬ ValidTuple g := by
  intro hg
  have hDpos : 0 < 2^L-2^(r-A) := by
    have hp := Nat.pow_lt_pow_right (by omega : 1 < (2 : ℕ)) (by omega : r-A < L)
    omega
  have hDsmall : 2^L-2^(r-A) < 2^L := by
    have hp : 0 < 2^(r-A) := by positivity
    omega
  have hDEven : Even (2^L-2^(r-A)) := by
    have hLform : L=L-1+1 := by omega
    have hrform : r-A=(r-A-1)+1 := by omega
    have hpL : 2^L=2*2^(L-1) := by conv_lhs => rw [hLform,pow_succ']
    have hpR : 2^(r-A)=2*2^(r-A-1) := by conv_lhs => rw [hrform,pow_succ']
    refine ⟨2^(L-1)-2^(r-A-1),?_⟩
    rw [hpL,hpR,← Nat.mul_sub_left_distrib]
    omega
  have hsubbinary : (2^L-2^(r-A))*2^A < 2^(A+L) := by
    calc
      _<2^L*2^A := Nat.mul_lt_mul_of_pos_right hDsmall (by positivity)
      _=2^(A+L) := by rw [← pow_add,Nat.add_comm]
  letI : NeZero (2^A) := ⟨by positivity⟩
  letI : NeZero ((2^L-2^(r-A))*2^A) := ⟨Nat.mul_ne_zero hDpos.ne' (NeZero.ne _)⟩
  let z := x-2^(B-A) • y
  have hz : addOrderOf z=2^A := addOrderOf_fork_discrepancy_of_valid (by omega) hAB hBL g hg x y hleft hright hmerge
  have hkill : 2^A • z=0 := by simpa only [hz] using addOrderOf_nsmul_eq_zero z
  obtain ⟨t,ht,hcal⟩ := exists_bounded_coefficient_of_full_cyclic_kernel_order z y hz
  have hx : x=2^(B-A) • y+z := by dsimp only [z]; abel
  have htodd := odd_fork_calibration_of_valid_subbinary_tuple (by omega : 0 < A) hDEven hsubbinary
    g hg x y z hleft hright hx hkill hcal
  exact not_validTuple_of_odd_calibrated_shallow_fork hA hAB hBL hAr hrn hn g x y z
    hleft hright hx hkill ⟨t,ht,htodd,hcal⟩ hg

/-- Affine reindexing of the general shallow-fork power-gap obstruction.
All actual seeds are arbitrary, including nonunits. -/
theorem not_validTuple_of_affine_shallow_fork_power_gap
    {A B L r N : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBL : B < L)
    (hAr : A < r) (hrn : r < A+L) (hn : A+L < 2^r)
    (hN : N=(2^L-2^(r-A))*2^A)
    (g : Fin (A+L) → ZMod N) (E : Equiv.Perm (Fin (A+L))) (b x y : ZMod N)
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hmerge : 2^A • x=2^B • y) : ¬ ValidTuple g := by
  subst N
  intro hg
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  exact not_validTuple_of_shallow_fork_power_gap hA hAB hBL hAr hrn hn _ x y hleft hright hmerge hv

/-- Factor the exact exceptional modulus at ANY proposed shorter arm
length not exceeding the dyadic depth. -/
theorem exceptional_modulus_eq_fork_power_gap
    {A L r : ℕ} (hn : 3 ≤ A+L) (hAr : A ≤ r)
    (hr : r=Nat.log 2 (A+L)+1) (hnpow : 2^Nat.log 2 (A+L) ≠ A+L) :
    2*globalBound (A+L-1)=(2^L-2^(r-A))*2^A := by
  have hlog : Nat.log 2 (A+L-1)=Nat.log 2 (A+L) := by
    have h := (Nat.log_eq_log_succ_iff (b := 2) (n := A+L-1)
      (by omega) (by omega)).mpr
      (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ A+L)] using hnpow)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ A+L)] using h
  have hpn : 2*2^(A+L-1)=2^(A+L) := by
    rw [← pow_succ',Nat.sub_add_cancel (by omega : 1 ≤ A+L)]
  have hpr : 2*2^Nat.log 2 (A+L)=2^r := by
    calc
      _=2^(Nat.log 2 (A+L)+1) := (pow_succ' _ _).symm
      _=2^r := congrArg (fun e ↦ 2^e) hr.symm
  rw [globalBound,hlog,Nat.mul_sub_left_distrib,hpn,hpr,Nat.mul_sub_right_distrib]
  have hp : 2^(r-A)*2^A=2^r := by rw [← pow_add,Nat.sub_add_cancel hAr]
  rw [hp,← pow_add,Nat.add_comm L A]

/-- Direct G3 exclusion for every actual shallower fork arm of length
at least three. Oddness, units, inverse choices, and all coin budgets
are extracted or eliminated internally. -/
theorem not_validTuple_exceptional_of_shallow_fork
    {A B L : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBL : B < L)
    (hAr : A < Nat.log 2 (A+L)+1) (hnpow : 2^Nat.log 2 (A+L) ≠ A+L)
    (g : Fin (A+L) → ZMod (2*globalBound (A+L-1)))
    (E : Equiv.Perm (Fin (A+L))) (b x y : ZMod (2*globalBound (A+L-1)))
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hmerge : 2^A • x=2^B • y) : ¬ ValidTuple g := by
  have hn : 3 ≤ A+L := by omega
  have hrn : Nat.log 2 (A+L)+1 < A+L := by
    have hp := succ_le_two_pow_pred (A+L) hn
    have h := Nat.log_lt_of_lt_pow (by omega : A+L ≠ 0) (by omega : A+L < 2^(A+L-1))
    omega
  have hupper : A+L < 2^(Nat.log 2 (A+L)+1) := by
    simpa only [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by omega : 1 < (2 : ℕ)) (A+L)
  exact not_validTuple_of_affine_shallow_fork_power_gap hA hAB hBL hAr hrn hupper
    (exceptional_modulus_eq_fork_power_gap hn (by omega) rfl hnpow) g E b x y hleft hright hmerge

/-- Exact dyadic order cannot exceed the valuation of an odd-factor
cyclic modulus. This extracts the depth range for actual fork data. -/
theorem dyadic_order_exponent_le_of_odd_factor
    {N A r q : ℕ} [NeZero N] (hN : N=2^r*q) (hq : Odd q)
    (z : ZMod N) (hz : addOrderOf z=2^A) : A ≤ r := by
  have hdvd : 2^A ∣ N := by
    rw [← hz]
    simpa using (addOrderOf_dvd_card (x := z))
  by_contra hnot
  have hp : 2^(r+1) ∣ 2^A := pow_dvd_pow 2 (by omega)
  have hdiv : 2^r*2 ∣ 2^r*q := by
    simpa only [hN,pow_succ] using hp.trans hdvd
  have htwo : 2 ∣ q := Nat.dvd_of_mul_dvd_mul_left (by positivity : 0 < 2^r) hdiv
  obtain ⟨u,hu⟩ := htwo
  obtain ⟨v,hv⟩ := hq
  omega

/-- A long actual chain with one or two extra coordinates already has
the full global bound, with arbitrary affine transport and multiplier. -/
theorem global_lower_bound_of_valid_chain_with_at_most_two_extras
    {A L N : ℕ} [NeZero N] (hA : 0 < A) (hA2 : A ≤ 2) (hL : A+1 ≤ L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (A+L))) (b y : ZMod N)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y) :
    globalBound (A+L) ≤ N := by
  let f : Fin (L+A) → ZMod N := fun i ↦ g (E (finAddFlip i))+b
  have hf : ValidTuple f := by
    simpa only [f,sub_neg_eq_add,Equiv.trans_apply] using
      validTuple_sub_const (fun i ↦ g ((finAddFlip.trans E) i))
        (validTuple_embedding (finAddFlip.trans E).toEmbedding g hg) (-b)
  have hpow (i : ℕ) : 2^i • y=y*(a i : ZMod N)+y := by
    have ha : a i+1=2^i := by
      unfold a
      have hp : 0 < 2^i := by positivity
      omega
    rw [nsmul_eq_mul,← ha,Nat.cast_add,Nat.cast_one]
    ring
  have hprefix (i : Fin L) : f (Fin.castAdd A i)=y*(a i.val : ZMod N)+y := by
    simpa only [f,finAddFlip_apply_castAdd,hpow] using hright i
  rcases (show A=1 ∨ A=2 by omega) with rfl | rfl
  · have hb := global_lower_bound_of_valid_scaled_fixed_prefix (by omega : 2 ≤ L)
      f hf (Equiv.refl _) y y (by intro i; exact hprefix i)
    simpa only [Nat.add_comm] using hb
  · have hb := global_lower_bound_of_valid_scaled_fixed_short_prefix (by omega : 3 ≤ L)
      f hf (Equiv.refl _) y y (by intro i; exact hprefix i)
    simpa only [Nat.add_comm] using hb

/-- COMPLETE G3 exclusion for every actual two-chain merging fork.
Short arms use the proved prefix bounds; validity extracts the dyadic
depth range; full-depth and shallower arms use their constructed rivals.
No depth, unit, calibration, or coin-pattern premise is retained. -/
theorem not_validTuple_exceptional_of_actual_fork
    {A B L : ℕ} (hA : 0 < A) (hAB : A ≤ B) (hBL : B < L)
    (hnpow : 2^Nat.log 2 (A+L) ≠ A+L)
    (g : Fin (A+L) → ZMod (2*globalBound (A+L-1)))
    (E : Equiv.Perm (Fin (A+L))) (b x y : ZMod (2*globalBound (A+L-1)))
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hmerge : 2^A • x=2^B • y) : ¬ ValidTuple g := by
  intro hg
  have hn : 3 ≤ A+L := by omega
  have hB : 2 ≤ globalBound (A+L-1) := (nmin_eq (by omega : 2 ≤ A+L-1)).1.1
  letI : NeZero (2*globalBound (A+L-1)) := ⟨by omega⟩
  by_cases hAsmall : A ≤ 2
  · have hb := global_lower_bound_of_valid_chain_with_at_most_two_extras hA hAsmall (by omega)
      g hg E b y hright
    have hnpow' : 2^Nat.log 2 ((A+L-1)+1) ≠ (A+L-1)+1 := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ A+L)] using hnpow
    have hgap : 2*globalBound (A+L-1) < globalBound (A+L) := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ A+L)] using
        two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ A+L-1) hnpow'
    omega
  · let r := Nat.log 2 (A+L)+1
    have hrn : r < A+L := by
      have hp := succ_le_two_pow_pred (A+L) hn
      have h := Nat.log_lt_of_lt_pow (by omega : A+L ≠ 0) (by omega : A+L < 2^(A+L-1))
      dsimp only [r]
      omega
    have hnform : r+(A+L-r)=A+L := by omega
    have hfactor : 2*globalBound (A+L-1)=(2^(A+L-r)-1)*2^r := by
      have h := exceptional_modulus_eq_full_depth_fork_factor (A := r) (L := A+L-r)
        (by omega) (by rw [hnform])
        (by simpa only [hnform] using hnpow)
      simpa only [hnform] using h
    have hq : Odd (2^(A+L-r)-1) := by
      have hp : 2^(A+L-r)=2*2^(A+L-r-1) := by
        have he : A+L-r=(A+L-r-1)+1 := by omega
        conv_lhs => rw [he,pow_succ']
      have hp0 : 0 < 2^(A+L-r-1) := by positivity
      exact ⟨2^(A+L-r-1)-1,by omega⟩
    have hv : ValidTuple (fun i ↦ g (E i)+b) := by
      simpa only [sub_neg_eq_add] using
        validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
    have hz := addOrderOf_fork_discrepancy_of_valid hA hAB hBL _ hv x y hleft hright hmerge
    have hAr : A ≤ r := dyadic_order_exponent_le_of_odd_factor
      (by rw [hfactor,Nat.mul_comm]) hq _ hz
    rcases lt_or_eq_of_le hAr with hlt | heq
    · exact not_validTuple_exceptional_of_shallow_fork (by omega) hAB hBL hlt hnpow g E b x y hleft hright hmerge hg
    · exact not_validTuple_exceptional_of_full_depth_fork hAB hBL heq hnpow g E b x y hleft hright hmerge hg

end MinModulus
