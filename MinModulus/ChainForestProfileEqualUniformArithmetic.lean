import MinModulus.ChainForestProfileEqualFactorFour

/-! Uniform equal-companion rivals at every nonmaximal dyadic index.
Three rational blocks cover nonintegral steps; symmetric companions and
an odd dyadic boundary cover integral steps. No finite phase census is used. -/

namespace MinModulus

/-- Beyond the already closed small companion lengths, the actual
half-profile cost leaves sixteen times the companion length available. -/
theorem sixteen_equal_length_le_of_half_cost {a n : ℕ}
    (ha : 6 ≤ a) (hcost : 2^(a+1) ≤ n+1) : 16*a ≤ n := by
  have hp : ∀ b, 6 ≤ b → 16*b+1 ≤ 2^(b+1) := by
    intro b hb
    induction b, hb using Nat.le_induction with
    | base => norm_num
    | succ b hb ih =>
      rw [pow_succ]
      nlinarith
  have hh := hp a ha
  omega

/-- A proper fractional remainder with denominator below one binary
block can never produce the all-ones block. -/
theorem rational_binary_block_lt_ones {S r B : ℕ}
    (hS : 0 < S) (hSB : S < 2^B) (hr : r < S) :
    r*2^B/S < 2^B-1 := by
  apply (Nat.div_lt_iff_lt_mul hS).mpr
  have hp : 1 ≤ 2^B := Nat.one_le_two_pow
  have hm := Nat.mul_le_mul_right (2^B) (show r+1 ≤ S by omega)
  have hp' : 2^B-1+1=2^B := Nat.sub_add_cancel hp
  have he := congrArg (fun t : ℕ ↦ t*S) hp'
  nlinarith only [hm,he,hSB]

/-- Quotient and remainder split multiplication by an arbitrary block. -/
theorem mul_div_block_decomposition (x P : ℕ) {S : ℕ} (hS : 0 < S) :
    x*P/S=(x/S)*P+((x%S)*P)/S := by
  have hh := congrArg (fun t : ℕ ↦ t*P) (Nat.mod_add_div x S)
  have he : x*P=(x%S)*P+S*((x/S)*P) := by nlinarith only [hh]
  rw [he,Nat.add_mul_div_left _ _ hS]
  omega

/-- A first rational prefix below twice the denominator pays for its
integer part and saves a coin in its fractional block. -/
theorem rational_first_binary_block_coin_bound {S R B : ℕ}
    (hS : 0 < S) (hSB : S < 2^B) (hR : R < 2*S) (hB : 1 ≤ B) :
    gmin (B-1) (R*2^B/S) ≤ B+1 := by
  have hd := rational_binary_block_lt_ones hS hSB (Nat.mod_lt R hS)
  have hc : gmin (B-1) ((R%S)*2^B/S) ≤ B-1 :=
    gmin_le_of_lt_binary_ones (by simpa only [Nat.sub_add_cancel hB] using hd)
  have hq : R/S < 2 := (Nat.div_lt_iff_lt_mul hS).mpr (by omega)
  let d := (R%S)*2^B/S
  change gmin (B-1) d ≤ B-1 at hc
  rw [mul_div_block_decomposition R (2^B) hS]
  change gmin (B-1) ((R/S)*2^B+d) ≤ B+1
  have hqnonneg : 0 ≤ R/S := Nat.zero_le _
  by_cases hz : R/S=0
  · rw [hz,zero_mul,zero_add]
    omega
  · have ho : R/S=1 := by omega
    have hp : 2^B=2^(B-1)+2^(B-1) := by rw [← two_mul,← pow_succ']; congr 1; omega
    rw [ho,one_mul,Nat.add_comm,hp,← Nat.add_assoc,gmin_add_pow,gmin_add_pow]
    omega

/-- Three rational fractional blocks save enough coins for every
bounded equal-companion index step, uniformly in the denominator. -/
theorem rational_three_binary_blocks_coin_bound {S R B : ℕ}
    (hS : 0 < S) (hSB : S < 2^B) (hR : R < 2*S) (hB : 1 ≤ B) :
    gmin (3*B-1) (R*2^(3*B)/S) ≤ 3*B-1 := by
  let P := 2^B
  let A1 := R*P/S
  let A2 := R*P*P/S
  let A3 := R*P*P*P/S
  let d2 := ((R*P)%S)*P/S
  let d3 := ((R*P*P)%S)*P/S
  have h2 : A2=A1*P+d2 := mul_div_block_decomposition (R*P) P hS
  have h3 : A3=A2*P+d3 := mul_div_block_decomposition (R*P*P) P hS
  have hd2 : d2 < 2^B-1 := rational_binary_block_lt_ones hS hSB (Nat.mod_lt (R*P) hS)
  have hd3 : d3 < 2^B-1 := rational_binary_block_lt_ones hS hSB (Nat.mod_lt (R*P*P) hS)
  have hc2 := gmin_binary_low_lt_ones hB hd2
  have hc3 := gmin_binary_low_lt_ones hB hd3
  have hc1 : gmin (B-1) A1 ≤ B+1 := rational_first_binary_block_coin_bound hS hSB hR hB
  have he2 : B+(B-1)=2*B-1 := by omega
  have he3 : B+(2*B-1)=3*B-1 := by omega
  have hg2 := gmin_binary_block B (B-1) A1 d2 (by omega)
  have hg3 := gmin_binary_block B (2*B-1) A2 d3 (by omega)
  rw [he2,show A1*2^B+d2=A2 from h2.symm] at hg2
  rw [he3,show A2*2^B+d3=A3 from h3.symm] at hg3
  have hp : 2^(3*B)=2^B*2^B*2^B := by rw [show 3*B=(B+B)+B by omega,pow_add,pow_add]
  have hA : R*2^(3*B)/S=A3 := by rw [hp]; dsimp [A3,P]; congr 1; ring
  rw [hA,hg3,hg2]
  omega

/-- Three variable rational blocks fit inside the actual axis width at
every remaining equal-companion length and primitive factor. -/
theorem equal_uniform_three_block_error_bound {a f n : ℕ}
    (ha : 6 ≤ a) (hf : f ≤ a-1) (hn : 67 ≤ n) (hcost : 2^(a+1) ≤ n+1) :
    (8*2^f*2^(a-1))*n < 2^(n-(2*a+3*(a+f))) := by
  have hmargin := sixteen_equal_length_le_of_half_cost ha hcost
  have hsmall := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
  have hU : 8*2^f*2^(a-1)=2^(a+f+2) := by
    calc
      _ = 2^3*2^f*2^(a-1) := by norm_num
      _ = _ := by rw [← pow_add,← pow_add]; congr 1; omega
  have hm := Nat.mul_lt_mul_of_pos_left (show n < 2^(n/3-2) by omega) (Nat.two_pow_pos (a+f+2))
  rw [← pow_add,show a+f+2+(n/3-2)=a+f+n/3 by omega] at hm
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show a+f+n/3 ≤ n-(2*a+3*(a+f)) by omega)
  rw [hU]
  exact lt_of_lt_of_le hm hp

/-- A unit primitive phase admits a positive index step strictly below
the primitive factor and with phase error minus one. -/
theorem exists_strict_unit_index_step {F r : ℕ}
    (hF : 2 ≤ F) (hr : Nat.Coprime r F) :
    ∃ κ : ℕ, 1 ≤ κ ∧ κ < F ∧ F ∣ κ*r+1 := by
  letI : NeZero F := ⟨by omega⟩
  obtain ⟨u,hu⟩ := (ZMod.isUnit_iff_coprime r F).mpr hr
  let κ := (-(↑(u⁻¹) : ZMod F)).val
  have hκ : κ < F := ZMod.val_lt _
  have he : (κ : ZMod F)*(r : ZMod F)+1=0 := by
    rw [show (κ : ZMod F)=-(↑(u⁻¹) : ZMod F) by exact ZMod.natCast_zmod_val _,← hu]
    rw [neg_mul,Units.inv_mul]
    ring
  have hd : F ∣ κ*r+1 := by
    apply (ZMod.natCast_eq_zero_iff (κ*r+1) F).mp
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] using he
  have hκpos : 1 ≤ κ := by
    by_contra hh
    have hz : κ=0 := by omega
    simp only [hz,zero_mul,zero_add] at hd
    have he := Nat.dvd_one.mp hd
    omega
  exact ⟨κ,hκpos,hκ,hd⟩

/-- Every odd dyadic primitive phase and unit one-each phase admit a
bounded odd index step and a bounded companion weight, at every factor. -/
theorem exists_equal_uniform_unit_step {f T r q : ℕ}
    (hf : 1 ≤ f) (hT : 0 < T) (hr : Odd r) (hq : Nat.Coprime q T) :
    ∃ κ v : ℕ, 1 ≤ κ ∧ κ < 2^f ∧ Odd κ ∧ v < T ∧ ∃ ν : ℤ,
      (2^f : ℕ)*(v : ℤ)*q-(κ : ℤ)*r=(2^f*T : ℕ)*ν+1 := by
  have hF : 2 ≤ 2^f := Nat.pow_le_pow_right (by decide : 0 < 2) hf
  obtain ⟨κ,hκpos,hκ,hd⟩ := exists_strict_unit_index_step hF (hr.coprime_two_right.pow_right f)
  have hκodd : Odd κ := by
    by_contra hh
    have hk2 : 2 ∣ κ := even_iff_two_dvd.mp ((Nat.even_or_odd κ).resolve_right hh)
    have hF2 : 2 ∣ 2^f := by
      simpa only [pow_one] using (Nat.pow_dvd_pow 2 hf)
    have hs : 2 ∣ κ*r+1 := dvd_trans hF2 hd
    have hp : 2 ∣ κ*r := dvd_mul_of_dvd_left hk2 r
    have hbad : 2 ∣ 1 := (Nat.dvd_add_iff_right hp).mpr hs
    norm_num at hbad
  obtain ⟨v,hv,ν,hν⟩ := exists_unit_phase_index_step_weight hT hq hd
  exact ⟨κ,v,hκpos,hκ,hκodd,hv,ν,hν⟩

def equalUnitStepNumerator (F s κ v : ℕ) : ℕ := F*v+2*F*s-κ*(s-1)

/-- The leading numerator of every chosen unit step is positive and
strictly below twice its full primitive denominator. -/
theorem equal_unit_step_numerator_bounds {F s T κ v : ℕ}
    (hF : 2 ≤ F) (hs : 2 ≤ s) (hT : T+1=2*s)
    (hκpos : 1 ≤ κ) (hκ : κ < F) (hv : v < T) :
    equalUnitStepNumerator F s κ v+κ*(s-1)=F*v+2*F*s ∧
      0 < equalUnitStepNumerator F s κ v ∧ equalUnitStepNumerator F s κ v < 2*(F*T) := by
  have hkP : κ*(s-1) ≤ F*s := Nat.mul_le_mul (by omega) (Nat.sub_le s 1)
  have hsub : κ*(s-1) ≤ F*v+2*F*s := by nlinarith
  have he : equalUnitStepNumerator F s κ v+κ*(s-1)=F*v+2*F*s := Nat.sub_add_cancel hsub
  have hpos : 0 < equalUnitStepNumerator F s κ v := by nlinarith
  have hvF := Nat.mul_le_mul_left F (show v+1 ≤ T by omega)
  have hpF := congrArg (fun t : ℕ ↦ F*t) hT
  have hkPpos : 1 ≤ κ*(s-1) := by
    have hh := Nat.mul_le_mul hκpos (show 1 ≤ s-1 by omega)
    simpa only [one_mul] using hh
  exact ⟨he,hpos,by nlinarith only [he,hvF,hpF,hkPpos]⟩

/-- A completely general bounded index step has at most one coin more
than twice the total companion length. -/
theorem equal_unit_step_companion_coin_bound {a D F s T κ v : ℕ}
    (ha : 1 ≤ a) (hs : s=2^(a-1)) (hDF : D*F=2*s) (hD : 0 < D)
    (hT : T+1=2*s) (hκ : κ < F) (hv : v < T) :
    gmin (a-1) (v+D*κ)+gmin (a-1) v ≤ 2*a+1 := by
  have hp : 2^a=2*s := by rw [hs,← pow_succ']; congr 1; omega
  have hkD := Nat.mul_lt_mul_of_pos_left hκ hD
  have hval : v+D*κ < 4*s := by omega
  have hquot : (v+D*κ)/2^(a-1) < 4 :=
    (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by rw [← hs]; omega)
  have hca := gmin_le_top_quotient_add_width (a-1) (v+D*κ)
  have hcb : gmin (a-1) v ≤ a-1 := gmin_le_of_lt_binary_ones (by
    rw [Nat.sub_add_cancel ha]
    omega)
  omega

def equalUniformGeometry (a D F s T : ℕ) : PrimitiveBasisGeometry :=
  ⟨a,a,D,F,T,2*F*s,F*s,s,1⟩

def equalUniformPlan (D F s κ v : ℕ) (ν : ℤ) : PrimitiveBasisRivalPlan :=
  ⟨κ,ν,v+D*κ,v,equalUnitStepNumerator F s κ v,0,0⟩

/-- Three rational blocks certify every nonintegral leading unit step,
uniformly over all equal-companion primitive factors. -/
theorem equal_uniform_nonintegral_certificate
    {a f n D F s T κ v r q : ℕ} {ν : ℤ}
    (ha : 6 ≤ a) (hf : f ≤ a-1) (hn : 67 ≤ n) (hcost : 2^(a+1) ≤ n+1)
    (hF : F=2^f) (hs : s=2^(a-1)) (hDF : D*F=2*s) (hD : 0 < D) (hT : T+1=2*s)
    (hκpos : 1 ≤ κ) (hκ : κ < F) (hv : v < T)
    (hphase : (F : ℤ)*v*q-(κ : ℤ)*r=(F*T : ℕ)*ν+1)
    (hnonint : ¬T ∣ equalUnitStepNumerator F s κ v) :
    PrimitiveBasisNonintegralCertificate (equalUniformGeometry a D F s T)
      (3*(a+f)) (8*F*s) n ((s : ℤ)-1) 1 r q (equalUniformPlan D F s κ v ν) := by
  have hFpos : 0 < F := by omega
  have hs2 : 2 ≤ s := by rw [hs]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ a-1)
  have hTp : 0 < T := by omega
  have hS : 0 < F*T := by positivity
  have hp : 2^a=2*s := by rw [hs,← pow_succ']; congr 1; omega
  have hB : 1 ≤ a+f := by omega
  have hnum := equal_unit_step_numerator_bounds (by omega : 2 ≤ F) hs2 hT hκpos hκ hv
  have hSB : F*T < 2^(a+f) := by
    calc
      F*T < F*2^a := Nat.mul_lt_mul_of_pos_left (by omega) hFpos
      _ = _ := by rw [hF,← pow_add]; congr 1; omega
  have hprefix := rational_three_binary_blocks_coin_bound hS hSB hnum.2.2 hB
  have hcomp := equal_unit_step_companion_coin_bound (by omega) hs hDF hD hT hκ hv
  have hmargin := sixteen_equal_length_le_of_half_cost ha hcost
  have hsmall : (8*F*s)*n < 2^(n-(2*a+3*(a+f))) := by
    simpa only [← hF,← hs] using equal_uniform_three_block_error_bound ha hf hn hcost
  have hTodd : Odd T := by refine ⟨s-1,?_⟩; omega
  have hrem : 0 < (equalUnitStepNumerator F s κ v*2^(3*(a+f)))%(F*T) := by
    by_contra hh
    have hd : F*T ∣ equalUnitStepNumerator F s κ v*2^(3*(a+f)) := Nat.dvd_of_mod_eq_zero (by omega)
    have ht : T ∣ 2^(3*(a+f))*equalUnitStepNumerator F s κ v := by
      simpa only [Nat.mul_comm] using dvd_trans (dvd_mul_left T F) hd
    exact hnonint ((hTodd.coprime_two_right.pow_right (3*(a+f))).dvd_of_dvd_mul_left ht)
  have hRZ : (equalUnitStepNumerator F s κ v : ℤ)=
      (F : ℤ)*v-(κ : ℤ)*((s : ℤ)-1)+2*(F : ℤ)*s := by
    have hh : (equalUnitStepNumerator F s κ v : ℤ)+(κ : ℤ)*((s-1 : ℕ) : ℤ)=
        (F : ℤ)*v+2*(F : ℤ)*s := by exact_mod_cast hnum.1
    rw [Nat.cast_sub (by omega : 1 ≤ s),Nat.cast_one] at hh
    linarith
  have hrel : PrimitiveBasisPlanRelation (equalUniformGeometry a D F s T)
      ((s : ℤ)-1) 1 r q (equalUniformPlan D F s κ v ν) := by
    refine ⟨by simp [equalUniformGeometry,equalUniformPlan,Nat.mul_comm],
      Or.inr (by simp only [equalUniformGeometry,equalUniformPlan]; omega),?_⟩
    dsimp [equalUniformGeometry,equalUniformPlan]
    push_cast at hphase ⊢
    nlinarith only [congrArg (fun z : ℤ ↦ (2*(F : ℤ)*s)*z) hphase,hRZ]
  have hJ : primitiveBasisRivalJ (equalUniformGeometry a D F s T) (equalUniformPlan D F s κ v ν) r q=-1 := by
    dsimp [primitiveBasisRivalJ,equalUniformGeometry,equalUniformPlan]
    push_cast at hphase
    linarith only [hphase]
  have hFv : (F : ℤ)*v ≤ 2*(F : ℤ)*s := by
    have hh := Nat.mul_le_mul_left F (show v ≤ 2*s by omega)
    exact_mod_cast (show F*v ≤ 2*F*s by nlinarith only [hh])
  have hkS : (κ : ℤ)*s ≤ (F : ℤ)*s := by exact_mod_cast Nat.mul_le_mul_right s (le_of_lt hκ)
  have hSS : (F*T : ℕ) ≤ 2*(F : ℤ)*s := by
    have hh := Nat.mul_le_mul_left F (show T ≤ 2*s by omega)
    exact_mod_cast (show F*T ≤ 2*F*s by nlinarith only [hh])
  have hkP : 0 ≤ (κ : ℤ)*((s : ℤ)-1) := mul_nonneg (by positivity) (by exact_mod_cast (show 0 ≤ (s : ℤ)-1 by omega))
  have hFs : (0 : ℤ) < (F : ℤ)*s := by positivity
  have hFv0 : 0 ≤ (F : ℤ)*v := by positivity
  have hκ0 : (0 : ℤ) ≤ κ := by positivity
  refine ⟨hrel,hS,by omega,by omega,by simp only [equalUniformGeometry]; omega,
    by positivity,by simpa [equalUniformGeometry,two_mul] using hsmall,
    ?_,hnum.2.1,hrem,?_,?_,?_,?_,?_⟩
  · have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show a+f ≤ 3*(a+f) by omega)
    exact le_trans (le_of_lt hSB) hh
  · dsimp [equalUniformGeometry,equalUniformPlan]
    omega
  all_goals try rw [hJ]
  all_goals dsimp [primitiveBasisRivalA,primitiveBasisRivalB,equalUniformGeometry,equalUniformPlan]
  all_goals norm_num
  all_goals push_cast at hSS
  all_goals nlinarith only [hFv,hkS,hSS,hkP,hFs,hFv0,hκ0]

/-- Every nonintegral leading unit step has a complete affordable actual
rival, uniformly in both companion length and primitive factor. -/
theorem exists_equal_uniform_nonintegral_rival
    {a f n N L D F s T M E H c V α z r q κ v : ℕ} {ν : ℤ}
    (ha : 6 ≤ a) (hf : f ≤ a-1) (hn : 67 ≤ n) (hcost : 2^(a+1) ≤ n+1)
    (hF : F=2^f) (hs : s=2^(a-1)) (hDF : D*F=2*s) (hD : 0 < D) (hT : T+1=2*s)
    (hL : L+2*a=n) (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=2*F*s*2^L) (hE : E ≤ F*s*H)
    (hκpos : 1 ≤ κ) (hκ : κ < F) (hv : v < T)
    (hphase : (F : ℤ)*v*q-(κ : ℤ)*r=(F*T : ℕ)*ν+1)
    (hnonint : ¬T ∣ equalUnitStepNumerator F s κ v)
    (hap : (F*T : ℕ)*(α : ℤ)=((s : ℤ)-1)*((2 : ℤ)^L-H)+(s : ℤ)*c+(r : ℤ)*M)
    (hzp : (T : ℤ)*z=(2 : ℤ)^L+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*M)
    (x b d : ZMod N) (hα : α • x=D • b) (hz : z • x+b+d=V • x) (hmx : M • x=0) :
    ∃ w, n ≤ w ∧ (v+D*κ ≠ 2^a-1 ∨ v ≠ 2^a-1) ∧ ∃ k,
      val L k=w ∧ dsum L k+gmin (a-1) (v+D*κ)+gmin (a-1) v ≤ n ∧
      w • x+(v+D*κ) • b+v • d=V • x := by
  have hcert := equal_uniform_nonintegral_certificate ha hf hn hcost hF hs hDF hD hT
    hκpos hκ hv hphase hnonint
  have hh := exists_rival_of_primitive_basis_nonintegral_certificate
    (equalUniformGeometry a D F s T) (equalUniformPlan D F s κ v ν)
    (n:=n) (L:=L) (N:=N) (M:=M) (E:=E) (H:=H) (c:=c) (V:=V) (α:=α) (z:=z)
    (P:=(s : ℤ)-1) (Q:=1) (r:=r) (q:=q) (by rfl)
    (by simpa [equalUniformGeometry,two_mul,add_assoc] using hL) hH hnc hbase hM hE
    hap (by simpa [equalUniformGeometry] using hzp) x b d hα hz hmx hcert
  exact hh

/-- An integral odd leading denominator forces a dyadic boundary above
one full width and symmetric companion weights around top minus one. -/
theorem equal_unit_step_integral_classification
    {D F s T κ v : ℕ} (hF : 2 ≤ F) (hs : 2 ≤ s) (hFs : F ∣ s)
    (hDF : D*F=2*s) (hT : T+1=2*s) (hκpos : 1 ≤ κ) (hκ : κ < F)
    (hκodd : Odd κ) (hv : v < T) (hint : T ∣ equalUnitStepNumerator F s κ v) :
    ∃ m δ : ℕ, Odd m ∧ F < m ∧ m < 2*F ∧ m+κ=2*F ∧
      equalUnitStepNumerator F s κ v=m*T ∧ 1 ≤ δ ∧ δ < s ∧
      v+δ=T-1 ∧ D*κ=2*δ := by
  have hFp : 0 < F := by omega
  have hTp : 0 < T := by omega
  have hn := equal_unit_step_numerator_bounds hF hs hT hκpos hκ hv
  obtain ⟨u,hu⟩ := hFs
  have hup : 1 ≤ u := by nlinarith only [hu,hs]
  let δ := κ*u
  have hδp : 1 ≤ δ := by
    have hh := Nat.mul_le_mul hκpos hup
    simpa only [one_mul,δ] using hh
  have hδs : δ < s := by
    have hh := Nat.mul_lt_mul_of_pos_right hκ (show 0 < u by omega)
    simpa only [← hu,δ] using hh
  have hFδ : F*δ=κ*s := by dsimp [δ]; rw [hu]; ring
  obtain ⟨m,hm⟩ := hint
  have hmR : equalUnitStepNumerator F s κ v=m*T := by simpa only [Nat.mul_comm] using hm
  have hmp : 1 ≤ m := by nlinarith only [hm,hn.2.1]
  have hmhi : m < 2*F := by
    apply Nat.lt_of_mul_lt_mul_left (a:=T)
    nlinarith only [hm,hn.2.2]
  have hnumZ : (equalUnitStepNumerator F s κ v : ℤ)+(κ : ℤ)*((s : ℤ)-1)=
      (F : ℤ)*v+2*(F : ℤ)*s := by
    have hh := hn.1
    have hhZ : (equalUnitStepNumerator F s κ v : ℤ)+(κ : ℤ)*(s-1 : ℕ)=
        (F : ℤ)*v+2*(F : ℤ)*s := by exact_mod_cast hh
    simpa only [Nat.cast_sub (by omega : 1 ≤ s),Nat.cast_one] using hhZ
  have hmZ : (equalUnitStepNumerator F s κ v : ℤ)=(m : ℤ)*T := by exact_mod_cast hmR
  have htZ : (T : ℤ)+1=2*s := by exact_mod_cast hT
  have hsZ : (s : ℤ)=(F : ℤ)*u := by exact_mod_cast hu
  have hd : F ∣ m+κ := by
    have hh : (F : ℤ) ∣ (m : ℤ)+κ := by
      refine ⟨2*(u : ℤ)*m-v-2*s+(κ : ℤ)*u,?_⟩
      linear_combination -hnumZ+(m : ℤ)*htZ+hmZ+(2*(m : ℤ)+κ)*hsZ
    exact_mod_cast hh
  obtain ⟨j,hj⟩ := hd
  have hjpos : 1 ≤ j := by nlinarith only [hj,hmp,hκpos]
  have hjhi : j < 3 := by
    apply Nat.lt_of_mul_lt_mul_left (a:=F)
    nlinarith only [hj,hmhi,hκ]
  have hsum : m+κ=2*F := by
    have hjcases : j=1 ∨ j=2 := by omega
    rcases hjcases with rfl | rfl
    · have hjZ : (m : ℤ)+κ=F := by exact_mod_cast (show m+κ=F by omega)
      have hbad : (F : ℤ)*v+(κ : ℤ)*s+F=0 := by
        linear_combination -hnumZ+hmZ+(m : ℤ)*htZ+(2*(s : ℤ)-1)*hjZ
      have hpos : (0 : ℤ) < (F : ℤ)*v+(κ : ℤ)*s+F := by positivity
      linarith
    · omega
  have hveq : v+δ=T-1 := by
    have htM := congrArg (fun t : ℕ ↦ m*t) hT
    have hkS := congrArg (fun t : ℕ ↦ κ*t) (show s-1+1=s by omega)
    have hsumS := congrArg (fun t : ℕ ↦ t*s) hsum
    have hmul : F*(v+δ+2)=F*(2*s) := by
      nlinarith only [hn.1,hmR,htM,hkS,hsumS,hFδ,hsum]
    have he : v+δ+2=2*s := (mul_left_cancel₀ (ne_of_gt hFp)) hmul
    omega
  have hDκ : D*κ=2*δ := by
    have hh := congrArg (fun t : ℕ ↦ t*κ) hDF
    have hmul : F*(D*κ)=F*(2*δ) := by nlinarith only [hh,hFδ]
    exact (mul_left_cancel₀ (ne_of_gt hFp)) hmul
  have hmOdd : Odd m := by
    obtain ⟨k,hk⟩ := hκodd
    refine ⟨F-k-1,?_⟩
    omega
  exact ⟨m,δ,hmOdd,by omega,hmhi,hsum,hmR,hδp,hδs,hveq,hDκ⟩

/-- Symmetric integral-step companions cost at most one coin less than
twice their common length, independently of the primitive factor. -/
theorem equal_integral_symmetric_companion_coin_bound {a s T v δ : ℕ}
    (ha : 2 ≤ a) (hs : s=2^(a-1)) (hT : T+1=2*s)
    (hδp : 1 ≤ δ) (hδs : δ < s) (hv : v+δ=T-1) :
    gmin (a-1) (v+2*δ)+gmin (a-1) v ≤ 2*a-1 := by
  have hp : 2^a=2*s := by rw [hs,← pow_succ']; congr 1; omega
  have hTpow : T=2^a-1 := by omega
  have hcb : gmin (a-1) v ≤ a-1 := gmin_le_of_lt_binary_ones (by
    rw [show a-1+1=a by omega]
    omega)
  have hca : gmin (a-1) (v+2*δ) ≤ a := by
    by_cases he : δ=1
    · have hh : v+2*δ=T := by omega
      rw [hh,hTpow]
      simpa only [Nat.sub_add_cancel (show 1 ≤ a by omega)] using le_of_eq (gmin_ones (a-1))
    · have hlow : δ-2 < 2^(a-1)-1 := by rw [← hs]; omega
      have hc := gmin_binary_low_lt_ones (by omega : 1 ≤ a-1) hlow
      have hh : v+2*δ=(δ-2)+s+s := by omega
      rw [hh,hs,gmin_add_pow,gmin_add_pow]
      omega
  omega

/-- The even prefix immediately below an odd dyadic boundary saves one
coin; the boundary itself has the ordinary top-quotient bound. -/
theorem odd_dyadic_boundary_prefix_coin_bounds {f m : ℕ}
    (hf : 1 ≤ f) (hm : Odd m) (hhi : m < 2*2^f) :
    gmin (f-1) (m-1) ≤ f+1 ∧ gmin (f-1) m ≤ f+2 := by
  have hp : 2^f=2*2^(f-1) := by rw [← pow_succ']; congr 1; omega
  have hq : m/2^(f-1) < 4 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by omega)
  have hupper := gmin_le_top_quotient_add_width (f-1) m
  refine ⟨?_,by omega⟩
  by_cases he : f=1
  · subst f
    norm_num [gmin] at hhi ⊢
    omega
  · obtain ⟨k,hk⟩ := hm
    have hmod : (m-1)%2=0 := by omega
    have hp' : 2^f=4*2^(f-2) := by rw [show f=2+(f-2) by omega,pow_add]; norm_num
    have hq' : ((m-1)/2)/2^(f-2) < 4 :=
      (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by omega)
    have hc := gmin_le_top_quotient_add_width (f-2) ((m-1)/2)
    rw [show f-1=(f-2)+1 by omega,gmin,hmod,zero_add]
    omega

/-- Every bounded unit index step has a common signed linear error
window, whether its leading phase is integral or nonintegral. -/
theorem equal_unit_step_signed_error_window
    {F s T κ v n K H c E R : ℕ} {Z : ℤ}
    (hF : 2 ≤ F) (hs : 2 ≤ s) (hT : T+1=2*s) (hκ : κ < F) (hv : v < T)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hE : E ≤ F*s*H)
    (herr : (F*T : ℕ)*Z-(R : ℤ)*K=
      ((F*T : ℕ)-(F : ℤ)*v+(κ : ℤ)*((s : ℤ)-1))*H+
      ((F*T : ℕ)-(F : ℤ)*v-(κ : ℤ)*s)*c-(F*T : ℕ)-E) :
    -((8*F*s : ℕ) : ℤ)*n < (F*T : ℕ)*Z-(R : ℤ)*K ∧
      (F*T : ℕ)*Z-(R : ℤ)*K < ((8*F*s : ℕ) : ℤ)*n := by
  have hS : 0 < F*T := by
    have hTp : 0 < T := by omega
    positivity
  have hFv : (F : ℤ)*v ≤ 2*(F : ℤ)*s := by
    have hh := Nat.mul_le_mul_left F (show v ≤ 2*s by omega)
    exact_mod_cast (show F*v ≤ 2*F*s by nlinarith only [hh])
  have hkS : (κ : ℤ)*s ≤ (F : ℤ)*s := by exact_mod_cast Nat.mul_le_mul_right s (le_of_lt hκ)
  have hSS : (F : ℤ)*T ≤ 2*(F : ℤ)*s := by
    have hh := Nat.mul_le_mul_left F (show T ≤ 2*s by omega)
    exact_mod_cast (show F*T ≤ 2*F*s by nlinarith only [hh])
  have hkP : 0 ≤ (κ : ℤ)*((s : ℤ)-1) := mul_nonneg (by positivity) (by omega)
  have hFs : (0 : ℤ) < (F : ℤ)*s := by positivity
  have hFv0 : 0 ≤ (F : ℤ)*v := by positivity
  have hκ0 : (0 : ℤ) ≤ κ := by positivity
  have hκs0 : (0 : ℤ) ≤ (κ : ℤ)*s := by positivity
  have hS0 : (0 : ℤ) ≤ (F : ℤ)*T := by positivity
  have hw := signed_rival_linear_error_window (S:=F*T) (W:=F*s)
    (A:=(F*T : ℕ)-(F : ℤ)*v+(κ : ℤ)*((s : ℤ)-1))
    (B:=(F*T : ℕ)-(F : ℤ)*v-(κ : ℤ)*s) (J:=-1) (C:=8*(F : ℤ)*s)
    hH hnc hE hS (by positivity)
    (by norm_num; nlinarith only [hFv,hkS,hSS,hkP,hFs,hFv0,hκ0,hκs0,hS0])
    (by norm_num; nlinarith only [hFv,hkS,hSS,hkP,hFs,hFv0,hκ0,hκs0,hS0])
    (by norm_num; nlinarith only [hFv,hkS,hSS,hkP,hFs,hFv0,hκ0,hκs0,hS0])
    (by norm_num; nlinarith only [hFv,hkS,hSS,hkP,hFs,hFv0,hκ0,hκs0,hS0])
  push_cast at herr hw ⊢
  constructor <;> nlinarith only [herr,hw.1,hw.2]

/-- The final dyadic block dominates the signed error, and the error
itself fits into one third of the dimension's binary budget. -/
theorem equal_uniform_integral_block_budget {a f n L : ℕ}
    (ha : 6 ≤ a) (hf : f ≤ a-1) (hn : 67 ≤ n)
    (hcost : 2^(a+1) ≤ n+1) (hL : L+2*a=n) :
    f ≤ L ∧ 8*n < 2^(L-f) ∧ 8*n < 2^(n/3) ∧ n/3+f+2+2*a-1 ≤ n := by
  have hm := sixteen_equal_length_le_of_half_cost ha hcost
  have hh := equal_uniform_three_block_error_bound ha hf hn hcost
  have hU : 8 ≤ 8*2^f*2^(a-1) := by
    have hp := Nat.mul_le_mul (Nat.one_le_two_pow (n:=f)) (Nat.one_le_two_pow (n:=a-1))
    nlinarith only [hp]
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show n-(2*a+3*(a+f)) ≤ L-f by omega)
  have hw : 8*n < 2^(L-f) := lt_of_le_of_lt (Nat.mul_le_mul_right n hU) (lt_of_lt_of_le hh hp)
  have ht := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
  have htp : 4*2^(n/3-2)=2^(n/3) := by
    rw [show n/3=2+(n/3-2) by omega,pow_add]
    norm_num
  exact ⟨by omega,hw,by nlinarith only [ht,htp],by omega⟩

/-- An odd dyadic boundary has an affordable representation on either
side throughout the common signed error window. -/
theorem exists_rep_near_equal_integral_boundary
    {a f n L m : ℕ} {Z : ℤ}
    (ha : 6 ≤ a) (hfpos : 1 ≤ f) (hf : f ≤ a-1) (hn : 67 ≤ n)
    (hcost : 2^(a+1) ≤ n+1) (hL : L+2*a=n)
    (hm : Odd m) (hmlo : 2^f < m) (hmhi : m < 2*2^f)
    (hlo : -(8*(n : ℤ)) < Z-(m : ℤ)*2^(L-f))
    (hhi : Z-(m : ℤ)*2^(L-f) < 8*(n : ℤ)) :
    (n : ℤ) ≤ Z ∧ ∃ k, val L k=Z.toNat ∧ dsum L k+(2*a-1) ≤ n := by
  have hb := equal_uniform_integral_block_budget ha hf hn hcost hL
  have hc := odd_dyadic_boundary_prefix_coin_bounds hfpos hm hmhi
  have hmp : 2 ≤ m := by have := Nat.one_le_two_pow (n:=f); omega
  have hpZ : (8 : ℤ)*n < 2^(L-f) := by exact_mod_cast hb.2.1
  have hmZ : (2 : ℤ) ≤ m := by exact_mod_cast hmp
  have hp0 : (0 : ℤ) < 2^(L-f) := by positivity
  have hmP := mul_le_mul_of_nonneg_right hmZ (le_of_lt hp0)
  have hZlo : (n : ℤ) ≤ Z := by nlinarith only [hlo,hpZ,hmP]
  have hZ0 : 0 ≤ Z := le_trans (by positivity) hZlo
  have hZcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hZ0
  have hlen : L-f+(f-1+1)=L := by omega
  refine ⟨hZlo,?_⟩
  by_cases hbelow : Z.toNat < m*2^(L-f)
  · have hbZ : (Z.toNat : ℤ) < (m : ℤ)*2^(L-f) := by exact_mod_cast hbelow
    have hlowZ : ((m-1 : ℕ) : ℤ)*2^(L-f) ≤ Z.toNat := by
      rw [Nat.cast_sub (by omega : 1 ≤ m),Nat.cast_one,hZcast]
      nlinarith only [hlo,hpZ]
    have hlow : (m-1)*2^(L-f) ≤ Z.toNat := by exact_mod_cast hlowZ
    let tail := Z.toNat-(m-1)*2^(L-f)
    have heq : (m-1)*2^(L-f)+tail=Z.toNat := Nat.add_sub_of_le hlow
    have hprod : (m-1)*2^(L-f)+2^(L-f)=m*2^(L-f) := by
      have hh := congrArg (fun t : ℕ ↦ t*2^(L-f)) (Nat.sub_add_cancel (by omega : 1 ≤ m))
      nlinarith only [hh]
    have htail : tail < 2^(L-f) := by omega
    obtain ⟨k,hk,hkc⟩ := exists_rep_binary_block_tail (f-1) (L-f) (m-1) tail htail
    rw [hlen,heq] at hk
    rw [hlen] at hkc
    exact ⟨k,hk,by omega⟩
  · have hlow : m*2^(L-f) ≤ Z.toNat := by omega
    let tail := Z.toNat-m*2^(L-f)
    have heq : m*2^(L-f)+tail=Z.toNat := Nat.add_sub_of_le hlow
    have heqZ : (m : ℤ)*2^(L-f)+(tail : ℤ)=Z := by
      have hh : (m : ℤ)*2^(L-f)+(tail : ℤ)=(Z.toNat : ℤ) := by exact_mod_cast heq
      rwa [hZcast] at hh
    have htail8 : tail < 8*n := by
      have hh : (tail : ℤ) < 8*(n : ℤ) := by linarith only [heqZ,hhi]
      exact_mod_cast hh
    obtain ⟨k,hk,hkc⟩ := exists_rep_binary_block_bounded_tail (f-1) (L-f) (n/3) m tail
      (by omega) (lt_trans htail8 hb.2.2.1)
    rw [hlen,heq] at hk
    rw [hlen] at hkc
    exact ⟨k,hk,by omega⟩

/-- Integral leading unit steps give complete affordable actual rivals
at every dyadic primitive factor. -/
theorem exists_equal_uniform_integral_rival
    {a f n N L D F s T M E H c V α z r q κ v : ℕ} {ν : ℤ}
    (ha : 6 ≤ a) (hfpos : 1 ≤ f) (hf : f ≤ a-1) (hn : 67 ≤ n) (hcost : 2^(a+1) ≤ n+1)
    (hF : F=2^f) (hs : s=2^(a-1)) (hFs : F ∣ s) (hDF : D*F=2*s) (hT : T+1=2*s)
    (hL : L+2*a=n) (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=2*F*s*2^L) (hE : E ≤ F*s*H)
    (hκpos : 1 ≤ κ) (hκ : κ < F) (hκodd : Odd κ) (hv : v < T)
    (hphase : (F : ℤ)*v*q-(κ : ℤ)*r=(F*T : ℕ)*ν+1)
    (hint : T ∣ equalUnitStepNumerator F s κ v)
    (hap : (F*T : ℕ)*(α : ℤ)=((s : ℤ)-1)*((2 : ℤ)^L-H)+(s : ℤ)*c+(r : ℤ)*M)
    (hzp : (T : ℤ)*z=(2 : ℤ)^L+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*M)
    (x b d : ZMod N) (hα : α • x=D • b) (hz : z • x+b+d=V • x) (hmx : M • x=0) :
    ∃ w, n ≤ w ∧ (v+D*κ ≠ 2^a-1 ∨ v ≠ 2^a-1) ∧ ∃ k,
      val L k=w ∧ dsum L k+gmin (a-1) (v+D*κ)+gmin (a-1) v ≤ n ∧
      w • x+(v+D*κ) • b+v • d=V • x := by
  have hF2 : 2 ≤ F := by rw [hF]; exact Nat.pow_le_pow_right (by decide : 0 < 2) hfpos
  have hs2 : 2 ≤ s := by rw [hs]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ a-1)
  have hTp : 0 < T := by omega
  have hSZ : (0 : ℤ) < (F*T : ℕ) := by positivity
  obtain ⟨m,δ,hm,hmlo,hmhi,hmsum,hmR,hδp,hδs,hvδ,hDκ⟩ :=
    equal_unit_step_integral_classification hF2 hs2 hFs hDF hT hκpos hκ hκodd hv hint
  have hcomp := equal_integral_symmetric_companion_coin_bound (by omega) hs hT hδp hδs hvδ
  rw [← hDκ] at hcomp
  let Z : ℤ := (v : ℤ)*z-(κ : ℤ)*α+(1-(v : ℤ))*V-ν*M
  have hnum := equal_unit_step_numerator_bounds hF2 hs2 hT hκpos hκ hv
  have hR : (equalUnitStepNumerator F s κ v : ℤ)=
      (F : ℤ)*v-(κ : ℤ)*((s : ℤ)-1)+(2*F*s : ℕ) := by
    have hh : (equalUnitStepNumerator F s κ v : ℤ)+(κ : ℤ)*((s-1 : ℕ) : ℤ)=
        (F : ℤ)*v+2*(F : ℤ)*s := by exact_mod_cast hnum.1
    rw [Nat.cast_sub (by omega : 1 ≤ s),Nat.cast_one] at hh
    push_cast
    linarith only [hh]
  have herr := unit_phase_index_step_rival_error hbase hM hphase hR
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hap)
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hzp)
  have hw := equal_unit_step_signed_error_window hF2 hs2 hT hκ hv hH hnc hE herr
  change -((8*F*s : ℕ) : ℤ)*n < (F*T : ℕ)*Z-(equalUnitStepNumerator F s κ v : ℤ)*(2^L : ℕ) ∧
    (F*T : ℕ)*Z-(equalUnitStepNumerator F s κ v : ℤ)*(2^L : ℕ) < ((8*F*s : ℕ) : ℤ)*n at hw
  have hb := equal_uniform_integral_block_budget ha hf hn hcost hL
  have hK : 2^L=F*2^(L-f) := by rw [hF,← pow_add]; congr 1; omega
  have hboundary : (F*T : ℕ)*((m : ℤ)*2^(L-f))=
      (equalUnitStepNumerator F s κ v : ℤ)*(2^L : ℕ) := by
    rw [hmR,hK]
    push_cast
    ring
  have hU : ((8*F*s : ℕ) : ℤ)*n ≤ 8*(F*T : ℕ)*(n : ℤ) := by
    have hh := Nat.mul_le_mul_left (8*F*n) (show s ≤ T by omega)
    exact_mod_cast (show (8*F*s)*n ≤ 8*(F*T)*n by nlinarith only [hh])
  have hlo : -(8*(n : ℤ)) < Z-(m : ℤ)*2^(L-f) := by
    apply (mul_lt_mul_iff_right₀ hSZ).mp
    nlinarith only [hw.1,hboundary,hU]
  have hhi : Z-(m : ℤ)*2^(L-f) < 8*(n : ℤ) := by
    apply (mul_lt_mul_iff_right₀ hSZ).mp
    nlinarith only [hw.2,hboundary,hU]
  obtain ⟨hZ,k,hk,hkc⟩ := exists_rep_near_equal_integral_boundary ha hfpos hf hn hcost hL hm
    (by simpa only [← hF] using hmlo) (by simpa only [← hF] using hmhi) hlo hhi
  have hZ0 : 0 ≤ Z := le_trans (by positivity) hZ
  have hZcast := Int.toNat_of_nonneg hZ0
  have hnat : n ≤ Z.toNat := by exact_mod_cast (show (n : ℤ) ≤ (Z.toNat : ℤ) by omega)
  have hp : 2^a=2*s := by rw [hs,← pow_succ']; congr 1; omega
  refine ⟨Z.toNat,hnat,Or.inr (by omega),k,hk,by omega,?_⟩
  exact signed_axis_basis_rival_eq x b d (κ : ℤ) ν (by push_cast; ring) hz hα hmx hZ0

/-- Every remaining odd/unit primitive phase has an affordable actual
rival, uniformly over all equal companion lengths and actual indices. -/
theorem exists_equal_uniform_primitive_rival
    {a f n N L D F s T M E H c V α z r q : ℕ}
    (ha : 6 ≤ a) (hfpos : 1 ≤ f) (hf : f ≤ a-1) (hn : 67 ≤ n) (hcost : 2^(a+1) ≤ n+1)
    (hF : F=2^f) (hs : s=2^(a-1)) (hFs : F ∣ s) (hDF : D*F=2*s) (hD : 0 < D) (hT : T+1=2*s)
    (hL : L+2*a=n) (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=2*F*s*2^L) (hE : E ≤ F*s*H) (hr : Odd r) (hq : Nat.Coprime q T)
    (hap : (F*T : ℕ)*(α : ℤ)=((s : ℤ)-1)*((2 : ℤ)^L-H)+(s : ℤ)*c+(r : ℤ)*M)
    (hzp : (T : ℤ)*z=(2 : ℤ)^L+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*M)
    (x b d : ZMod N) (hα : α • x=D • b) (hz : z • x+b+d=V • x) (hmx : M • x=0) :
    ∃ w ta tb, n ≤ w ∧ (ta ≠ 2^a-1 ∨ tb ≠ 2^a-1) ∧ ∃ k,
      val L k=w ∧ dsum L k+gmin (a-1) ta+gmin (a-1) tb ≤ n ∧
      w • x+ta • b+tb • d=V • x := by
  have hspos : 1 ≤ s := by rw [hs]; exact Nat.one_le_two_pow
  obtain ⟨κ,v,hκpos,hκ,hκodd,hv,ν,hphase⟩ :=
    exists_equal_uniform_unit_step hfpos (by omega : 0 < T) hr hq
  rw [← hF] at hκ hphase
  have hh : ∃ w, n ≤ w ∧ (v+D*κ ≠ 2^a-1 ∨ v ≠ 2^a-1) ∧ ∃ k,
      val L k=w ∧ dsum L k+gmin (a-1) (v+D*κ)+gmin (a-1) v ≤ n ∧
      w • x+(v+D*κ) • b+v • d=V • x := by
    by_cases hint : T ∣ equalUnitStepNumerator F s κ v
    · exact exists_equal_uniform_integral_rival ha hfpos hf hn hcost hF hs hFs hDF hT
        hL hH hnc hbase hM hE hκpos hκ hκodd hv hphase hint hap hzp x b d hα hz hmx
    · exact exists_equal_uniform_nonintegral_rival ha hf hn hcost hF hs hDF hD hT
        hL hH hnc hbase hM hE hκpos hκ hv hphase hint hap hzp x b d hα hz hmx
  obtain ⟨w,hw,hd,k,hk,hkc,heq⟩ := hh
  exact ⟨w,v+D*κ,v,hw,hd,k,hk,hkc,heq⟩

end MinModulus
