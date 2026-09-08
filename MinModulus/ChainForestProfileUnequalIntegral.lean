import MinModulus.ChainForestProfileUnequalIntegralArithmetic

/-! Complete closure of unequal companions with a maximal even collision
axis, in dimensions at least sixty-seven. Integral unit phases now give
actual affordable rivals at every index and either error sign. Combining
this with the earlier phase exclusions and equal-companion closure gives
the sharp bound for the whole maximal-even-axis three-chain family.
Other axes/profile families and the unrestricted conjecture remain open. -/

namespace MinModulus

/-- All integral unequal unit phases admit full affordable actual rivals,
including either error sign and the largest possible actual index. -/
theorem exists_unequal_normalized_integral_unit_rival
    {a b f n L N D F s t u T H c V M E α z r q : ℕ} {P Q ε : ℤ}
    (ha : 2 ≤ a) (hab : a < b) (hsum : 10 < a+b) (hf : f ≤ a-2) (hn : 67 ≤ n)
    (hL : L+a+b=n) (hD2 : 2 ≤ D) (hF : F=2^f) (hs : s=2^(a-1)) (ht : t=2^(b-1))
    (hDF : D*F=s) (htu : t=s*u) (hupow : u=2^(b-a)) (hu : 2 ≤ u) (hT : T+u+1=4*t) (_hTodd : Odd T)
    (hcost : 3*s+t ≤ n+1) (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=4*F*t*2^L) (hE : E ≤ F*t*H)
    (hcase : (P=(t : ℤ)-1 ∧ Q=3-(u : ℤ) ∧ ε=-1) ∨
      (P=1-3*(t : ℤ) ∧ Q=3*(u : ℤ)-1 ∧ ε=1))
    (hlink : T ∣ 4*r+q) (hr : Nat.Coprime r (F*T))
    (hint : (T : ℤ) ∣ P+4*(F : ℤ)*t*r)
    (hap : (F*T : ℕ)*(α : ℤ)=P*((2 : ℤ)^L-H)+(t : ℤ)*c+(r : ℤ)*M)
    (hzp : (T : ℤ)*z=Q*(2 : ℤ)^L+((T : ℤ)-Q)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*M)
    (x y w : ZMod N) (hα : α • x=D • y) (hz : z • x+y+w=V • x) (hmx : M • x=0)
    (htop : (2^L-1) • x+(2*s-1) • y+(2*t-1) • w=V • x) :
    ∃ ta tb, (ta ≠ 2^a-1 ∨ tb ≠ 2^b-1) ∧ ∃ v, n ≤ v ∧ ∃ k,
      val L k=v ∧ dsum L k+gmin (a-1) ta+gmin (b-1) tb ≤ n ∧
      v • x+ta • y+tb • w=V • x := by
  have hD : 0 < D := by omega
  have hs2 : 2 ≤ s := by rw [hs]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ a-1)
  have hFp : 0 < F := by rw [hF]; positivity
  have htus : 2*u ≤ t := by nlinarith only [Nat.mul_le_mul_right u hs2,htu]
  have ht2 : 2 ≤ t := by omega
  have hTp : 2 ≤ T := by omega
  have hFT2 : 2 ≤ F*T := by nlinarith only [Nat.mul_le_mul_left F hTp,hFp]
  have hTlt : T < 4*t := by omega
  have hε : ε=-1 ∨ ε=1 := by rcases hcase with ⟨_,_,he⟩ | ⟨_,_,he⟩ <;> omega
  obtain ⟨m,hmpos,hm,l,hml⟩ := exists_strict_signed_unit_multiplier hFT2 hr hε
  obtain ⟨p,hp⟩ := hlink
  let C := 4*s-1
  have hC : C+1=4*s := by dsimp [C]; omega
  let ta := unequalNormalizedShortWeight D C m
  let tb := unequalNormalizedLongWeight D C m
  obtain ⟨hta,htb,hdec,hpos⟩ := unequal_normalized_companion_weight_bounds hD hs2 hDF htu hu hC hT hmpos hm
  change ta < C at hta
  change tb < t at htb
  change ta+C*tb=D*m at hdec
  change 0 < ta+tb at hpos
  let κ : ℤ := (m : ℤ)-4*(F : ℤ)*tb
  let ν : ℤ := (tb : ℤ)*p-l
  let R : ℤ := (F : ℤ)*tb*Q-κ*P-4*(F : ℤ)*t*ε
  let Z : ℤ := (tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M
  let A : ℤ := (F*T : ℕ)-(F : ℤ)*tb*Q+κ*P
  let B : ℤ := (F*T : ℕ)-(F : ℤ)*tb*(u+1)-κ*t
  have hi : (ta : ℤ)=tb+(D : ℤ)*κ := unequal_normalized_signed_index_relation hDF hC hdec
  have hphase : (F*T : ℕ)*ν-(F : ℤ)*tb*q+κ*r=ε := by
    have hh := unequal_normalized_phase_relation hp.symm hml (tb:=tb)
    dsimp only [ν,κ]
    push_cast at hh ⊢
    linarith only [hh]
  have hTZ : (T : ℤ)+u+1=4*(t : ℤ) := by exact_mod_cast hT
  have hcancel : (T : ℤ) ∣ (F : ℤ)*tb*(Q+4*P) := by
    rcases hcase with ⟨hP,hQ,_⟩ | ⟨hP,hQ,_⟩
    · refine ⟨(F : ℤ)*tb,?_⟩
      rw [hP,hQ]
      linear_combination -(F : ℤ)*tb*hTZ
    · refine ⟨-3*(F : ℤ)*tb,?_⟩
      rw [hP,hQ]
      linear_combination 3*(F : ℤ)*tb*hTZ
  have hRint : (T : ℤ) ∣ R := unequal_normalized_integral_unit_leading_dvd hml rfl rfl hcancel hint
  have hRbounds : -2*(F*T : ℕ) < R ∧ R < 2*(F*T : ℕ) ∧ (R ≤ 0 → ta < 2*s) := by
    rcases hcase with ⟨hP,hQ,he⟩ | ⟨hP,hQ,he⟩
    · have hid := unequal_normalized_short_leading_identity hD hDF htu hC hdec
      have hbd := unequal_normalized_short_leading_bounds hD hs2 hDF htu hu hC hT hta htb hdec hpos
      have heq : R=4*(F : ℤ)*t-(F : ℤ)*u*ta+m-(F : ℤ)*tb := by
        dsimp [R,κ]
        rw [hP,hQ,he]
        linarith only [hid]
      rw [heq]
      have hS0 : (0 : ℤ) ≤ (F*T : ℕ) := by positivity
      exact ⟨by linarith only [hbd.1,hS0],hbd.2,by intro hh; linarith only [hh,hbd.1]⟩
    · have hid := unequal_normalized_long_leading_identity hD hDF htu hC hdec
      have hbd := unequal_normalized_long_leading_bounds hD hs2 hDF htu hu hC hT hta htb hdec hpos
      have heq : R=-4*(F : ℤ)*t+3*(F : ℤ)*u*ta-m+3*(F : ℤ)*tb := by
        dsimp [R,κ]
        rw [hP,hQ,he]
        linarith only [hid]
      rwa [heq]
  have hcopDC : Nat.Coprime D C := by
    apply Nat.coprime_iff_gcd_eq_one.mpr
    apply Nat.dvd_one.mp
    have hd : Nat.gcd D C ∣ C := Nat.gcd_dvd_right D C
    have hfour : Nat.gcd D C ∣ 4*s := by
      apply dvd_trans (Nat.gcd_dvd_left D C)
      exact ⟨4*F,by rw [← hDF]; ring⟩
    have hh : Nat.gcd D C ∣ C+1 := by rwa [hC]
    exact (Nat.dvd_add_iff_right hd).mpr hh
  have hoddplan : f=0 ∨ (Odd m ∧ Odd R ∧ Odd ((F*T : ℕ)-R)) := by
    by_cases hf0 : f=0
    · exact Or.inl hf0
    have hF2 : 2 ∣ F := by
      rw [hF]
      simpa only [pow_one] using Nat.pow_dvd_pow 2 (by omega : 1 ≤ f)
    have hmOdd := odd_multiplier_of_even_factor_signed_unit_phase hF2 hε hml
    have htEven : 2 ∣ t := by
      rw [ht]
      simpa only [pow_one] using Nat.pow_dvd_pow 2 (by omega : 1 ≤ b-1)
    obtain ⟨t0,ht0⟩ := htEven
    have hPOdd : Odd P := by
      rcases hcase with ⟨hP,_,_⟩ | ⟨hP,_,_⟩
      · refine ⟨(t0 : ℤ)-1,?_⟩
        rw [hP,ht0]
        push_cast
        ring
      · refine ⟨-3*(t0 : ℤ),?_⟩
        rw [hP,ht0]
        push_cast
        ring
    have hh := odd_normalized_unit_numerators (T:=T) hF2 hmOdd hPOdd rfl rfl (Q:=Q) (ε:=ε) (R:=R)
    exact Or.inr ⟨hmOdd,hh.1,hh.2⟩
  have hPbound : |P| ≤ 3*(t : ℤ) := by
    have htZ : (2 : ℤ) ≤ t := by exact_mod_cast ht2
    rw [abs_le]
    rcases hcase with ⟨hP,_,_⟩ | ⟨hP,_,_⟩ <;> rw [hP] <;> constructor <;> omega
  have hQbound : |Q| ≤ 3*(t : ℤ) := by
    have htZ : (2 : ℤ) ≤ t := by exact_mod_cast ht2
    have huZ : (2 : ℤ) ≤ u := by exact_mod_cast hu
    have hut : (u : ℤ) ≤ t := by exact_mod_cast (show u ≤ t by omega)
    rw [abs_le]
    rcases hcase with ⟨_,hQ,_⟩ | ⟨_,hQ,_⟩ <;> rw [hQ] <;> constructor <;> omega
  have hκbound := unequal_normalized_signed_index_bound hFp hTlt hm htb
  have hcoeff := unequal_normalized_error_coefficient_bounds (κ:=κ) (P:=P) (Q:=Q)
    (by omega : 1 ≤ t) (by omega : T ≤ 4*t) (by omega : u+1 ≤ 2*t) (le_of_lt htb) hκbound hPbound hQbound
  change |A| ≤ 32*(F : ℤ)*t^2 ∧ |B| ≤ 32*(F : ℤ)*t^2 at hcoeff
  have herr : (F*T : ℕ)*Z-R*(2 : ℤ)^L=A*H+B*c-(F*T : ℕ)+ε*E := by
    have hh := unequal_normalized_signed_rival_error (v:=u+1) hbase hM
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hap)
      (by push_cast; convert hzp using 1; ring) hphase
      (show R=(F : ℤ)*tb*Q-κ*P-(4*F*t : ℕ)*ε by simp only [R,Nat.cast_mul,Nat.cast_ofNat])
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using hh
  have heval : (Z : ZMod N)*x+ta • y+tb • w=V • x := signed_axis_basis_rival_cast_eq x y w κ ν hi hz hα hmx
  have hpA : 2^a=2*s := by rw [hs,← pow_succ']; congr 1; omega
  have hpB : 2^b=2*t := by rw [ht,← pow_succ']; congr 1; omega
  have hcost' : 3*2^(a-1)+t ≤ n+1 := by rwa [← hs]
  have hN0 : (0 : ℤ) ≤ (F : ℤ)*t^2 := by positivity
  have hS0 : (0 : ℤ) < (F*T : ℕ) := by exact_mod_cast (show 0 < F*T by positivity)
  by_cases hRpos : 0 < R
  · have hcomp := unequal_normalized_companion_strict_coin_bound ha (by omega : 2 ≤ b) hD hs ht hDF htu hC hT hm hta htb hdec
    have hoddR : f=0 ∨ Odd R := by
      rcases hoddplan with hh | ⟨_,hh,_⟩
      · exact Or.inl hh
      · exact Or.inr hh
    obtain ⟨v,hv,k,hk,hck,hvgroup⟩ := exists_unequal_uniform_signed_integral_rival
      ha hab hsum hf hn hL hF ht hcost' hTlt (by omega : 0 < T) hH hnc hE hRpos hRint hoddR
      (Or.inl ⟨hRbounds.2.1,hcomp⟩)
      (by linarith only [hcoeff.1,hN0]) (by linarith only [hcoeff.2,hN0])
      (by rcases hε with h | h; exact Or.inl h; exact Or.inr (Or.inr h)) herr x y w heval
    exact ⟨ta,tb,Or.inr (by rw [hpB]; omega),v,hv,k,hk,hck,hvgroup⟩
  · have htaTop : ta < 2*s := hRbounds.2.2 (by omega)
    let ta' := 2*s-1-ta
    let tb' := 2*t-1-tb
    let R' : ℤ := (F*T : ℕ)-R
    let Z' : ℤ := (2 : ℤ)^L-1+V-Z
    have hRlong : R=-4*(F : ℤ)*t+3*(F : ℤ)*u*ta-m+3*(F : ℤ)*tb := by
      rcases hcase with ⟨hP,hQ,he⟩ | ⟨hP,hQ,he⟩
      · have hid := unequal_normalized_short_leading_identity hD hDF htu hC hdec
        have hbd := unequal_normalized_short_leading_bounds hD hs2 hDF htu hu hC hT hta htb hdec hpos
        have heq : R=4*(F : ℤ)*t-(F : ℤ)*u*ta+m-(F : ℤ)*tb := by
          dsimp only [R,κ]
          rw [hP,hQ,he]
          linarith only [hid]
        exfalso
        rw [heq] at hRpos
        exact hRpos hbd.1
      · have hid := unequal_normalized_long_leading_identity hD hDF htu hC hdec
        dsimp only [R,κ]
        rw [hP,hQ,he]
        linarith only [hid]
    have hcostTwo : 2 ≤ gmin (a-1) ta+gmin (b-1) tb := by
      rcases hoddplan with hf0 | ⟨hmOdd,_,_⟩
      · have hFone : F=1 := by rw [hF,hf0,pow_zero]
        have hDs : D=s := by simpa only [hFone,mul_one] using hDF
        apply unequal_largest_integral_long_companion_cost_ge_two hs2 htu hu hC hT
          (by rwa [← hDs]) (by rwa [← hDs]) hpos htaTop htb
        have hh := hRint
        rw [hRlong] at hh
        simpa only [hFone,Nat.cast_one,mul_one,one_mul] using hh
      · exact unequal_integral_long_unit_companion_cost_ge_two hD2 hs2 hDF htu hu hC hT hcopDC
          hmOdd hdec hpos (by rwa [← hRlong])
    have hcomp : gmin (a-1) ta'+gmin (b-1) tb' ≤ a+b-2 := by
      have hca := gmin_top_complement_sum (by omega : 1 ≤ a) (z:=ta) (by rw [hpA]; omega)
      have hcb := gmin_top_complement_sum (by omega : 1 ≤ b) (z:=tb) (by rw [hpB]; omega)
      rw [hpA] at hca
      rw [hpB] at hcb
      dsimp only [ta',tb']
      omega
    have hdist : ta' ≠ 2^a-1 ∨ tb' ≠ 2^b-1 := by
      rw [hpA,hpB]
      dsimp [ta',tb']
      omega
    have heval' : (Z' : ZMod N)*x+ta' • y+tb' • w=V • x := by
      have hh := signed_axis_rival_profile_reflection x y w
        (by omega : ta ≤ 2*s-1) (by omega : tb ≤ 2*t-1) htop heval
      have hp : 1 ≤ 2^L := Nat.one_le_two_pow
      simpa only [Nat.cast_sub hp,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using hh
    have herr' : (F*T : ℕ)*Z'-R'*(2 : ℤ)^L=
        ((F*T : ℕ)-A)*H+((F*T : ℕ)-B)*c-(F*T : ℕ)+(-ε)*E := by
      have hh := signed_axis_rival_top_error_reflection (K:=2^L) hbase
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using herr)
      dsimp only [Z',R']
      simpa only [Nat.cast_pow,Nat.cast_ofNat,neg_mul,sub_eq_add_neg] using hh
    have hAc := (unequal_reflected_error_coefficient_bound (by omega : 1 ≤ t) (by omega : T ≤ 4*t) hcoeff.1).1
    have hBc := (unequal_reflected_error_coefficient_bound (by omega : 1 ≤ t) (by omega : T ≤ 4*t) hcoeff.2).1
    have hintR' : (T : ℤ) ∣ R' := by
      have hsD : (T : ℤ) ∣ (F*T : ℕ) := by push_cast; exact ⟨F,by ring⟩
      exact dvd_sub hsD hRint
    have hoddR' : f=0 ∨ Odd R' := by
      rcases hoddplan with hh | ⟨_,_,hh⟩
      · exact Or.inl hh
      · exact Or.inr hh
    have hRsharp : 2*R' < 5*(F*T : ℕ) := by
      have hlo := unequal_long_unit_numerator_gt_neg_five_half_widths hD hs2 hDF htu hu hC htb hdec
      rw [← hRlong] at hlo
      have hwide := unequal_remaining_three_denominators_ge_ten_half_widths ha hab hsum hs htu hupow hT
      have hmul : 10*(F : ℤ)*t ≤ 3*(F*T : ℕ) := by
        have hh := Nat.mul_le_mul_left F hwide
        exact_mod_cast (show 10*F*t ≤ 3*(F*T) by nlinarith only [hh])
      change 2*((F*T : ℕ)-R) < 5*(F*T : ℕ)
      nlinarith only [hlo,hmul]
    obtain ⟨v,hv,k,hk,hck,hvgroup⟩ := exists_unequal_uniform_signed_integral_rival
      ha hab hsum hf hn hL hF ht hcost' hTlt (by omega : 0 < T) hH hnc hE
      (by change 0 < (F*T : ℕ)-R; linarith only [hRpos,hS0] : 0 < R') hintR' hoddR'
      (Or.inr ⟨hRsharp,hcomp⟩) hAc hBc
      (by rcases hε with h | h <;> rw [h] <;> norm_num) herr' x y w heval'
    exact ⟨ta',tb',hdist,v,hv,k,hk,hck,hvgroup⟩

/-- Every actual integral-unit unequal residual contradicts validity. -/
theorem not_validTuple_of_unequal_integral_primitive_data
    {n N e H c V : ℕ} [NeZero N] (hn : 67 ≤ n)
    {β : Type*} [Fintype β] (hrank : Fintype.card β=3)
    (L : β → ℕ) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (I : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (I ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hlen : L a < L k) (hsum : 10 < L a+L k) (hepos : 1 ≤ e) (he : e < L a)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hindex : N.gcd (x j).val=2^e) (hsub : N < 2^n)
    (hgap : 4*2^(L a-1)*2^(L k-1)*2^(L j) ≤ N+2^(L a-1)*2^(L k-1)*H)
    (hdata : UnequalCompanionIntegralPrimitiveData n N (2^e) (2^(L a-1-e))
      (2^(L a-1)) (2^(L k-1)) (2^(L k-L a)) (4*2^(L k-1)-2^(L k-L a)-1)
      (2^(L j)) H c V (x j) (x a) (x k)) : False := by
  classical
  let D := 2^e
  let F := 2^(L a-1-e)
  let s := 2^(L a-1)
  let t := 2^(L k-1)
  let u := 2^(L k-L a)
  let T := 4*t-u-1
  let M := N/D
  have ha : 2 ≤ L a := by omega
  have hb : 2 ≤ L k := by omega
  have hD : 0 < D := by dsimp [D]; positivity
  have hD2 : 2 ≤ D := Nat.pow_le_pow_right (by decide : 0 < 2) hepos
  have hs : 1 ≤ s := Nat.one_le_two_pow
  have ht : 1 ≤ t := Nat.one_le_two_pow
  have hu : 2 ≤ u := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ L k-L a)
  have hDF : D*F=s := by dsimp [D,F,s]; rw [← pow_add]; congr 1; omega
  have htu : t=s*u := by dsimp [t,s,u]; rw [← pow_add]; congr 1; omega
  have hut : u ≤ t := by nlinarith only [htu,hs]
  have hst : s ≤ t := by nlinarith only [htu,hu]
  have hT : T+u+1=4*t := by dsimp [T]; omega
  have hU : u=2*2^(L k-L a-1) := by dsimp [u]; rw [← pow_succ']; congr 1; omega
  have hTodd : Odd T := by
    refine ⟨2*t-2^(L k-L a-1)-1,?_⟩
    omega
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hrank,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hsize : L j+L a+L k=n := by
    have hh := Fintype.card_congr I
    simp only [Fintype.card_sigma,Fintype.card_fin] at hh
    rw [hset] at hh
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,add_assoc] using hh
  have hpA : 2^(L a)=2*s := by dsimp [s]; rw [← pow_succ']; congr 1; omega
  have hpB : 2^(L k)=2*t := by dsimp [t]; rw [← pow_succ']; congr 1; omega
  have hpow : D*(4*F*t*2^(L j))=2^n := by
    calc
      _ = (2*(D*F))*(2*t)*2^(L j) := by ring
      _ = 2^(L a)*2^(L k)*2^(L j) := by rw [hDF,← hpA,← hpB]
      _ = _ := by rw [← pow_add,← pow_add]; congr 1; omega
  have hDN : D ∣ N := by dsimp [D]; rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hDM : D*M=N := Nat.mul_div_cancel' hDN
  have hMhi : M < 4*F*t*2^(L j) := by
    apply Nat.lt_of_mul_lt_mul_left (a:=D)
    rw [hDM,hpow]
    exact hsub
  let E := 4*F*t*2^(L j)-M
  have hME : M+E=4*F*t*2^(L j) := by dsimp [E]; omega
  have hDE : N+D*E=4*s*t*2^(L j) := by
    rw [← hDM,← Nat.mul_add,hME]
    calc
      _ = 4*(D*F)*t*2^(L j) := by ring
      _ = _ := by rw [hDF]
  have hE : E ≤ F*t*H := by
    apply Nat.le_of_mul_le_mul_left _ hD
    have hmul : D*(F*t*H)=s*t*H := by rw [← Nat.mul_assoc,← Nat.mul_assoc,hDF]
    rw [hmul]
    change 4*s*t*2^(L j) ≤ N+s*t*H at hgap
    omega
  have ho : addOrderOf (x j)=M := by
    have hh := ZMod.addOrderOf_coe (x j).val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hmx : M • x j=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero _
  change UnequalCompanionIntegralPrimitiveData n N D F s t u T (2^(L j)) H c V (x j) (x a) (x k) at hdata
  rcases hdata with ⟨htop,α,z,r,q,hαlo,hzlo,hα,hz,hlink,hres,horient⟩
  have hrF : Nat.Coprime r F := by
    rcases hres with hF | hr
    · rw [hF]; exact Nat.coprime_one_right r
    · exact hr.coprime_two_right.pow_right _
  have htarget : (∑ i, (2^(L i)-1) • x i)=V • x j := by
    have htop' := htop
    rw [← hpA,← hpB] at htop'
    rw [hset]
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,add_assoc] using htop'
  have hclose (P Q ε : ℤ)
      (hcase : (P=(t : ℤ)-1 ∧ Q=3-(u : ℤ) ∧ ε=-1) ∨
        (P=1-3*(t : ℤ) ∧ Q=3*(u : ℤ)-1 ∧ ε=1))
      (hcost : 3*s+t ≤ n+1) (hrT : Nat.Coprime r T)
      (hint : (T : ℤ) ∣ P+4*(F : ℤ)*t*r)
      (hap : (F*T : ℕ)*(α : ℤ)=P*((2 : ℤ)^(L j)-H)+(t : ℤ)*c+(r : ℤ)*M)
      (hzp : (T : ℤ)*z=Q*(2 : ℤ)^(L j)+((T : ℤ)-Q)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*M) : False := by
    obtain ⟨ta,tb,hd,Z,hZ,rep,hrep,hcost',heval⟩ := exists_unequal_normalized_integral_unit_rival
      ha hlen hsum (by omega : L a-1-e ≤ L a-2) hn hsize hD2 rfl rfl rfl hDF htu rfl hu hT hTodd
      hcost hH hnc hbase hME hE hcase hlink (hrF.mul_right hrT) hint hap hzp (x j) (x a) (x k) hα hz hmx htop
    obtain ⟨ua,hua,hca⟩ := exists_rep_gmin (L a-1) ta
    obtain ⟨uk,huk,hck⟩ := exists_rep_gmin (L k-1) tb
    rw [show L a-1+1=L a by omega] at hua hca
    rw [show L k-1+1=L k by omega] at huk hck
    exact not_validTuple_of_three_axis_representations hrank L g I x b hchain j a k haj hkj hka
      Z ta tb rep ua uk hrep hua huk (by rw [hca,hck]; exact hcost')
      (by omega) hd (heval.trans htarget.symm) hg
  rcases horient with ⟨hcost,_,_,_,hap,hzp,_,_,hrT,hint⟩ | ⟨hcost,_,_,_,_,hap,hzp,hrT,hint⟩
  · apply hclose ((t : ℤ)-1) (3-(u : ℤ)) (-1) (Or.inl ⟨rfl,rfl,rfl⟩) (by omega) hrT hint
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hap)
    simp only [Nat.cast_pow,Nat.cast_ofNat] at hzp
    convert hzp using 1; ring
  · apply hclose (1-3*(t : ℤ)) (3*(u : ℤ)-1) 1 (Or.inr ⟨rfl,rfl,rfl⟩) (by omega) hrT hint
    · simp only [Nat.cast_pow,Nat.cast_ofNat] at hap
      convert hap using 1; ring
    · simp only [Nat.cast_pow,Nat.cast_ofNat] at hzp
      convert hzp using 1; ring

/-- The sharp global bound holds for every unequal companion pair with
a maximal even axis, with no restriction on its actual index or phase. -/
theorem even_axis_unequal_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hlen : L a < L k) (hmax : ∀ i, L i ≤ L j)
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) :
    globalBound n ≤ N := by
  classical
  by_cases hsmall : L a+L k ≤ 10
  · exact even_axis_companion_length_sum_le_ten_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka hsmall hj hother v hv hvz
  have hsum : 10 < L a+L k := by omega
  by_contra hh
  have hsub : N < globalBound n := by omega
  obtain ⟨e,h,d,hepos,he,hindex,hnc,hbase,hgap,_,hdata,_,_⟩ :=
    even_axis_subglobal_maximal_unequal_companion_integral_unit_data hn hN hr L hL
      g hg E x b hchain hgen j a k haj hkj hka hlen hmax hj hother v hv hvz hsub
  exact not_validTuple_of_unequal_integral_primitive_data hn hr L g hg E x b hchain j a k haj hkj hka
    hlen hsum hepos he Nat.one_le_two_pow hnc hbase hindex
    (lt_of_lt_of_le hsub (Nat.sub_le _ _)) hgap hdata

/-- Equal and unequal companions both satisfy the sharp global bound
when the unique even collision axis is maximal. -/
theorem even_axis_maximal_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hmax : ∀ i, L i ≤ L j)
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) :
    globalBound n ≤ N := by
  rcases lt_trichotomy (L a) (L k) with hlt | heq | hgt
  · exact even_axis_unequal_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka hlt hmax hj hother v hv hvz
  · exact even_axis_equal_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka heq hmax hj hother v hv hvz
  · exact even_axis_unequal_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j k a hkj haj hka.symm hgt hmax hj hother v hv hvz

end MinModulus
