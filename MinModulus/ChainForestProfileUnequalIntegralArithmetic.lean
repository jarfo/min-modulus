import MinModulus.ChainForestProfileUnequalNonunit

/-! Uniform integral-boundary arithmetic for unequal unit phases. Normalized
companions save one coin and integral top reflections save two. A sharper
reflected numerator bound and doubled dyadic prefixes cover both error signs
at every factor, including factor one. These bounds yield actual signed
integral rivals; the genuine global consumer is in UnequalIntegral. -/

namespace MinModulus

/-- Staying below three half-widths avoids the unique extra-coin endpoint. -/
theorem gmin_below_three_half_widths {a s z : ℕ}
    (ha : 2 ≤ a) (hs : s=2^(a-1)) (hz : z < 3*s-1) :
    gmin (a-1) z ≤ a := by
  have hp : 2^a=2*s := by rw [hs,← pow_succ']; congr 1; omega
  by_cases hh : z < 2*s
  · have hc := gmin_le_of_lt_binary_width (w:=a-1) (t:=z) (by rw [Nat.sub_add_cancel (by omega : 1 ≤ a),hp]; exact hh)
    omega
  · have htail : z-2*s < 2^(a-1)-1 := by rw [← hs]; omega
    have hc := gmin_binary_low_lt_ones (by omega : 1 ≤ a-1) htail
    have he : z=(z-2*s)+s+s := by omega
    rw [he,hs,gmin_add_pow,gmin_add_pow]
    rw [hs] at hc
    omega

/-- Every normalized multiplier below the full denominator saves one
companion coin. At the long all-ones endpoint the short weight drops below
three half-widths; elsewhere the long weight itself saves a coin. -/
theorem unequal_normalized_companion_strict_coin_bound
    {a b D F s t u C T m ta tb : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hD : 0 < D) (hs : s=2^(a-1)) (ht : t=2^(b-1))
    (hDF : D*F=s) (htu : t=s*u) (hC : C+1=4*s) (hT : T+u+1=4*t)
    (hm : m < F*T) (hta : ta < C) (htb : tb < t) (hdecomp : ta+C*tb=D*m) :
    gmin (a-1) ta+gmin (b-1) tb ≤ a+b-1 := by
  have htp : 1 ≤ t := by rw [ht]; exact Nat.one_le_two_pow
  have hCT : s*T+s=C*t := by
    have hh := congrArg (fun z : ℕ ↦ s*z) hT
    have hc := congrArg (fun z : ℕ ↦ z*t) hC
    nlinarith only [hh,hc,htu]
  have hmul := Nat.mul_lt_mul_of_pos_left hm hD
  rw [← Nat.mul_assoc,hDF] at hmul
  by_cases htop : tb=t-1
  · have hsub : C*(t-1)+C=C*t := by
      have hh := congrArg (fun v : ℕ ↦ C*v) (Nat.sub_add_cancel htp)
      simpa only [Nat.mul_add,Nat.mul_one] using hh
    have hsmall : ta < 3*s-1 := by
      rw [htop] at hdecomp
      omega
    have hca := gmin_below_three_half_widths ha hs hsmall
    have hcb := gmin_binary_low_le (e:=b-1) (r:=tb) (by rwa [← ht])
    omega
  · have hca := gmin_normalized_short_weight_bound (by omega : 1 ≤ a) hs (by omega : ta < 4*s-1)
    have hcb := gmin_binary_low_lt_ones (e:=b-1) (r:=tb) (by omega) (by rw [← ht]; omega)
    omega

/-- Greedy binary cost vanishes exactly at zero. -/
theorem gmin_eq_zero_iff (w z : ℕ) : gmin w z=0 ↔ z=0 := by
  induction w generalizing z with
  | zero => simp [gmin]
  | succ w ih =>
    simp only [gmin,Nat.add_eq_zero_iff,ih]
    omega

/-- A greedy representation of cost one is a single available power of two. -/
theorem exists_pow_of_gmin_eq_one {w z : ℕ} (hg : gmin w z=1) :
    ∃ i ≤ w, z=2^i := by
  induction w generalizing z with
  | zero => exact ⟨0,by omega,by simpa only [gmin,pow_zero] using hg⟩
  | succ w ih =>
    simp only [gmin] at hg
    have hm := Nat.mod_lt z (by decide : 0 < 2)
    have hd := Nat.mod_add_div z 2
    by_cases hmod : z%2=0
    · have hh : gmin w (z/2)=1 := by omega
      obtain ⟨i,hi,he⟩ := ih hh
      exact ⟨i+1,by omega,by rw [pow_succ]; omega⟩
    · have hh : gmin w (z/2)=0 := by omega
      have hz : z/2=0 := (gmin_eq_zero_iff w _).mp hh
      exact ⟨0,by omega,by rw [pow_zero]; omega⟩

/-- Complementary weights inside an original top have exactly its full
binary coin total. -/
theorem gmin_top_complement_sum {a z : ℕ} (ha : 1 ≤ a) (hz : z ≤ 2^a-1) :
    gmin (a-1) z+gmin (a-1) (2^a-1-z)=a := by
  have hp : 2^a=2*2^(a-1) := by rw [← pow_succ']; congr 1; omega
  have hpp : 1 ≤ 2^a := Nat.one_le_two_pow
  have he : z+(2^a-1-z)+1=2*2^(a-1) := by omega
  have hh := gmin_pair_of_sum_add_one_eq_top_multiple (a-1) z (2^a-1-z) 2 he
  omega

/-- An odd divisor of a power of two is one. -/
theorem odd_divisor_two_pow_eq_one {m i : ℕ} (hm : Odd m) (hd : m ∣ 2^i) : m=1 := by
  have hh : m ∣ Nat.gcd m (2^i) := Nat.dvd_gcd (dvd_refl m) hd
  rw [(hm.coprime_two_right.pow_right i).gcd_eq_one] at hh
  exact Nat.dvd_one.mp hh

/-- A normalized odd multiplier with total companion cost one has only
the two possible single-index companion weights. -/
theorem normalized_odd_multiplier_one_coin_classification
    {wa wb D C m ta tb : ℕ} (hD : 0 < D) (hcop : Nat.Coprime D C)
    (hm : Odd m) (hdecomp : ta+C*tb=D*m) (hpos : 0 < ta+tb)
    (hcost : gmin wa ta+gmin wb tb ≤ 1) :
    (ta=D ∧ tb=0) ∨ (ta=0 ∧ tb=D) := by
  by_cases hta : ta=0
  · have htb : tb ≠ 0 := by omega
    have hgb : gmin wb tb=1 := by
      have ha0 := (gmin_eq_zero_iff wa ta).mpr hta
      have hb0 : gmin wb tb ≠ 0 := by intro hh; exact htb ((gmin_eq_zero_iff wb tb).mp hh)
      omega
    obtain ⟨i,_,hpow⟩ := exists_pow_of_gmin_eq_one hgb
    have hDtb : D ∣ tb := by
      apply hcop.dvd_of_dvd_mul_left
      have he : C*tb=D*m := by simpa only [hta,zero_add] using hdecomp
      rw [he]
      exact dvd_mul_right D m
    obtain ⟨b0,hb0⟩ := hDtb
    have hmeq : m=C*b0 := by rw [hta,hb0] at hdecomp; nlinarith only [hdecomp,hD]
    have hodd : Odd b0 := by rw [hmeq] at hm; exact (Nat.odd_mul.mp hm).2
    have hbdiv : b0 ∣ 2^i := by rw [← hpow,hb0]; exact dvd_mul_left b0 D
    have hbone := odd_divisor_two_pow_eq_one hodd hbdiv
    exact Or.inr ⟨hta,by rw [hb0,hbone,mul_one]⟩
  · have hga0 : gmin wa ta ≠ 0 := by intro hh; exact hta ((gmin_eq_zero_iff wa ta).mp hh)
    have hgb : gmin wb tb=0 := by omega
    have htb := (gmin_eq_zero_iff wb tb).mp hgb
    have hga : gmin wa ta=1 := by omega
    obtain ⟨i,_,hpow⟩ := exists_pow_of_gmin_eq_one hga
    have he : ta=D*m := by simpa only [htb,mul_zero,add_zero] using hdecomp
    have hmdiv : m ∣ 2^i := by rw [← hpow,he]; exact dvd_mul_left m D
    have hmone := odd_divisor_two_pow_eq_one hm hmdiv
    exact Or.inl ⟨by rw [he,hmone,mul_one],htb⟩

/-- Remaining unequal lengths make three primitive denominators wider
than ten long half-widths. -/
theorem unequal_remaining_three_denominators_ge_ten_half_widths
    {a b s t u T : ℕ} (ha : 2 ≤ a) (hab : a < b) (hsum : 10 < a+b)
    (hs : s=2^(a-1)) (htu : t=s*u) (hu : u=2^(b-a)) (hT : T+u+1=4*t) :
    10*t ≤ 3*T := by
  have hs2 : 2 ≤ s := by rw [hs]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ a-1)
  have hu2 : 2 ≤ u := by rw [hu]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ b-a)
  have hmargin : 3*u+3 ≤ 2*t := by
    by_cases ha2 : a=2
    · have hsval : s=2 := by rw [ha2] at hs; norm_num at hs; exact hs
      have hu4 : 4 ≤ u := by rw [hu]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ b-a)
      nlinarith only [htu,hsval,hu4]
    · have hs4 : 4 ≤ s := by rw [hs]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ a-1)
      have hh := Nat.mul_le_mul_right u hs4
      nlinarith only [hh,htu,hu2]
  omega

/-- The long unit numerator is strictly above minus five long period
half-widths, using the exact normalized remainder relation. -/
theorem unequal_long_unit_numerator_gt_neg_five_half_widths
    {D F s t u C m ta tb : ℕ} (hD : 0 < D) (hs : 2 ≤ s)
    (hDF : D*F=s) (htu : t=s*u) (hu : 2 ≤ u) (hC : C+1=4*s)
    (htb : tb < t) (hdecomp : ta+C*tb=D*m) :
    -5*(F : ℤ)*t < -4*(F : ℤ)*t+3*(F : ℤ)*u*ta-m+3*(F : ℤ)*tb := by
  have hDZ : (0 : ℤ) < D := by exact_mod_cast hD
  have hsZ : (2 : ℤ) ≤ s := by exact_mod_cast hs
  have huZ : (2 : ℤ) ≤ u := by exact_mod_cast hu
  have hDFZ : (D : ℤ)*F=s := by exact_mod_cast hDF
  have htuZ : (t : ℤ)=(s : ℤ)*u := by exact_mod_cast htu
  have hCZ : (C : ℤ)+1=4*s := by exact_mod_cast hC
  have hdec : (ta : ℤ)+(C : ℤ)*tb=(D : ℤ)*m := by exact_mod_cast hdecomp
  have htZ : (0 : ℤ) < t := by
    have hh := mul_pos (show (0 : ℤ) < s by omega) (show (0 : ℤ) < u by omega)
    rwa [← htuZ] at hh
  have htbZ : (tb : ℤ) < t := by exact_mod_cast htb
  have heq : (D : ℤ)*(-4*(F : ℤ)*t+3*(F : ℤ)*u*ta-m+3*(F : ℤ)*tb)=
      -4*(s : ℤ)*t+(3*(t : ℤ)-1)*ta-((s : ℤ)-1)*tb := by
    linear_combination (-4*(t : ℤ)+3*(u : ℤ)*ta+3*(tb : ℤ))*hDFZ+
      hdec-(tb : ℤ)*hCZ-3*(ta : ℤ)*htuZ
  apply (mul_lt_mul_iff_right₀ hDZ).mp
  rw [heq]
  have heq' : (D : ℤ)*(-5*(F : ℤ)*t)=-5*(s : ℤ)*t := by linear_combination -5*(t : ℤ)*hDFZ
  rw [heq']
  have hlow : (0 : ℤ) ≤ (3*(t : ℤ)-1)*ta := mul_nonneg (by omega) (by positivity)
  have htail := mul_lt_mul_of_pos_left htbZ (show 0 < (s : ℤ)-1 by omega)
  nlinarith only [hlow,htail,htZ]

/-- An integral long unit step cannot consist of a single companion coin.
The two possible single-index plans have a nonzero residue below `T`. -/
theorem unequal_integral_long_unit_companion_cost_ge_two
    {wa wb D F s t u C T m ta tb : ℕ}
    (hD : 2 ≤ D) (hs : 2 ≤ s) (hDF : D*F=s) (htu : t=s*u) (hu : 2 ≤ u)
    (hC : C+1=4*s) (hT : T+u+1=4*t) (hcop : Nat.Coprime D C)
    (hm : Odd m) (hdecomp : ta+C*tb=D*m) (hpos : 0 < ta+tb)
    (hint : (T : ℤ) ∣ -4*(F : ℤ)*t+3*(F : ℤ)*u*ta-m+3*(F : ℤ)*tb) :
    2 ≤ gmin wa ta+gmin wb tb := by
  have hDp : 0 < D := by omega
  have hFp : 0 < F := by nlinarith only [hDF,hs]
  have hFZ : (0 : ℤ) < F := by exact_mod_cast hFp
  have hsZ : (2 : ℤ) ≤ s := by exact_mod_cast hs
  have huZ : (2 : ℤ) ≤ u := by exact_mod_cast hu
  have hDFZ : (D : ℤ)*F=s := by exact_mod_cast hDF
  have htuZ : (t : ℤ)=(s : ℤ)*u := by exact_mod_cast htu
  have hCZ : (C : ℤ)+1=4*s := by exact_mod_cast hC
  have hTZ : (T : ℤ)+u+1=4*t := by exact_mod_cast hT
  have hFle : (F : ℤ) ≤ s := by
    have hh := Nat.mul_le_mul_right F hD
    exact_mod_cast (show F ≤ s by nlinarith only [hh,hDF])
  have h2s : 2*(s : ℤ) ≤ t := by
    have hh := Nat.mul_le_mul_left s hu
    exact_mod_cast (show 2*s ≤ t by nlinarith only [hh,htu])
  have hFu : 2*(F : ℤ)*u ≤ t := by
    have hh : 2*F ≤ s := by nlinarith only [Nat.mul_le_mul_right F hD,hDF]
    have hh' := Nat.mul_le_mul_right u hh
    exact_mod_cast (show 2*F*u ≤ t by nlinarith only [hh',htu])
  have hUtp : (u : ℤ)+1 ≤ t := by
    have hh := mul_nonneg (show 0 ≤ (s : ℤ)-2 by omega) (show (0 : ℤ) ≤ u by positivity)
    nlinarith only [hh,htuZ,huZ]
  have h3t : 3*(t : ℤ) ≤ T := by omega
  have htZ : (0 : ℤ) < t := by omega
  have hFu0 : (0 : ℤ) ≤ (F : ℤ)*u := by positivity
  have hDFu : (F : ℤ)*u*D=t := by linear_combination (u : ℤ)*hDFZ-htuZ
  have hSTdiv : (T : ℤ) ∣ (F*T : ℕ) := by push_cast; exact ⟨F,by ring⟩
  by_contra hh
  obtain h | h := normalized_odd_multiplier_one_coin_classification hDp hcop hm hdecomp hpos (by omega : gmin wa ta+gmin wb tb ≤ 1)
  · rcases h with ⟨hta,htb⟩
    subst ta
    subst tb
    have hmone : m=1 := by simp only [mul_zero,add_zero] at hdecomp; nlinarith only [hdecomp,hDp]
    subst m
    simp only [Nat.cast_zero,Nat.cast_one,mul_zero,add_zero] at hint
    have heq : (-4*(F : ℤ)*t+3*(F : ℤ)*u*D-1)+(F*T : ℕ)=3*(t : ℤ)-(F : ℤ)*u-F-1 := by
      push_cast
      linear_combination 3*hDFu+(F : ℤ)*hTZ
    have hd : (T : ℤ) ∣ 3*(t : ℤ)-(F : ℤ)*u-F-1 := by
      have hh := dvd_add hint hSTdiv
      rwa [heq] at hh
    have hlow : (0 : ℤ) < 3*(t : ℤ)-(F : ℤ)*u-F-1 := by
      nlinarith only [hFu,hFle,h2s,htZ]
    have hhi : 3*(t : ℤ)-(F : ℤ)*u-F-1 < T := by
      nlinarith only [hFu0,hFZ,h3t]
    exact (not_le_of_gt hhi) (Int.le_of_dvd hlow hd)
  · rcases h with ⟨hta,htb⟩
    subst ta
    subst tb
    have hmC : m=C := by simp only [zero_add] at hdecomp; nlinarith only [hdecomp,hDp]
    subst m
    simp only [Nat.cast_zero,mul_zero,add_zero] at hint
    have heq : (-4*(F : ℤ)*t-C+3*(F : ℤ)*D)+(F*T : ℕ)=-((F : ℤ)*u+F+s-1) := by
      push_cast
      linear_combination 3*hDFZ-hCZ+(F : ℤ)*hTZ
    have hd : (T : ℤ) ∣ (F : ℤ)*u+F+s-1 := by
      have hh := dvd_add hint hSTdiv
      rw [heq,dvd_neg] at hh
      exact hh
    have hlow : (0 : ℤ) < (F : ℤ)*u+F+s-1 := by nlinarith only [hFu0,hFZ,hsZ]
    have hhi : (F : ℤ)*u+F+s-1 < T := by nlinarith only [hFu,hFle,h2s,h3t,htZ]
    exact (not_le_of_gt hhi) (Int.le_of_dvd hlow hd)

/-- At the largest index, an integral reflected long plan has two
positive companion weights, even when its primitive multiplier is even. -/
theorem unequal_largest_integral_long_companion_cost_ge_two
    {wa wb s t u C T m ta tb : ℕ}
    (hs : 2 ≤ s) (htu : t=s*u) (hu : 2 ≤ u) (hC : C+1=4*s) (hT : T+u+1=4*t)
    (hcop : Nat.Coprime s C) (hdecomp : ta+C*tb=s*m) (hpos : 0 < ta+tb)
    (hta : ta < 2*s) (htb : tb < t)
    (hint : (T : ℤ) ∣ -4*(t : ℤ)+3*(u : ℤ)*ta-m+3*(tb : ℤ)) :
    2 ≤ gmin wa ta+gmin wb tb := by
  have hsp : 0 < s := by omega
  have hsZ : (2 : ℤ) ≤ s := by exact_mod_cast hs
  have huZ : (2 : ℤ) ≤ u := by exact_mod_cast hu
  have htuZ : (t : ℤ)=(s : ℤ)*u := by exact_mod_cast htu
  have hCZ : (C : ℤ)+1=4*s := by exact_mod_cast hC
  have hTZ : (T : ℤ)+u+1=4*t := by exact_mod_cast hT
  have hut : (u : ℤ)+1 < t := by
    have hh := mul_nonneg (show 0 ≤ (s : ℤ)-2 by omega) (show (0 : ℤ) ≤ u by positivity)
    nlinarith only [hh,htuZ,huZ]
  have hTpos : (0 : ℤ) < T := by omega
  have htaNZ : ta ≠ 0 := by
    intro hzero
    have hstb : s ∣ tb := by
      apply hcop.dvd_of_dvd_mul_left
      have he : C*tb=s*m := by simpa only [hzero,zero_add] using hdecomp
      rw [he]
      exact dvd_mul_right s m
    obtain ⟨v,hv⟩ := hstb
    have hvpos : 0 < v := by nlinarith only [hpos,hzero,hv]
    have hvu : v < u := by rw [hv,htu] at htb; exact Nat.lt_of_mul_lt_mul_left htb
    have hmeq : m=C*v := by rw [hzero,hv] at hdecomp; nlinarith only [hdecomp,hsp]
    have hvZ : (1 : ℤ) ≤ v := by exact_mod_cast (show 1 ≤ v by omega)
    have hvuZ : (v : ℤ) < u := by exact_mod_cast hvu
    have hvCast : (tb : ℤ)=(s : ℤ)*v := by exact_mod_cast hv
    have hmCast : (m : ℤ)=(C : ℤ)*v := by exact_mod_cast hmeq
    have heq : (-4*(t : ℤ)+3*(u : ℤ)*ta-m+3*(tb : ℤ))+2*(T : ℤ)=
        4*(t : ℤ)-2*u-2-((s : ℤ)-1)*v := by
      rw [hzero,Nat.cast_zero,mul_zero,add_zero,hvCast,hmCast]
      linear_combination 2*hTZ-(v : ℤ)*hCZ
    have hd : (T : ℤ) ∣ 4*(t : ℤ)-2*u-2-((s : ℤ)-1)*v := by
      have hh := dvd_add hint (show (T : ℤ) ∣ 2*(T : ℤ) from dvd_mul_left _ _)
      rwa [heq] at hh
    have hlow : (0 : ℤ) < 4*(t : ℤ)-2*u-2-((s : ℤ)-1)*v := by
      have hh := mul_lt_mul_of_pos_left hvuZ (show 0 < (s : ℤ)-1 by omega)
      nlinarith only [hh,htuZ,hut,huZ]
    have hhi : 4*(t : ℤ)-2*u-2-((s : ℤ)-1)*v < T := by
      have hh := mul_pos (show 0 < (s : ℤ)-1 by omega) (show (0 : ℤ) < v by omega)
      nlinarith only [hh,hTZ,huZ]
    exact (not_le_of_gt hhi) (Int.le_of_dvd hlow hd)
  have htbNZ : tb ≠ 0 := by
    intro hzero
    have he : ta=s*m := by simpa only [hzero,mul_zero,add_zero] using hdecomp
    have hmone : m=1 := by nlinarith only [he,hta,hpos,hzero,hsp]
    have htas : ta=s := by rw [he,hmone,mul_one]
    have heq : (-4*(t : ℤ)+3*(u : ℤ)*ta-m+3*(tb : ℤ))+(T : ℤ)=3*(t : ℤ)-u-2 := by
      rw [hzero,htas,hmone,Nat.cast_zero,Nat.cast_one,mul_zero,add_zero]
      linear_combination -3*htuZ+hTZ
    have hd : (T : ℤ) ∣ 3*(t : ℤ)-u-2 := by
      have hh := dvd_add hint (dvd_refl (T : ℤ))
      rwa [heq] at hh
    have hlow : (0 : ℤ) < 3*(t : ℤ)-u-2 := by omega
    have hhi : 3*(t : ℤ)-u-2 < T := by omega
    exact (not_le_of_gt hhi) (Int.le_of_dvd hlow hd)
  have hga : gmin wa ta ≠ 0 := fun hh ↦ htaNZ ((gmin_eq_zero_iff wa ta).mp hh)
  have hgb : gmin wb tb ≠ 0 := fun hh ↦ htbNZ ((gmin_eq_zero_iff wb tb).mp hh)
  omega

/-- Doubled direct integral boundaries have a lower-prefix budget that
also works at the largest index, without an oddness hypothesis there. -/
theorem unequal_direct_integral_doubled_prefix_bounds {f k : ℕ}
    (hkpos : 1 ≤ k) (hodd : f=0 ∨ Odd k) (hk : k < 2*2^f) :
    gmin f (2*k-1) ≤ f+2 ∧ gmin f (2*k) ≤ f+4 := by
  have hq : (2*k)/2^f < 4 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by omega)
  have hc := gmin_le_top_quotient_add_width f (2*k)
  refine ⟨?_,by omega⟩
  rcases hodd with rfl | hodd
  · norm_num [gmin] at hk ⊢
    omega
  · by_cases hf : f=0
    · subst f; norm_num [gmin] at hk ⊢; omega
    have hp := (odd_dyadic_boundary_prefix_coin_bounds (by omega : 1 ≤ f) hodd hk).1
    have hmod : (2*k-1)%2=1 := by omega
    have hdiv : (2*k-1)/2=k-1 := by omega
    rw [show f=(f-1)+1 by omega,gmin,hmod,hdiv]
    omega

/-- Doubled reflected integral boundaries below five half-widths save
the two required low-prefix coins, including the largest-index case. -/
theorem unequal_reflected_integral_doubled_prefix_bounds {f k : ℕ}
    (hkpos : 1 ≤ k) (hodd : f=0 ∨ Odd k) (hk : 2*k < 5*2^f) :
    gmin f (2*k-1) ≤ f+3 ∧ gmin f (2*k) ≤ f+4 := by
  have hq : (2*k)/2^f < 5 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by omega)
  have hc := gmin_le_top_quotient_add_width f (2*k)
  refine ⟨?_,by omega⟩
  by_cases hf : f=0
  · subst f; norm_num [gmin] at hk ⊢; omega
  have hodd' : Odd k := hodd.resolve_left hf
  have hlo : gmin (f-1) (k-1) ≤ f+2 := by
    by_cases hf1 : f=1
    · subst f; norm_num [gmin] at hk ⊢; omega
    obtain ⟨j,hj⟩ := hodd'
    have hmod : (k-1)%2=0 := by omega
    have hp : 2^f=4*2^(f-2) := by rw [show f=2+(f-2) by omega,pow_add]; norm_num
    have hq' : ((k-1)/2)/2^(f-2) < 5 :=
      (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by rw [hp] at hk; omega)
    have hc' := gmin_le_top_quotient_add_width (f-2) ((k-1)/2)
    rw [show f-1=(f-2)+1 by omega,gmin,hmod,zero_add]
    omega
  have hmod : (2*k-1)%2=1 := by omega
  have hdiv : (2*k-1)/2=k-1 := by omega
  rw [show f=(f-1)+1 by omega,gmin,hmod,hdiv]
  omega

/-- Four reserved blocks also pay for integral boundaries and their
short positive-error tails. -/
theorem unequal_uniform_integral_axis_budget
    {a b f n L F t : ℕ}
    (ha : 2 ≤ a) (hab : a < b) (hsum : 10 < a+b) (hf : f ≤ a-2) (hn : 67 ≤ n)
    (hL : L+a+b=n) (hF : F=2^f) (ht : t=2^(b-1))
    (hcost : 3*2^(a-1)+t ≤ n+1) :
    f+1 ≤ 4*(b+f+1) ∧ 4*(b+f+1) ≤ L ∧
    (128*F*t^2)*n < 2^(L-4*(b+f+1)) ∧
    f+4+(L-4*(b+f+1))+(a+b) ≤ n := by
  have hFp : 0 < F := by rw [hF]; positivity
  have htp : 0 < t := by rw [ht]; positivity
  have hUpos : 0 < 128*F*t^2 := by positivity
  have hsmall : (128*F*t^2)*n < 2^(n-(a+b+4*(b+f+1))) := by
    rw [hF,ht]
    exact unequal_uniform_four_block_error_bound ha hab hsum hf hn (by simpa only [ht] using hcost)
  have hres : a+b+4*(b+f+1) ≤ n := by
    by_contra hh
    rw [show n-(a+b+4*(b+f+1))=0 by omega,pow_zero] at hsmall
    have hm := Nat.mul_le_mul_right n (show 1 ≤ 128*F*t^2 by omega)
    omega
  exact ⟨by omega,by omega,by rwa [show L-4*(b+f+1)=n-(a+b+4*(b+f+1)) by omega],by omega⟩

/-- A positive integral multiplier can only enlarge an absolute error. -/
theorem int_error_window_of_positive_multiplier {S : ℕ} {δ C : ℤ}
    (hS : 0 < S) (hlo : -C < (S : ℤ)*δ) (hhi : (S : ℤ)*δ < C) :
    -C < δ ∧ δ < C := by
  have hS1 : (1 : ℤ) ≤ S := by exact_mod_cast hS
  have hh : |δ| ≤ |(S : ℤ)*δ| := by
    rw [abs_mul,abs_of_nonneg (by positivity : (0 : ℤ) ≤ S)]
    have hm := mul_le_mul_of_nonneg_right hS1 (abs_nonneg δ)
    simpa only [one_mul] using hm
  exact abs_lt.mp (lt_of_le_of_lt hh (abs_lt.mpr ⟨hlo,hhi⟩))

/-- An integral dyadic boundary gives an affordable axis representation
on either side when the lower prefix and the short upper tail have budgets.
The doubled numerator handles factor one with the same representation. -/
theorem exists_rep_near_doubled_integral_boundary
    {n L f bits U m companions : ℕ} {Z : ℤ}
    (hm : 2 ≤ m) (hU : 1 ≤ U) (hshift : f+1 ≤ bits) (hbits : bits ≤ L)
    (hsmall : U*n < 2^(L-bits))
    (hbelow : gmin f (m-1)+(L-(f+1))+companions ≤ n)
    (habove : gmin f m+(L-bits)+companions ≤ n)
    (hlo : -((U*n : ℕ) : ℤ) < Z-(m : ℤ)*2^(L-(f+1)))
    (hhi : Z-(m : ℤ)*2^(L-(f+1)) < (U*n : ℕ)) :
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ k, val L k=Z.toNat ∧ dsum L k+companions ≤ n := by
  have hlen : L-(f+1)+(f+1)=L := by omega
  have hwide : 2^(L-bits) ≤ 2^(L-(f+1)) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have htailn : n ≤ 2^(L-bits) := by
    have hh := Nat.mul_le_mul_right n hU
    omega
  have hpZ : ((U*n : ℕ) : ℤ) < (2 : ℤ)^(L-(f+1)) := by exact_mod_cast (lt_of_lt_of_le hsmall hwide)
  have hnZ : (n : ℤ) ≤ (2 : ℤ)^(L-(f+1)) := by exact_mod_cast (le_trans htailn hwide)
  have hmZ : (2 : ℤ) ≤ m := by exact_mod_cast hm
  have hp0 : (0 : ℤ) < 2^(L-(f+1)) := by positivity
  have hmP := mul_le_mul_of_nonneg_right hmZ (le_of_lt hp0)
  have hZlo : (n : ℤ) ≤ Z := by nlinarith only [hlo,hpZ,hmP,hnZ]
  have hZ0 : 0 ≤ Z := le_trans (by positivity) hZlo
  have hZcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hZ0
  have hnNat : n ≤ Z.toNat := by exact_mod_cast (show (n : ℤ) ≤ (Z.toNat : ℤ) by rwa [hZcast])
  refine ⟨hZ0,hnNat,?_⟩
  by_cases hlow : Z.toNat < m*2^(L-(f+1))
  · have hlowZ : ((m-1 : ℕ) : ℤ)*2^(L-(f+1)) ≤ Z.toNat := by
      rw [Nat.cast_sub (by omega : 1 ≤ m),Nat.cast_one,hZcast]
      nlinarith only [hlo,hpZ]
    have hstart : (m-1)*2^(L-(f+1)) ≤ Z.toNat := by exact_mod_cast hlowZ
    let tail := Z.toNat-(m-1)*2^(L-(f+1))
    have heq : (m-1)*2^(L-(f+1))+tail=Z.toNat := Nat.add_sub_of_le hstart
    have hprod : (m-1)*2^(L-(f+1))+2^(L-(f+1))=m*2^(L-(f+1)) := by
      have hh := congrArg (fun t : ℕ ↦ t*2^(L-(f+1))) (Nat.sub_add_cancel (by omega : 1 ≤ m))
      nlinarith only [hh]
    have htail : tail < 2^(L-(f+1)) := by omega
    obtain ⟨k,hk,hkc⟩ := exists_rep_binary_block_tail f (L-(f+1)) (m-1) tail htail
    rw [hlen,heq] at hk
    rw [hlen] at hkc
    exact ⟨k,hk,by omega⟩
  · have hstart : m*2^(L-(f+1)) ≤ Z.toNat := by omega
    let tail := Z.toNat-m*2^(L-(f+1))
    have heq : m*2^(L-(f+1))+tail=Z.toNat := Nat.add_sub_of_le hstart
    have heqZ : (m : ℤ)*2^(L-(f+1))+(tail : ℤ)=Z := by
      have hh : (m : ℤ)*2^(L-(f+1))+(tail : ℤ)=(Z.toNat : ℤ) := by exact_mod_cast heq
      rwa [hZcast] at hh
    have htailU : tail < U*n := by
      have hh : (tail : ℤ) < (U*n : ℕ) := by linarith only [heqZ,hhi]
      exact_mod_cast hh
    obtain ⟨k,hk,hkc⟩ := exists_rep_binary_block_bounded_tail f (L-(f+1)) (L-bits) m tail
      (by omega) (lt_trans htailU hsmall)
    rw [hlen,heq] at hk
    rw [hlen] at hkc
    exact ⟨k,hk,by omega⟩

/-- Integral unit phases produce integral normalized numerators, with
no cancellation of the actual period quotient. -/
theorem unequal_normalized_integral_unit_leading_dvd
    {F T t m tb r : ℕ} {P Q κ R l ε : ℤ}
    (hm : (m : ℤ)*r=(F*T : ℕ)*l+ε)
    (hκ : κ=(m : ℤ)-4*(F : ℤ)*tb)
    (hR : R=(F : ℤ)*tb*Q-κ*P-4*(F : ℤ)*t*ε)
    (hcancel : (T : ℤ) ∣ (F : ℤ)*tb*(Q+4*P))
    (hint : (T : ℤ) ∣ P+4*(F : ℤ)*t*r) : (T : ℤ) ∣ R := by
  have hprod := dvd_mul_of_dvd_right hint (m : ℤ)
  have hbase : (T : ℤ) ∣ 4*(F : ℤ)*t*(F*T : ℕ)*l := by
    refine ⟨4*(F : ℤ)*t*F*l,?_⟩
    push_cast
    ring
  have hmul : (T : ℤ) ∣ (m : ℤ)*P+4*(F : ℤ)*t*ε := by
    have hh := dvd_sub hprod hbase
    have heq : (m : ℤ)*(P+4*(F : ℤ)*t*r)-4*(F : ℤ)*t*(F*T : ℕ)*l=
        (m : ℤ)*P+4*(F : ℤ)*t*ε := by
      linear_combination 4*(F : ℤ)*t*hm
    rwa [heq] at hh
  have hh := dvd_sub hcancel hmul
  have heq : (F : ℤ)*tb*(Q+4*P)-((m : ℤ)*P+4*(F : ℤ)*t*ε)=R := by
    rw [hR,hκ]
    ring
  rwa [heq] at hh

/-- Below factor one, either signed unit phase forces an odd multiplier. -/
theorem odd_multiplier_of_even_factor_signed_unit_phase
    {F T m r : ℕ} {l ε : ℤ} (hF : 2 ∣ F) (hε : ε=-1 ∨ ε=1)
    (hm : (m : ℤ)*r=(F*T : ℕ)*l+ε) : Odd m := by
  by_contra hh
  obtain ⟨j,hj⟩ := even_iff_two_dvd.mp ((Nat.even_or_odd m).resolve_right hh)
  obtain ⟨G,hG⟩ := hF
  rw [hj,hG] at hm
  push_cast at hm
  rcases hε with rfl | rfl <;> ring_nf at hm <;> omega

/-- An integral normalized unit numerator has an odd dyadic boundary
when its factor is even and its primitive coefficient is odd. -/
theorem odd_integral_normalized_unit_boundary
    {F T t m tb k : ℕ} {P Q κ R ε : ℤ}
    (hF : 2 ∣ F) (hm : Odd m) (hP : Odd P)
    (hκ : κ=(m : ℤ)-4*(F : ℤ)*tb)
    (hR : R=(F : ℤ)*tb*Q-κ*P-4*(F : ℤ)*t*ε)
    (hboundary : R=(k : ℤ)*T) : Odd k := by
  by_contra hh
  obtain ⟨j,hj⟩ := even_iff_two_dvd.mp ((Nat.even_or_odd k).resolve_right hh)
  obtain ⟨G,hG⟩ := hF
  obtain ⟨v,hv⟩ := hm
  obtain ⟨w,hw⟩ := hP
  have he : (k : ℤ)*T=(F : ℤ)*tb*Q-((m : ℤ)-4*(F : ℤ)*tb)*P-4*(F : ℤ)*t*ε := by
    rw [← hboundary,hR,hκ]
  rw [hj,hG,hv,hw] at he
  push_cast at he
  ring_nf at he
  omega

/-- At an even primitive factor, the original and top-reflected unit
numerators are both odd signed integers. -/
theorem odd_normalized_unit_numerators
    {F T t m tb : ℕ} {P Q κ R ε : ℤ}
    (hF : 2 ∣ F) (hm : Odd m) (hP : Odd P)
    (hκ : κ=(m : ℤ)-4*(F : ℤ)*tb)
    (hR : R=(F : ℤ)*tb*Q-κ*P-4*(F : ℤ)*t*ε) :
    Odd R ∧ Odd ((F*T : ℕ)-R) := by
  obtain ⟨G,hG⟩ := hF
  obtain ⟨v,hv⟩ := hm
  obtain ⟨w,hw⟩ := hP
  have hodd : Odd R := by
    refine ⟨(G : ℤ)*tb*Q-((v : ℤ)-4*(G : ℤ)*tb)*(2*w+1)-w-1-4*(G : ℤ)*t*ε,?_⟩
    rw [hR,hκ,hG,hv,hw]
    push_cast
    ring
  refine ⟨hodd,?_⟩
  obtain ⟨z,hz⟩ := hodd
  refine ⟨(G : ℤ)*T-z-1,?_⟩
  rw [hG,hz]
  push_cast
  ring

/-- An odd signed integral numerator has an odd natural quotient. -/
theorem odd_nat_quotient_of_odd_signed_numerator
    {k T : ℕ} {R : ℤ} (hR : Odd R) (hk : R=(k : ℤ)*T) : Odd k := by
  by_contra hh
  obtain ⟨j,hj⟩ := even_iff_two_dvd.mp ((Nat.even_or_odd k).resolve_right hh)
  obtain ⟨v,hv⟩ := hR
  rw [hj,hv] at hk
  push_cast at hk
  ring_nf at hk
  omega

/-- Integral scalar windows give actual affordable unequal rivals with
the direct one-coin or reflected two-coin companion saving. -/
theorem exists_unequal_uniform_signed_integral_rival
    {a b f n L N F T t H c E ta tb : ℕ} {Z R A B J : ℤ}
    (ha : 2 ≤ a) (hab : a < b) (hsum : 10 < a+b) (hf : f ≤ a-2) (hn : 67 ≤ n)
    (hL : L+a+b=n) (hF : F=2^f) (ht : t=2^(b-1))
    (hcost : 3*2^(a-1)+t ≤ n+1) (hT : T < 4*t) (hTp : 0 < T)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hE : E ≤ F*t*H)
    (hR : 0 < R) (hint : (T : ℤ) ∣ R) (hodd : f=0 ∨ Odd R)
    (hplan : (R < 2*(F*T : ℕ) ∧ gmin (a-1) ta+gmin (b-1) tb ≤ a+b-1) ∨
      (2*R < 5*(F*T : ℕ) ∧ gmin (a-1) ta+gmin (b-1) tb ≤ a+b-2))
    (hA : |A| ≤ 64*(F : ℤ)*t^2) (hB : |B| ≤ 64*(F : ℤ)*t^2)
    (hJ : J=-1 ∨ J=0 ∨ J=1)
    (herr : (F*T : ℕ)*Z-R*(2 : ℤ)^L=A*H+B*c-(F*T : ℕ)+J*E)
    (x y w : ZMod N) {V : ℕ} (heval : (Z : ZMod N)*x+ta • y+tb • w=V • x) :
    ∃ v, n ≤ v ∧ ∃ k, val L k=v ∧
      dsum L k+gmin (a-1) ta+gmin (b-1) tb ≤ n ∧ v • x+ta • y+tb • w=V • x := by
  let bits := 4*(b+f+1)
  let U := 128*F*t^2
  let companions := gmin (a-1) ta+gmin (b-1) tb
  have hFp : 0 < F := by rw [hF]; positivity
  have htp : 0 < t := by rw [ht]; positivity
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hTZ : (0 : ℤ) < T := by exact_mod_cast hTp
  have hb := unequal_uniform_integral_axis_budget ha hab hsum hf hn hL hF ht hcost
  change f+1 ≤ bits ∧ bits ≤ L ∧ U*n < 2^(L-bits) ∧ f+4+(L-bits)+(a+b) ≤ n at hb
  obtain ⟨k0,hk0⟩ := hint
  have hk0pos : 0 < k0 := by nlinarith only [hR,hk0,hTZ]
  let k := k0.toNat
  have hkcast : (k : ℤ)=k0 := Int.toNat_of_nonneg (le_of_lt hk0pos)
  have hkpos : 1 ≤ k := by dsimp [k]; omega
  have hboundary : R=(k : ℤ)*T := by rw [hkcast]; simpa only [mul_comm] using hk0
  have hkodd : f=0 ∨ Odd k := by
    rcases hodd with hh | hh
    · exact Or.inl hh
    · exact Or.inr (odd_nat_quotient_of_odd_signed_numerator hh hboundary)
  have hbelow : gmin f (2*k-1)+(L-(f+1))+companions ≤ n := by
    rcases hplan with ⟨hr,hcomp⟩ | ⟨hr,hcomp⟩
    · have hknat : k < 2*2^f := by
        have hh : (k : ℤ) < 2*(F : ℤ) := by
          push_cast at hr
          rw [hboundary] at hr
          nlinarith only [hr,hTZ]
        rw [← hF]
        exact_mod_cast hh
      have hc := (unequal_direct_integral_doubled_prefix_bounds hkpos hkodd hknat).1
      dsimp only [companions]
      omega
    · have hknat : 2*k < 5*2^f := by
        have hh : 2*(k : ℤ) < 5*(F : ℤ) := by
          push_cast at hr
          rw [hboundary] at hr
          nlinarith only [hr,hTZ]
        rw [← hF]
        exact_mod_cast hh
      have hc := (unequal_reflected_integral_doubled_prefix_bounds hkpos hkodd hknat).1
      dsimp only [companions]
      omega
  have habove : gmin f (2*k)+(L-bits)+companions ≤ n := by
    have hknat : 2*k < 5*2^f := by
      have hh : 2*(k : ℤ) < 5*(F : ℤ) := by
        rcases hplan with ⟨hr,_⟩ | ⟨hr,_⟩ <;> push_cast at hr <;> rw [hboundary] at hr
        · have hFZ : (0 : ℤ) < F := by exact_mod_cast hFp
          nlinarith only [hr,hTZ,hFZ]
        · nlinarith only [hr,hTZ]
      rw [← hF]
      exact_mod_cast hh
    have hc := (unequal_reflected_integral_doubled_prefix_bounds hkpos hkodd hknat).2
    have hcomp : companions ≤ a+b := by rcases hplan with ⟨_,hh⟩ | ⟨_,hh⟩ <;> dsimp only [companions] <;> omega
    omega
  have hpow : (F : ℤ)*2*2^(L-(f+1))=(2 : ℤ)^L := by
    rw [hF,Nat.cast_pow,Nat.cast_ofNat,← pow_succ,← pow_add]
    congr 1
    omega
  have heq : (F*T : ℕ)*(Z-(2*k : ℕ)*2^(L-(f+1)))=(F*T : ℕ)*Z-R*(2 : ℤ)^L := by
    rw [hboundary]
    push_cast
    linear_combination -(k : ℤ)*(T : ℤ)*hpow
  have hw := unequal_uniform_signed_error_window hFp hTp (by omega : 1 ≤ t) (by omega : T ≤ 4*t)
    hH hnc hE hA hB hJ
  have hwindow := int_error_window_of_positive_multiplier (show 0 < F*T by positivity)
    (δ:=Z-(2*k : ℕ)*2^(L-(f+1)))
    (by rw [heq,herr]; exact hw.1) (by rw [heq,herr]; exact hw.2)
  obtain ⟨hZ,hnZ,rep,hrep,hrepCost⟩ := exists_rep_near_doubled_integral_boundary
    (by omega : 2 ≤ 2*k) (by omega : 1 ≤ U) hb.1 hb.2.1 hb.2.2.1 hbelow habove hwindow.1 hwindow.2
  have hZcast : (Z.toNat : ZMod N)=(Z : ZMod N) := by
    have hh := congrArg (fun v : ℤ ↦ (v : ZMod N)) (Int.toNat_of_nonneg hZ)
    simpa only [Int.cast_natCast] using hh
  exact ⟨Z.toNat,hnZ,rep,hrep,by dsimp only [companions] at hrepCost; omega,
    by simpa only [nsmul_eq_mul,hZcast] using heval⟩

end MinModulus
