import MinModulus.ChainForestProfileUnequalUnit

/-! Uniform closure of nonunit unequal phases. A proper odd-denominator
annihilator multiple has normalized short weight inside the actual half
profile. The genuine scalar equation makes its leading numerator
nonintegral. Direct or half-reflected rivals contradict validity uniformly
in both companion lengths and the actual index. All genuine residual
phases are now integral units; that residual and the conjecture remain open. -/

namespace MinModulus

/-- A multiple of the dyadic factor below the full primitive denominator
cannot be divisible by its coprime odd factor. -/
theorem unequal_annihilator_multiplier_not_dvd_odd_factor
    {F T m : ℕ} (hmpos : 0 < m) (hm : m < F*T) (hFm : F ∣ m)
    (hcop : Nat.Coprime F T) : ¬ T ∣ m := by
  intro hTm
  have hd : F*T ∣ m := hcop.mul_dvd_of_dvd_of_dvd hFm hTm
  exact (not_le_of_gt hm) (Nat.le_of_dvd hmpos hd)

/-- The actual primitive scalar equation prevents every nonzero
annihilator step from having an integral leading numerator. -/
theorem unequal_actual_annihilator_leading_not_dvd
    {F T t c K H α r M m tb : ℕ} {P Q κ R : ℤ}
    (hcop : Nat.Coprime T (t*c)) (hmr : (F*T) ∣ m*r)
    (hmnon : ¬ T ∣ m) (hκ : κ=(m : ℤ)-4*(F : ℤ)*tb)
    (hcancel : (T : ℤ) ∣ (F : ℤ)*tb*(Q+4*P))
    (hR : R=(F : ℤ)*tb*Q-κ*P)
    (hap : (F*T : ℕ)*(α : ℤ)=P*((K : ℤ)-H)+(t : ℤ)*c+(r : ℤ)*M) :
    ¬ (T : ℤ) ∣ R := by
  intro hd
  have hmP : (T : ℤ) ∣ (m : ℤ)*P := by
    have hh := dvd_sub hcancel hd
    have heq : (F : ℤ)*tb*(Q+4*P)-R=(m : ℤ)*P := by rw [hR,hκ]; ring
    rwa [heq] at hh
  have hmrT : (T : ℤ) ∣ (m : ℤ)*r := by
    exact_mod_cast dvd_trans (dvd_mul_left T F) hmr
  have hleft : (T : ℤ) ∣ (m : ℤ)*(F*T : ℕ)*α := by
    refine ⟨(m : ℤ)*F*α,?_⟩
    push_cast
    ring
  have hPterm := dvd_mul_of_dvd_left hmP ((K : ℤ)-H)
  have hrterm := dvd_mul_of_dvd_left hmrT (M : ℤ)
  have htc : (T : ℤ) ∣ (m : ℤ)*t*c := by
    have hh := dvd_sub (dvd_sub hleft hPterm) hrterm
    have heq : (m : ℤ)*(F*T : ℕ)*α-(m : ℤ)*P*((K : ℤ)-H)-(m : ℤ)*r*M=(m : ℤ)*t*c := by
      linear_combination (m : ℤ)*hap
    rwa [heq] at hh
  have htcNat : T ∣ m*(t*c) := by
    exact_mod_cast (show (T : ℤ) ∣ (m : ℤ)*((t : ℤ)*c) by simpa only [mul_assoc] using htc)
  exact hmnon (hcop.dvd_of_dvd_mul_right htcNat)

/-- A modulus remainder above the short half-profile bound has a small
positive complementary remainder. Its annihilator order forces that
complement past the short half-width before wrapping. -/
theorem unequal_annihilator_complement_order_bound
    {g C s t a b v : ℕ} (_hg : 2 ≤ g) (hs : 2 ≤ s) (hC : C+1=4*s)
    (ha : a < C) (hbad : 3*s ≤ a) (hdec : a+C*b=v)
    (hperiod : g*v+s=C*t) (hgnot : ¬ g ∣ s) :
    0 < C-a ∧ C-a < s ∧ s+C ≤ g*(C-a) := by
  have hd : 0 < C-a := by omega
  have hdhi : C-a < s := by omega
  have hrel : g*(C-a)+C*t=s+C*(g*(b+1)) := by
    have hsub : C-a+a=C := Nat.sub_add_cancel (by omega)
    nlinarith only [hsub,hdec,hperiod]
  have hgt : t < g*(b+1) := by
    by_contra hh
    have hle : g*(b+1) ≤ t := by omega
    by_cases he : g*(b+1)=t
    · rw [he] at hrel
      have hh' : g*(C-a)=s := by omega
      exact hgnot ⟨C-a,hh'.symm⟩
    · have hh' : g*(b+1)+1 ≤ t := by omega
      have hmul := Nat.mul_le_mul_left C hh'
      nlinarith only [hrel,hmul,hd,hs,hC]
  have hmul := Nat.mul_le_mul_left C (show t+1 ≤ g*(b+1) by omega)
  exact ⟨hd,hdhi,by nlinarith only [hrel,hmul]⟩

/-- A small complementary remainder supplies a strictly smaller
annihilator multiple that crosses the short half-width but does not wrap. -/
theorem unequal_annihilator_small_multiple_bounds
    {g C s δ : ℕ} (hδ : 0 < δ) (hδs : δ < s) (hC : C+1=4*s)
    (horder : s+C ≤ g*δ) :
    1 ≤ s/δ+1 ∧ s/δ+1 < g ∧ s < (s/δ+1)*δ ∧ (s/δ+1)*δ < C := by
  have hdecomp := Nat.mod_add_div s δ
  have hmod := Nat.mod_lt s hδ
  have hle := Nat.div_mul_le_self s δ
  have hcross : s < (s/δ+1)*δ := by nlinarith only [hdecomp,hmod]
  have hupper : (s/δ+1)*δ ≤ s+δ := by nlinarith only [hle]
  have hg : s/δ+1 < g := by
    apply Nat.lt_of_mul_lt_mul_right (a:=δ)
    nlinarith only [hupper,horder,hC,hδs,hδ]
  exact ⟨Nat.succ_le_succ (Nat.zero_le _),hg,hcross,by omega⟩

/-- Before a complementary remainder wraps, multiplication gives its
exact reflected remainder in the normalization modulus. -/
theorem normalized_complement_remainder_of_small_multiple
    {C v k : ℕ} (hC : 0 < C) (hkpos : 0 < k*(C-v%C)) (hk : k*(C-v%C) < C) :
    (k*v)%C=C-k*(C-v%C) := by
  let δ := C-v%C
  change 0 < k*δ at hkpos
  change k*δ < C at hk
  have hd : v%C+δ=C := by dsimp [δ]; have hh := Nat.mod_lt v hC; omega
  have hdec := Nat.mod_add_div v C
  have hvd : C ∣ v+δ := by
    refine ⟨v/C+1,?_⟩
    nlinarith only [hdec,hd]
  have hmod : Nat.ModEq C (v+δ) 0 := Nat.modEq_zero_iff_dvd.mpr hvd
  have hmult : Nat.ModEq C (k*v+k*δ) 0 := by
    simpa only [Nat.mul_add,Nat.mul_zero] using hmod.mul_left k
  have hright : Nat.ModEq C ((C-k*δ)+k*δ) 0 := by
    rw [Nat.sub_add_cancel (by omega : k*δ ≤ C)]
    exact Nat.modulus_modEq_zero
  have hh := Nat.ModEq.add_right_cancel' (k*δ) (hmult.trans hright.symm)
  exact Nat.mod_eq_of_modEq hh (by change C-k*δ < C; omega)

/-- Some proper multiple in every odd annihilator orbit has normalized
short weight within the actual short half profile. -/
theorem exists_unequal_annihilator_multiple_short_bound
    {g C s t v : ℕ} (hg : 2 ≤ g) (hs : 2 ≤ s) (hC : C+1=4*s)
    (hperiod : g*v+s=C*t) (hgnot : ¬ g ∣ s) :
    ∃ k : ℕ, 1 ≤ k ∧ k < g ∧ (k*v)%C ≤ 3*s-1 := by
  have hCp : 0 < C := by omega
  by_cases hgood : v%C ≤ 3*s-1
  · exact ⟨1,by decide,by omega,by simpa only [one_mul] using hgood⟩
  have hdec : v%C+C*(v/C)=v := Nat.mod_add_div v C
  obtain ⟨hδ,hδs,horder⟩ := unequal_annihilator_complement_order_bound hg hs hC
    (Nat.mod_lt v hCp) (by omega) hdec hperiod hgnot
  obtain ⟨hkpos,hk,hcross,hwrap⟩ := unequal_annihilator_small_multiple_bounds hδ hδs hC horder
  refine ⟨s/(C-v%C)+1,hkpos,hk,?_⟩
  rw [normalized_complement_remainder_of_small_multiple hCp (by omega) hwrap]
  omega

/-- A nonunit odd primitive phase has a nonzero annihilator multiplier
in the dyadic lattice, with its short weight inside the actual half profile. -/
theorem exists_unequal_normalized_annihilator_multiplier
    {D F s t u C T r : ℕ} (_hD : 0 < D) (hF : 0 < F) (hs : 2 ≤ s)
    (hDF : D*F=s) (htu : t=s*u) (hC : C+1=4*s) (hT : T+u+1=4*t)
    (hTp : 0 < T) (hcop : Nat.Coprime T s) (hr : ¬ Nat.Coprime r T) :
    ∃ m : ℕ, 1 ≤ m ∧ m < F*T ∧ F ∣ m ∧ F*T ∣ m*r ∧
      unequalNormalizedShortWeight D C m ≤ 3*s-1 := by
  let g := Nat.gcd r T
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right r hTp
  have hg : 2 ≤ g := by
    have hh : g ≠ 1 := by simpa only [g,Nat.coprime_iff_gcd_eq_one] using hr
    omega
  have hgT : g ∣ T := Nat.gcd_dvd_right r T
  have hgr : g ∣ r := Nat.gcd_dvd_left r T
  have hgnot : ¬ g ∣ s := by
    intro hgs
    have hh : g ∣ Nat.gcd T s := Nat.dvd_gcd hgT hgs
    rw [hcop.gcd_eq_one] at hh
    have hh' := Nat.dvd_one.mp hh
    omega
  let m0 := F*(T/g)
  let v := D*m0
  have hgTq : g*(T/g)=T := Nat.mul_div_cancel' hgT
  have hg0 : g*m0=F*T := by dsimp [m0]; nlinarith only [hgTq]
  have hm0 : 0 < m0 := by have hp : 0 < F*T := Nat.mul_pos hF hTp; nlinarith only [hg0,hp]
  have hperiod : g*v+s=C*t := by
    have hCT : s*T+s=C*t := by
      have hh := congrArg (fun z : ℕ ↦ s*z) hT
      have hc := congrArg (fun z : ℕ ↦ z*t) hC
      nlinarith only [hh,hc,htu]
    dsimp [v]
    nlinarith only [hg0,hDF,hCT]
  obtain ⟨k,hkpos,hk,hshort⟩ := exists_unequal_annihilator_multiple_short_bound hg hs hC hperiod hgnot
  refine ⟨k*m0,by have hp := Nat.mul_pos (show 0 < k by omega) hm0; omega,?_,?_,?_,?_⟩
  · have hh := Nat.mul_lt_mul_of_pos_right hk hm0
    rwa [hg0] at hh
  · refine ⟨k*(T/g),?_⟩
    dsimp [m0]
    ring
  · obtain ⟨r0,hr0⟩ := hgr
    refine ⟨k*r0,?_⟩
    rw [hr0,← hg0]
    ring
  · change (D*(k*m0))%C ≤ 3*s-1
    have he : D*(k*m0)=k*v := by dsimp [v]; ring
    rwa [he]

/-- A short annihilator numerator lies between minus one and one
primitive denominator when its weight is inside the actual half profile. -/
theorem unequal_normalized_short_annihilator_leading_bounds
    {D F s t u C T m ta tb : ℕ} (hD : 0 < D) (hs : 2 ≤ s)
    (hDF : D*F=s) (htu : t=s*u) (hu : 2 ≤ u) (hC : C+1=4*s) (hT : T+u+1=4*t)
    (hta : ta < C) (htb : tb < t) (hdecomp : ta+C*tb=D*m) (hpos : 0 < ta+tb)
    (hshort : ta ≤ 3*s-1) :
    -(F*T : ℕ) < (m : ℤ)-(F : ℤ)*tb-(F : ℤ)*u*ta ∧
    (m : ℤ)-(F : ℤ)*tb-(F : ℤ)*u*ta < (F*T : ℕ) := by
  have hd := unequal_normalized_index_step_delta_bounds hD hs hDF htu hu hC hta htb hdecomp hpos
  have hFp : 0 < F := by nlinarith only [hDF,hs]
  have hFZ : (0 : ℤ) < F := by exact_mod_cast hFp
  have htuZ : (t : ℤ)=(s : ℤ)*u := by exact_mod_cast htu
  have hTZ : (T : ℤ)+u+1=4*t := by exact_mod_cast hT
  have htaZ : (ta : ℤ) ≤ 3*(s : ℤ)-1 := by
    have hh : (ta : ℤ)+1 ≤ 3*(s : ℤ) := by exact_mod_cast (show ta+1 ≤ 3*s by omega)
    omega
  have hut : (u : ℤ)+1 < t := by
    have hsZ : (2 : ℤ) ≤ s := by exact_mod_cast hs
    have huZ : (2 : ℤ) ≤ u := by exact_mod_cast hu
    have hh := mul_nonneg (show 0 ≤ (s : ℤ)-2 by omega) (show (0 : ℤ) ≤ u by positivity)
    nlinarith only [hh,htuZ,huZ]
  have hFt : (F : ℤ)*t=(F : ℤ)*u*s := by linear_combination (F : ℤ)*htuZ
  have hST : (F : ℤ)*T+(F : ℤ)*u+F=4*(F : ℤ)*t := by linear_combination (F : ℤ)*hTZ
  have hmul := mul_le_mul_of_nonneg_left htaZ (show 0 ≤ (F : ℤ)*u by positivity)
  have htp : (0 : ℤ) < (F : ℤ)*((t : ℤ)-1) := mul_pos hFZ (by omega)
  have htp' : (0 : ℤ) < (F : ℤ)*((t : ℤ)-u-1) := mul_pos hFZ (by omega)
  have hnonneg : (0 : ℤ) ≤ (F : ℤ)*u*ta := by positivity
  push_cast
  constructor <;> nlinarith only [hd.1,hd.2.1,hmul,htp,htp',hnonneg,hFt,hST]

/-- A long annihilator numerator is below three primitive denominators;
a negative numerator permits the actual long half-profile reflection. -/
theorem unequal_normalized_long_annihilator_leading_bounds
    {D F s t u C T m ta tb : ℕ} (hD : 0 < D) (hs : 2 ≤ s)
    (hDF : D*F=s) (htu : t=s*u) (hu : 2 ≤ u) (hC : C+1=4*s) (hT : T+u+1=4*t)
    (hta : ta < C) (htb : tb < t) (hdecomp : ta+C*tb=D*m) (hpos : 0 < ta+tb) :
    -(F*T : ℕ) < 3*(F : ℤ)*u*ta-m+3*(F : ℤ)*tb ∧
    3*(F : ℤ)*u*ta-m+3*(F : ℤ)*tb < 3*(F*T : ℕ) ∧
    (3*(F : ℤ)*u*ta-m+3*(F : ℤ)*tb ≤ 0 → ta < s) := by
  have hd := unequal_normalized_index_step_delta_bounds hD hs hDF htu hu hC hta htb hdecomp hpos
  have hFp : 0 < F := by nlinarith only [hDF,hs]
  have hFZ : (0 : ℤ) < F := by exact_mod_cast hFp
  have huZ : (2 : ℤ) ≤ u := by exact_mod_cast hu
  have hsZ : (2 : ℤ) ≤ s := by exact_mod_cast hs
  have htuZ : (t : ℤ)=(s : ℤ)*u := by exact_mod_cast htu
  have hTZ : (T : ℤ)+u+1=4*t := by exact_mod_cast hT
  have htaZ : (ta : ℤ) ≤ 4*(s : ℤ)-2 := by
    have hh : (ta : ℤ)+2 ≤ 4*(s : ℤ) := by exact_mod_cast (show ta+2 ≤ 4*s by omega)
    omega
  have hFt : (F : ℤ)*t=(F : ℤ)*u*s := by linear_combination (F : ℤ)*htuZ
  have hST : (F : ℤ)*T+(F : ℤ)*u+F=4*(F : ℤ)*t := by linear_combination (F : ℤ)*hTZ
  have hut : (u : ℤ)+1 < t := by
    have hh := mul_nonneg (show 0 ≤ (s : ℤ)-2 by omega) (show (0 : ℤ) ≤ u by positivity)
    nlinarith only [hh,htuZ,huZ]
  have hwide : 2*(F : ℤ)*t < (F : ℤ)*T := by
    have hh := mul_pos hFZ (show 0 < 2*(t : ℤ)-u-1 by omega)
    nlinarith only [hh,hST]
  have hFU : (0 : ℤ) < (F : ℤ)*u := by positivity
  have hmul := mul_le_mul_of_nonneg_left htaZ (show 0 ≤ 3*(F : ℤ)*u by positivity)
  have hsep := mul_pos hFZ (show 0 < (u : ℤ)-1 by omega)
  have hnonneg : (0 : ℤ) ≤ (F : ℤ)*u*ta := by positivity
  push_cast
  refine ⟨by nlinarith only [hd.2.2.2,hnonneg,hwide],by nlinarith only [hd.2.2.1,hmul,hsep,hFt,hST],?_⟩
  intro hneg
  have hh : (ta : ℤ) < s := by
    apply (mul_lt_mul_iff_right₀ hFU).mp
    have hp : (0 : ℤ) < (F : ℤ)*t := mul_pos hFZ (by omega)
    nlinarith only [hd.2.2.2,hneg,hFt,hp]
  exact_mod_cast hh

/-- Every nonunit unequal phase supplies an actual affordable rival.
Both half orientations use the same bounded annihilator construction. -/
theorem exists_unequal_normalized_nonunit_rival
    {a b f d n L N D F s t u T H c V M E α z r q : ℕ} {P Q : ℤ}
    (ha : 2 ≤ a) (hab : a < b) (hsum : 10 < a+b) (hf : f ≤ a-2) (hn : 67 ≤ n)
    (hL : L+a+b=n) (hD : 0 < D) (hF : F=2^f) (hs : s=2^(a-1)) (ht : t=2^(b-1)) (hc : c=2^d)
    (hDF : D*F=s) (htu : t=s*u) (hu : 2 ≤ u) (hT : T+u+1=4*t) (hTodd : Odd T)
    (hcost : 3*s+t ≤ n+1) (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hM : M+E=4*F*t*2^L) (hE : E ≤ F*t*H)
    (hlink : T ∣ 4*r+q) (hr : ¬ Nat.Coprime r T)
    (hap : (F*T : ℕ)*(α : ℤ)=P*((2 : ℤ)^L-H)+(t : ℤ)*c+(r : ℤ)*M)
    (hzp : (T : ℤ)*z=Q*(2 : ℤ)^L+((T : ℤ)-Q)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*M)
    (x y w : ZMod N) (hα : α • x=D • y) (hz : z • x+y+w=V • x) (hmx : M • x=0)
    (hcase : (P=(t : ℤ)-1 ∧ Q=3-(u : ℤ) ∧ (3*s-1) • y+(t-1) • w=c • x) ∨
      (P=1-3*(t : ℤ) ∧ Q=3*(u : ℤ)-1 ∧ (s-1) • y+(3*t-1) • w=c • x)) :
    ∃ ta tb, (ta ≠ 2^a-1 ∨ tb ≠ 2^b-1) ∧ ∃ v, n ≤ v ∧ ∃ k,
      val L k=v ∧ dsum L k+gmin (a-1) ta+gmin (b-1) tb ≤ n ∧
      v • x+ta • y+tb • w=V • x := by
  have hs2 : 2 ≤ s := by rw [hs]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ a-1)
  have hFp : 0 < F := by rw [hF]; positivity
  have htus : 2*u ≤ t := by nlinarith only [Nat.mul_le_mul_right u hs2,htu]
  have ht2 : 2 ≤ t := by omega
  have hTp : 0 < T := by omega
  have hTlt : T < 4*t := by omega
  have hcopTs : Nat.Coprime T s := by rw [hs]; exact hTodd.coprime_two_right.pow_right _
  have hcopTc : Nat.Coprime T (t*c) := by
    rw [ht,hc]
    exact (hTodd.coprime_two_right.pow_right _).mul_right (hTodd.coprime_two_right.pow_right _)
  have hcopFT : Nat.Coprime F T := by rw [hF]; exact hTodd.coprime_two_left.pow_left _
  let C := 4*s-1
  have hC : C+1=4*s := by dsimp [C]; omega
  obtain ⟨m,hmpos,hm,hFm,hmr,hshort⟩ := exists_unequal_normalized_annihilator_multiplier
    hD hFp hs2 hDF htu hC hT hTp hcopTs hr
  have hmnon := unequal_annihilator_multiplier_not_dvd_odd_factor (by omega : 0 < m) hm hFm hcopFT
  obtain ⟨l,hl⟩ := hmr
  have hml : (m : ℤ)*r=(F*T : ℕ)*(l : ℤ)+0 := by exact_mod_cast (show m*r=F*T*l+0 by omega)
  obtain ⟨p,hp⟩ := hlink
  let ta := unequalNormalizedShortWeight D C m
  let tb := unequalNormalizedLongWeight D C m
  obtain ⟨hta,htb,hdec,hpos⟩ := unequal_normalized_companion_weight_bounds hD hs2 hDF htu hu hC hT hmpos hm
  change ta < C at hta
  change tb < t at htb
  change ta+C*tb=D*m at hdec
  change 0 < ta+tb at hpos
  change ta ≤ 3*s-1 at hshort
  let κ : ℤ := (m : ℤ)-4*(F : ℤ)*tb
  let ν : ℤ := (tb : ℤ)*p-l
  let R : ℤ := (F : ℤ)*tb*Q-κ*P
  let Z : ℤ := (tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M
  let A : ℤ := (F*T : ℕ)-(F : ℤ)*tb*Q+κ*P
  let B : ℤ := (F*T : ℕ)-(F : ℤ)*tb*(u+1)-κ*t
  have hi : (ta : ℤ)=tb+(D : ℤ)*κ := unequal_normalized_signed_index_relation hDF hC hdec
  have hphase : (F*T : ℕ)*ν-(F : ℤ)*tb*q+κ*r=0 := by
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
  have hRnon : ¬ (T : ℤ) ∣ R := unequal_actual_annihilator_leading_not_dvd (K:=2^L) hcopTc ⟨l,hl⟩ hmnon
    rfl hcancel rfl (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hap)
  have hRne : R ≠ 0 := by intro hh; apply hRnon; rw [hh]; exact dvd_zero _
  have hRshort (hP : P=(t : ℤ)-1) (hQ : Q=3-(u : ℤ)) :
      R=(m : ℤ)-(F : ℤ)*tb-(F : ℤ)*u*ta := by
    have hid := unequal_normalized_short_leading_identity hD hDF htu hC hdec
    dsimp only [R,κ]
    rw [hP,hQ]
    linarith only [hid]
  have hRlong (hP : P=1-3*(t : ℤ)) (hQ : Q=3*(u : ℤ)-1) :
      R=3*(F : ℤ)*u*ta-m+3*(F : ℤ)*tb := by
    have hid := unequal_normalized_long_leading_identity hD hDF htu hC hdec
    dsimp only [R,κ]
    rw [hP,hQ]
    linarith only [hid]
  have hS0 : (0 : ℤ) < (F*T : ℕ) := by exact_mod_cast Nat.mul_pos hFp hTp
  have hRbounds : -(F*T : ℕ) < R ∧ R < 3*(F*T : ℕ) := by
    rcases hcase with ⟨hP,hQ,_⟩ | ⟨hP,hQ,_⟩
    · rw [hRshort hP hQ]
      have hh := unequal_normalized_short_annihilator_leading_bounds hD hs2 hDF htu hu hC hT hta htb hdec hpos hshort
      exact ⟨hh.1,by linarith only [hh.2,hS0]⟩
    · rw [hRlong hP hQ]
      have hh := unequal_normalized_long_annihilator_leading_bounds hD hs2 hDF htu hu hC hT hta htb hdec hpos
      exact ⟨hh.1,hh.2.1⟩
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
  have herr : (F*T : ℕ)*Z-R*(2 : ℤ)^L=A*H+B*c-(F*T : ℕ)+(0 : ℤ)*E := by
    have hh := unequal_normalized_signed_rival_error (v:=u+1) hbase hM
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hap)
      (by push_cast; convert hzp using 1; ring) hphase
      (show R=(F : ℤ)*tb*Q-κ*P-(4*F*t : ℕ)*0 by simp only [mul_zero,sub_zero,R])
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using hh
  have heval : (Z : ZMod N)*x+ta • y+tb • w=V • x := signed_axis_basis_rival_cast_eq x y w κ ν hi hz hα hmx
  have hpA : 2^a=2*s := by rw [hs,← pow_succ']; congr 1; omega
  have hpB : 2^b=2*t := by rw [ht,← pow_succ']; congr 1; omega
  have hcost' : 3*2^(a-1)+t ≤ n+1 := by rwa [← hs]
  have hN0 : (0 : ℤ) ≤ (F : ℤ)*t^2 := by positivity
  by_cases hRpos : 0 < R
  · have hcomp := unequal_normalized_companion_coin_bound (by omega : 1 ≤ a) (by omega : 1 ≤ b) hs ht hC hta htb
    obtain ⟨v,hv,k,hk,hck,hvgroup⟩ := exists_unequal_uniform_signed_nonintegral_rival
      ha hab hsum hf hn hL hF ht hcost' hTlt hTodd hH hnc hE hRpos hRbounds.2 hRnon hcomp
      (by linarith only [hcoeff.1,hN0]) (by linarith only [hcoeff.2,hN0]) (by simp) herr x y w heval
    exact ⟨ta,tb,Or.inr (by rw [hpB]; omega),v,hv,k,hk,hck,hvgroup⟩
  · have hreflection : ∃ A0 B0 : ℕ, ta ≤ A0 ∧ tb ≤ B0 ∧ A0 • y+B0 • w=c • x ∧
        gmin (a-1) (A0-ta)+gmin (b-1) (B0-tb) ≤ a+b ∧
        (A0-ta ≠ 2^a-1 ∨ B0-tb ≠ 2^b-1) := by
      rcases hcase with ⟨_,_,hhalf⟩ | ⟨hP,hQ,hhalf⟩
      · have hca := gmin_normalized_short_weight_bound (by omega : 1 ≤ a) hs
          (show 3*s-1-ta < 4*s-1 by omega)
        have hcb := gmin_binary_low_le (e:=b-1) (r:=t-1-tb) (by rw [← ht]; omega)
        exact ⟨3*s-1,t-1,hshort,by omega,hhalf,by omega,Or.inr (by rw [hpB]; omega)⟩
      · have hbd := unequal_normalized_long_annihilator_leading_bounds hD hs2 hDF htu hu hC hT hta htb hdec hpos
        have htasmall : ta < s := hbd.2.2 (by rw [← hRlong hP hQ]; omega)
        have hca := gmin_binary_low_le (e:=a-1) (r:=s-1-ta) (by rw [← hs]; omega)
        have hcb := gmin_normalized_short_weight_bound (by omega : 1 ≤ b) ht
          (show 3*t-1-tb < 4*t-1 by omega)
        exact ⟨s-1,3*t-1,by omega,by omega,hhalf,by omega,Or.inl (by rw [hpA]; omega)⟩
    obtain ⟨A0,B0,hta0,htb0,hhalf,hcomp,hdist⟩ := hreflection
    let R' : ℤ := -R
    let Z' : ℤ := (H : ℤ)-1+V-Z
    have hhalfprofile : (H-1) • x+A0 • y+B0 • w=V • x := by
      rw [add_assoc,hhalf,← add_nsmul,show H-1+c=V by omega]
    have heval' : (Z' : ZMod N)*x+(A0-ta) • y+(B0-tb) • w=V • x := by
      have hh := signed_axis_rival_profile_reflection x y w hta0 htb0 hhalfprofile heval
      simpa only [Nat.cast_sub hH,Nat.cast_one] using hh
    have herr' : (F*T : ℕ)*Z'-R'*(2 : ℤ)^L=
        (2*(F*T : ℕ)-A)*H+((F*T : ℕ)-B)*c-(F*T : ℕ)+(0 : ℤ)*E := by
      have hh := signed_axis_rival_half_error_reflection (K:=2^L) hbase
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using herr)
      dsimp only [Z',R']
      simpa only [Nat.cast_pow,Nat.cast_ofNat,zero_mul,sub_zero,add_zero] using hh
    have hAc := (unequal_reflected_error_coefficient_bound (by omega : 1 ≤ t) (by omega : T ≤ 4*t) hcoeff.1).2
    have hBc := (unequal_reflected_error_coefficient_bound (by omega : 1 ≤ t) (by omega : T ≤ 4*t) hcoeff.2).1
    have hnR' : ¬ (T : ℤ) ∣ R' := by simpa only [R',dvd_neg] using hRnon
    obtain ⟨v,hv,k,hk,hck,hvgroup⟩ := exists_unequal_uniform_signed_nonintegral_rival
      ha hab hsum hf hn hL hF ht hcost' hTlt hTodd hH hnc hE
      (by change 0 < -R; omega : 0 < R')
      (by change -R < 3*(F*T : ℕ); linarith only [hRbounds.1,hS0] : R' < 3*(F*T : ℕ)) hnR' hcomp hAc hBc
      (by simp) herr' x y w heval'
    exact ⟨A0-ta,B0-tb,hdist,v,hv,k,hk,hck,hvgroup⟩

/-- Actual unequal primitive data now retain only integral unit phases. -/
def UnequalCompanionIntegralPrimitiveData
    (n N D F s t u T K H c V : ℕ) (x a b : ZMod N) : Prop :=
  (K-1) • x+(2*s-1) • a+(2*t-1) • b=V • x ∧
  ∃ α z r q : ℕ, α < N/D ∧ z < N/D ∧
    α • x=D • a ∧ z • x+a+b=V • x ∧ T ∣ 4*r+q ∧ (F=1 ∨ Odd r) ∧
    ((H+3*s+t ≤ n+2 ∧ (3*s-1) • a+(t-1) • b=c • x ∧
      r < F*T ∧ q ≤ T ∧
      (F*T : ℕ)*(α : ℤ)=((t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c+(r : ℤ)*(N/D : ℕ) ∧
      (T : ℤ)*z=(3-(u : ℤ))*K+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*(N/D : ℕ) ∧
      (u ≤ 3 → q < T) ∧ (4 ≤ u → 1 ≤ q) ∧
      (Nat.Coprime r T ∧ (T : ℤ) ∣ ((t : ℤ)-1)+4*(F : ℤ)*t*r)) ∨
    (H+s+3*t ≤ n+2 ∧ (s-1) • a+(3*t-1) • b=c • x ∧
      1 ≤ r ∧ r ≤ F*T ∧ q < T ∧
      (F*T : ℕ)*(α : ℤ)=-(3*(t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c+(r : ℤ)*(N/D : ℕ) ∧
      (T : ℤ)*z=(3*(u : ℤ)-1)*K+((T : ℤ)-3*u+1)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*(N/D : ℕ) ∧
      (Nat.Coprime r T ∧ (T : ℤ) ∣ (1-3*(t : ℤ))+4*(F : ℤ)*t*r)))

/-- Validity excludes every nonunit unequal phase via an actual half-profile
reflection when necessary, preserving the remaining integral unit data. -/
theorem unequal_integral_primitive_data_of_valid_forest
    {n N e d H c V : ℕ} [NeZero N] (hn : 67 ≤ n)
    {β : Type*} [Fintype β] (hrank : Fintype.card β=3)
    (L : β → ℕ) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (I : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (I ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hlen : L a < L k) (hsum : 10 < L a+L k) (hepos : 1 ≤ e) (he : e < L a)
    (hH : 1 ≤ H) (hc : c=2^d) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hindex : N.gcd (x j).val=2^e) (hsub : N < 2^n)
    (hgap : 4*2^(L a-1)*2^(L k-1)*2^(L j) ≤ N+2^(L a-1)*2^(L k-1)*H)
    (hdata : UnequalCompanionUnitReducedPrimitiveData n N (2^e) (2^(L a-1-e))
      (2^(L a-1)) (2^(L k-1)) (2^(L k-L a)) (4*2^(L k-1)-2^(L k-L a)-1)
      (2^(L j)) H c V (x j) (x a) (x k)) :
    UnequalCompanionIntegralPrimitiveData n N (2^e) (2^(L a-1-e))
      (2^(L a-1)) (2^(L k-1)) (2^(L k-L a)) (4*2^(L k-1)-2^(L k-L a)-1)
      (2^(L j)) H c V (x j) (x a) (x k) := by
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
  change UnequalCompanionUnitReducedPrimitiveData n N D F s t u T (2^(L j)) H c V (x j) (x a) (x k) at hdata
  change UnequalCompanionIntegralPrimitiveData n N D F s t u T (2^(L j)) H c V (x j) (x a) (x k)
  rcases hdata with ⟨htop,α,z,r,q,hαlo,hzlo,hα,hz,hlink,hres,horient⟩
  have htarget : (∑ i, (2^(L i)-1) • x i)=V • x j := by
    have htop' := htop
    rw [← hpA,← hpB] at htop'
    rw [hset]
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,add_assoc] using htop'
  have hclose (P Q : ℤ)
      (hcase : (P=(t : ℤ)-1 ∧ Q=3-(u : ℤ) ∧ (3*s-1) • x a+(t-1) • x k=c • x j) ∨
        (P=1-3*(t : ℤ) ∧ Q=3*(u : ℤ)-1 ∧ (s-1) • x a+(3*t-1) • x k=c • x j))
      (hcost : 3*s+t ≤ n+1) (hrT : ¬ Nat.Coprime r T)
      (hap : (F*T : ℕ)*(α : ℤ)=P*((2 : ℤ)^(L j)-H)+(t : ℤ)*c+(r : ℤ)*M)
      (hzp : (T : ℤ)*z=Q*(2 : ℤ)^(L j)+((T : ℤ)-Q)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*M) : False := by
    obtain ⟨ta,tb,hd,Z,hZ,rep,hrep,hcost',heval⟩ := exists_unequal_normalized_nonunit_rival
      ha hlen hsum (by omega : L a-1-e ≤ L a-2) hn hsize hD rfl rfl rfl hc hDF htu hu hT hTodd
      hcost hH hnc hbase hME hE hlink hrT hap hzp (x j) (x a) (x k) hα hz hmx hcase
    obtain ⟨ua,hua,hca⟩ := exists_rep_gmin (L a-1) ta
    obtain ⟨uk,huk,hck⟩ := exists_rep_gmin (L k-1) tb
    rw [show L a-1+1=L a by omega] at hua hca
    rw [show L k-1+1=L k by omega] at huk hck
    exact not_validTuple_of_three_axis_representations hrank L g I x b hchain j a k haj hkj hka
      Z ta tb rep ua uk hrep hua huk (by rw [hca,hck]; exact hcost')
      (by omega) hd (heval.trans htarget.symm) hg
  refine ⟨htop,α,z,r,q,hαlo,hzlo,hα,hz,hlink,hres,?_⟩
  rcases horient with ⟨hcost,hhalf,hrhi,hqhi,hap,hzp,hq0,hq1,hunit⟩ | ⟨hcost,hhalf,hrlo,hrhi,hqhi,hap,hzp,hunit⟩
  · left
    refine ⟨hcost,hhalf,hrhi,hqhi,hap,hzp,hq0,hq1,?_⟩
    have hrT : Nat.Coprime r T := by
      by_contra hnon
      apply hclose ((t : ℤ)-1) (3-(u : ℤ)) (Or.inl ⟨rfl,rfl,hhalf⟩) (by omega) hnon
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hap)
      simp only [Nat.cast_pow,Nat.cast_ofNat] at hzp
      convert hzp using 1; ring
    exact ⟨hrT,hunit.resolve_left (not_not.mpr hrT)⟩
  · right
    refine ⟨hcost,hhalf,hrlo,hrhi,hqhi,hap,hzp,?_⟩
    have hrT : Nat.Coprime r T := by
      by_contra hnon
      apply hclose (1-3*(t : ℤ)) (3*(u : ℤ)-1) (Or.inr ⟨rfl,rfl,hhalf⟩) (by omega) hnon
      · simp only [Nat.cast_pow,Nat.cast_ofNat] at hap
        convert hap using 1; ring
      · simp only [Nat.cast_pow,Nat.cast_ofNat] at hzp
        convert hzp using 1; ring
    exact ⟨hrT,hunit.resolve_left (not_not.mpr hrT)⟩

/-- Integral unit data preserve every earlier unit-phase residual field. -/
theorem UnequalCompanionIntegralPrimitiveData.to_unit_reduced
    {n N D F s t u T K H c V : ℕ} {x a b : ZMod N}
    (hdata : UnequalCompanionIntegralPrimitiveData n N D F s t u T K H c V x a b) :
    UnequalCompanionUnitReducedPrimitiveData n N D F s t u T K H c V x a b := by
  rcases hdata with ⟨htop,α,z,r,q,hαlo,hzlo,hα,hz,hlink,hres,horient⟩
  refine ⟨htop,α,z,r,q,hαlo,hzlo,hα,hz,hlink,hres,?_⟩
  rcases horient with ⟨hc,hh,hr,hq,hap,hzp,hq0,hq1,_,hint⟩ | ⟨hc,hh,hr0,hr1,hq,hap,hzp,_,hint⟩
  · exact Or.inl ⟨hc,hh,hr,hq,hap,hzp,hq0,hq1,Or.inr hint⟩
  · exact Or.inr ⟨hc,hh,hr0,hr1,hq,hap,hzp,Or.inr hint⟩

/-- All genuine maximal-even-axis unequal residual phases are integral
units; every previous index and modulus stratum remains available. -/
theorem even_axis_subglobal_maximal_unequal_companion_integral_unit_data
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
    (hvz : ∀ i, i ≠ j → (v i).val=0) (hsub : N < globalBound n) :
    let s := 2^(L a-1)
    let t := 2^(L k-1)
    let u := 2^(L k-L a)
    ∃ e h d : ℕ, 1 ≤ e ∧ e < L a ∧ N.gcd (x j).val=2^e ∧
      2^h+2^d ≤ n ∧ 2^h+2^d=(v j).val+1 ∧
      4*s*t*2^(L j) ≤ N+s*t*2^h ∧ 2^(Nat.log 2 n) < s*t*2^h ∧
      UnequalCompanionIntegralPrimitiveData n N (2^e) (2^(L a-1-e)) s t u (4*t-u-1)
        (2^(L j)) (2^h) (2^d) (v j).val (x j) (x a) (x k) ∧
      (∀ t ≤ L a-1-e, 2^(e+t) ∣ N ↔ t ≤ h) ∧
      (e=L a-1 ∨
        (h < L a-1-e ∧ ∃ q, Odd q ∧ N=2^(e+h)*q) ∨
        (h=L a-1-e ∧ 2^(L a) ∣ N) ∨
        (L a-1-e < h ∧ ∃ q, Odd q ∧ N=2^(L a-1)*q)) := by
  have hsum : 10 < L a+L k := by
    by_contra hh
    have hglo := even_axis_companion_length_sum_le_ten_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka (by omega) hj hother v hv hvz
    omega
  obtain ⟨e,h,d,hepos,he,hindex,hnc,hbase,hgap,hcharge,hdata,hprofile,hstratum⟩ :=
    even_axis_subglobal_maximal_unequal_companion_unit_residual_data hn hN hr L hL
      g hg E x b hchain hgen j a k haj hkj hka hlen hmax hj hother v hv hvz hsub
  exact ⟨e,h,d,hepos,he,hindex,hnc,hbase,hgap,hcharge,
    unequal_integral_primitive_data_of_valid_forest hn hr L g hg E x b hchain j a k haj hkj hka
      hlen hsum hepos he Nat.one_le_two_pow rfl hnc hbase hindex
      (lt_of_lt_of_le hsub (Nat.sub_le _ _)) hgap hdata,hprofile,hstratum⟩

end MinModulus
