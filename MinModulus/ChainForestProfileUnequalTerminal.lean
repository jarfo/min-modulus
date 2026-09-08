import MinModulus.ChainForestProfileUnequalStratum

/-! Actual odd companion seeds sharpen the terminal unequal modulus
profile below the largest possible index. Equality of heights forces an
extra factor of two; greater height fixes the valuation exactly. -/

namespace MinModulus

/-- Once twice the axis index divides the modulus, a coefficient taking
an index multiple of an odd companion into the axis must itself be odd. -/
theorem odd_axis_coefficient_of_double_index_dvd_modulus
    {N D α : ℕ} [NeZero N] (hD : 0 < D) (hDN : 2*D ∣ N)
    (x a : ZMod N) (hDx : D ∣ x.val) (ha : Odd a.val) (hα : α • x=D • a) : Odd α := by
  by_contra hodd
  have heven : 2 ∣ α := even_iff_two_dvd.mp ((Nat.even_or_odd α).resolve_right hodd)
  obtain ⟨k,hk⟩ := heven
  obtain ⟨u,hu⟩ := hDx
  have hax : 2*D ∣ α*x.val := by
    refine ⟨k*u,?_⟩
    rw [hk,hu]
    ring
  let π := ZMod.castHom hDN (ZMod (2*D))
  have hπval : ∀ z : ZMod N, π z=(z.val : ZMod (2*D)) := fun z ↦ ZMod.cast_eq_val z
  have hh := congrArg π hα
  simp only [map_nsmul] at hh
  simp only [hπval,nsmul_eq_mul] at hh
  have hz : (α : ZMod (2*D))*(x.val : ZMod (2*D))=0 := by
    simpa only [Nat.cast_mul] using (ZMod.natCast_eq_zero_iff (α*x.val) (2*D)).mpr hax
  rw [hz] at hh
  have hd : 2*D ∣ D*a.val := by
    apply (ZMod.natCast_eq_zero_iff (D*a.val) (2*D)).mp
    simpa only [Nat.cast_mul] using hh.symm
  obtain ⟨v,hv⟩ := hd
  have hdiv : 2 ∣ a.val := by
    refine ⟨v,?_⟩
    nlinarith only [hv,hD]
  obtain ⟨z,hz⟩ := ha
  obtain ⟨w,hw⟩ := hdiv
  omega

/-- After dividing out the primitive factor, the height and period
quotients have opposite parity whenever the actual coefficient is odd. -/
theorem odd_height_add_period_quotients_of_primitive_phase
    {F T t K H M c α r h m : ℕ} {P : ℤ}
    (hF : 0 < F) (hFt : 2*F ∣ t) (hFK : 2*F ∣ K)
    (hH : H=F*h) (hM : M=F*m) (hP : Odd P) (hr : Odd r) (hT : Odd T) (hα : Odd α)
    (hphase : (F*T : ℕ)*(α : ℤ)=P*((K : ℤ)-H)+(t : ℤ)*c+(r : ℤ)*M) : Odd (h+m) := by
  obtain ⟨u,hu⟩ := hFt
  obtain ⟨v,hv⟩ := hFK
  have htZ : (t : ℤ)=2*(F : ℤ)*u := by exact_mod_cast hu
  have hKZ : (K : ℤ)=2*(F : ℤ)*v := by exact_mod_cast hv
  have hHZ : (H : ℤ)=(F : ℤ)*h := by exact_mod_cast hH
  have hMZ : (M : ℤ)=(F : ℤ)*m := by exact_mod_cast hM
  have hdiv : (T : ℤ)*α=P*(2*(v : ℤ)-h)+2*(u : ℤ)*c+(r : ℤ)*m := by
    have hFne : (F : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hF
    apply mul_left_cancel₀ hFne
    push_cast at hphase
    linear_combination hphase+P*hKZ-P*hHZ+(c : ℤ)*htZ+(r : ℤ)*hMZ
  have hprod : Odd ((T : ℤ)*α) := by exact_mod_cast hT.mul hα
  obtain ⟨p,hp⟩ := hP
  obtain ⟨q,hq⟩ := hr
  obtain ⟨w,hw⟩ := hprod
  rw [hp,hq,hw] at hdiv
  push_cast at hdiv
  ring_nf at hdiv
  refine ⟨(h+m)/2,?_⟩
  omega

/-- Actual odd companion seeds sharpen both terminal-height cases:
equality forces one extra modulus factor of two; greater height fixes
the modulus valuation exactly at the shorter companion half-width. -/
theorem unequal_reduced_data_terminal_modulus_strata
    {a b e L n N h c V T : ℕ} [NeZero N]
    (hepos : 1 ≤ e) (he : e < a-1) (hlen : a < b) (hmax : b ≤ L)
    (hterminal : a-1-e ≤ h) (hTodd : Odd T)
    (x xa xb : ZMod N) (hindex : N.gcd x.val=2^e) (hxa : Odd xa.val)
    (hdata : UnequalCompanionReducedPrimitiveData n N (2^e) (2^(a-1-e))
      (2^(a-1)) (2^(b-1)) (2^(b-a)) T (2^L) (2^h) c V x xa xb) :
    (h=a-1-e ∧ 2^a ∣ N) ∨
      (a-1-e < h ∧ ∃ q, Odd q ∧ N=2^(a-1)*q) := by
  let f := a-1-e
  let F := 2^f
  have hfpos : 1 ≤ f := by dsimp [f]; omega
  have hprofile := unequal_reduced_data_modulus_dyadic_profile hepos (by omega) hlen hmax x xa xb hindex hdata
  have hDN : 2^e ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hNM : N=2^e*(N/2^e) := (Nat.mul_div_cancel' hDN).symm
  have hFM : F ∣ N/2^e := by
    have hh := (hprofile f (by rfl)).mpr hterminal
    rw [hNM,pow_add] at hh
    obtain ⟨m,hm⟩ := hh
    refine ⟨m,?_⟩
    have hpos := Nat.two_pow_pos e
    dsimp [F]
    nlinarith only [hm,hpos]
  obtain ⟨m,hm⟩ := hFM
  have hNfact : N=2^(a-1)*m := by
    rw [hNM,hm,← Nat.mul_assoc,show 2^e*F=2^(a-1) by dsimp [F,f]; rw [← pow_add]; congr 1; omega]
  rcases hdata with ⟨_,α,z,r,q,_,_,hα,_,_,hres,horient⟩
  have hFne : F ≠ 1 := by
    have hh : 2 ≤ F := Nat.pow_le_pow_right (by decide : 0 < 2) hfpos
    omega
  have hr : Odd r := hres.resolve_left hFne
  have h2DN : 2*2^e ∣ N := by
    have hh := (hprofile 1 (by dsimp [f] at hfpos; omega)).mpr (by omega)
    simpa only [pow_succ,Nat.mul_comm] using hh
  have hDx : 2^e ∣ x.val := by rw [← hindex]; exact Nat.gcd_dvd_right _ _
  have hαodd := odd_axis_coefficient_of_double_index_dvd_modulus (Nat.two_pow_pos e) h2DN x xa hDx hxa hα
  have hFt : 2*F ∣ 2^(b-1) := by
    have hh := Nat.pow_dvd_pow 2 (show f+1 ≤ b-1 by dsimp [f]; omega)
    simpa only [pow_succ',F] using hh
  have hFK : 2*F ∣ 2^L := by
    have hh := Nat.pow_dvd_pow 2 (show f+1 ≤ L by dsimp [f]; omega)
    simpa only [pow_succ',F] using hh
  have hH : 2^h=F*2^(h-f) := by dsimp [F]; rw [← pow_add]; congr 1; omega
  have htEven : 2 ∣ 2^(b-1) := dvd_trans (dvd_mul_right 2 F) hFt
  obtain ⟨u,hu⟩ := htEven
  have hPshort : Odd (((2^(b-1) : ℕ) : ℤ)-1) := by
    refine ⟨(u : ℤ)-1,?_⟩
    rw [hu]
    push_cast
    ring
  have hPlong : Odd (-(3*((2^(b-1) : ℕ) : ℤ)-1)) := by
    refine ⟨-3*(u : ℤ),?_⟩
    rw [hu]
    push_cast
    ring
  have hsum : Odd (2^(h-f)+m) := by
    rcases horient with ⟨_,_,_,_,hap,_,_,_⟩ | ⟨_,_,_,_,_,hap,_⟩
    · exact odd_height_add_period_quotients_of_primitive_phase (Nat.two_pow_pos f) hFt hFK hH hm
        hPshort hr hTodd hαodd hap
    · exact odd_height_add_period_quotients_of_primitive_phase (Nat.two_pow_pos f) hFt hFK hH hm
        hPlong hr hTodd hαodd hap
  by_cases heq : h=f
  · left
    have hmEven : 2 ∣ m := by
      obtain ⟨k,hk⟩ := hsum
      rw [heq,Nat.sub_self,pow_zero] at hk
      exact ⟨k,by omega⟩
    obtain ⟨k,hk⟩ := hmEven
    have hp : 2^a=2^(a-1)*2 := by rw [← pow_succ]; congr 1; omega
    exact ⟨heq,k,by rw [hNfact,hk,hp]; ring⟩
  · right
    have hpowEven : 2 ∣ 2^(h-f) := by
      simpa only [pow_one] using Nat.pow_dvd_pow 2 (show 1 ≤ h-f by omega)
    obtain ⟨k,hk⟩ := hpowEven
    obtain ⟨w,hw⟩ := hsum
    have hmOdd : Odd m := by refine ⟨w-k,?_⟩; omega
    exact ⟨by omega,m,hmOdd,hNfact⟩

/-- Actual odd companions give the three modulus alternatives below,
at, and above the terminal height whenever the primitive factor is nontrivial. -/
theorem unequal_reduced_data_modulus_trichotomy
    {a b e L n N h c V T : ℕ} [NeZero N]
    (hepos : 1 ≤ e) (he : e < a-1) (hlen : a < b) (hmax : b ≤ L)
    (hTodd : Odd T)
    (x xa xb : ZMod N) (hindex : N.gcd x.val=2^e) (hxa : Odd xa.val)
    (hdata : UnequalCompanionReducedPrimitiveData n N (2^e) (2^(a-1-e))
      (2^(a-1)) (2^(b-1)) (2^(b-a)) T (2^L) (2^h) c V x xa xb) :
    (h < a-1-e ∧ ∃ q, Odd q ∧ N=2^(e+h)*q) ∨
    (h=a-1-e ∧ 2^a ∣ N) ∨
    (a-1-e < h ∧ ∃ q, Odd q ∧ N=2^(a-1)*q) := by
  by_cases hlow : h < a-1-e
  · left
    have hh := unequal_reduced_data_modulus_stratum hepos (by omega) hlen hmax x xa xb hindex hdata
    rcases hh with hh | hh
    · exact hh
    · omega
  · right
    exact unequal_reduced_data_terminal_modulus_strata hepos he hlen hmax (by omega)
      hTodd x xa xb hindex hxa hdata

/-- Genuine maximal-even-axis unequal forests retain all previous data
and the sharper three-way stratum classification below the largest index. -/
theorem even_axis_subglobal_maximal_unequal_companion_modulus_trichotomy
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
      UnequalCompanionReducedPrimitiveData n N (2^e) (2^(L a-1-e)) s t u (4*t-u-1)
        (2^(L j)) (2^h) (2^d) (v j).val (x j) (x a) (x k) ∧
      (∀ t ≤ L a-1-e, 2^(e+t) ∣ N ↔ t ≤ h) ∧
      (e=L a-1 ∨
        (h < L a-1-e ∧ ∃ q, Odd q ∧ N=2^(e+h)*q) ∨
        (h=L a-1-e ∧ 2^(L a) ∣ N) ∨
        (L a-1-e < h ∧ ∃ q, Odd q ∧ N=2^(L a-1)*q)) := by
  obtain ⟨e,h,d,hepos,he,hindex,hnc,hbase,hgap,hcharge,hdata,hprofile⟩ :=
    even_axis_subglobal_maximal_unequal_companion_modulus_profile hn hN hr L hL
      g hg E x b hchain hgen j a k haj hkj hka hlen hmax hj hother v hv hvz hsub
  refine ⟨e,h,d,hepos,he,hindex,hnc,hbase,hgap,hcharge,hdata,hprofile,?_⟩
  by_cases heq : e=L a-1
  · exact Or.inl heq
  right
  let t := 2^(L k-1)
  let u := 2^(L k-L a)
  let u0 := 2^(L k-L a-1)
  have hu : 1 ≤ u := Nat.one_le_two_pow
  have hut : u ≤ t := Nat.pow_le_pow_right (by decide : 0 < 2) (by have := hL a; omega)
  have hU : u=2*u0 := by dsimp [u,u0]; rw [← pow_succ']; congr 1; omega
  have hTodd : Odd (4*2^(L k-1)-2^(L k-L a)-1) := by
    refine ⟨2*t-u0-1,?_⟩
    change 4*t-u-1=2*(2*t-u0-1)+1
    omega
  exact unequal_reduced_data_modulus_trichotomy hepos (by omega) hlen (hmax k) hTodd
    (x j) (x a) (x k) hindex (hother a haj) hdata

end MinModulus
