import MinModulus.ChainForestProfileEqualForest

/-! Odd equal primitive phases tie the dyadic half-profile height to
the modulus stratum. The full dyadic divisibility profile is retained
through the companion width. -/

namespace MinModulus

/-- The primitive factor divides height plus phase times period when
it divides the axis width and the companion half-width. -/
theorem equal_primitive_factor_dvd_height_add_phase_period
    {F T s K H c α r M : ℕ} (hFs : F ∣ s) (hFK : F ∣ K)
    (hphase : (F*T : ℕ)*(α : ℤ)=((s : ℤ)-1)*((K : ℤ)-H)+(s : ℤ)*c+(r : ℤ)*M) :
    F ∣ H+r*M := by
  obtain ⟨u,hu⟩ := hFs
  obtain ⟨v,hv⟩ := hFK
  have huZ : (s : ℤ)=(F : ℤ)*u := by exact_mod_cast hu
  have hvZ : (K : ℤ)=(F : ℤ)*v := by exact_mod_cast hv
  have hd : (F : ℤ) ∣ (H : ℤ)+(r : ℤ)*M := by
    refine ⟨(T : ℤ)*α-(u : ℤ)*((K : ℤ)-H+c)+v,?_⟩
    push_cast at hphase
    linear_combination -hphase-huZ*((K : ℤ)-H+c)+hvZ
  exact_mod_cast hd

/-- An odd phase preserves every power-of-two divisor up to the
primitive factor: height and period have the same truncated dyadic
valuation. -/
theorem dyadic_dvd_height_iff_dvd_period_of_odd_phase
    {f t H r M : ℕ} (ht : t ≤ f) (hr : Odd r) (hlink : 2^f ∣ H+r*M) :
    2^t ∣ H ↔ 2^t ∣ M := by
  have hd : 2^t ∣ H+r*M := dvd_trans (Nat.pow_dvd_pow 2 ht) hlink
  have hcop : Nat.Coprime (2^t) r := (hr.coprime_two_left.pow_left t)
  constructor
  · intro hH
    have hh : 2^t ∣ r*M := (Nat.dvd_add_iff_left hH).mpr (by simpa only [Nat.add_comm] using hd)
    exact hcop.dvd_of_dvd_mul_left hh
  · intro hM
    have hh : 2^t ∣ r*M := dvd_mul_of_dvd_right hM r
    exact (Nat.dvd_add_iff_right hh).mpr (by simpa only [Nat.add_comm] using hd)

/-- With dyadic height, the odd primitive phase determines every
modulus power-of-two divisibility test up to the companion width. -/
theorem equal_odd_phase_modulus_dyadic_profile
    {e f h N M F T s K c α r : ℕ}
    (hN : N=2^e*M) (hF : F=2^f) (hFs : F ∣ s) (hFK : F ∣ K) (hr : Odd r)
    (hphase : (F*T : ℕ)*(α : ℤ)=((s : ℤ)-1)*((K : ℤ)-(2^h : ℕ))+(s : ℤ)*c+(r : ℤ)*M) :
    ∀ t ≤ f, 2^(e+t) ∣ N ↔ t ≤ h := by
  have hlink := equal_primitive_factor_dvd_height_add_phase_period hFs hFK hphase
  rw [hF] at hlink
  intro t ht
  have hh := dyadic_dvd_height_iff_dvd_period_of_odd_phase ht hr hlink
  have hpow : 2^t ∣ 2^h ↔ t ≤ h := Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)
  have hcancel : 2^(e+t) ∣ N ↔ 2^t ∣ M := by
    rw [hN,pow_add]
    constructor
    · rintro ⟨v,hv⟩
      refine ⟨v,?_⟩
      have hepos := Nat.two_pow_pos e
      nlinarith only [hv,hepos]
    · rintro ⟨v,hv⟩
      refine ⟨v,?_⟩
      rw [hv]
      ring
  exact hcancel.trans (hh.symm.trans hpow)

/-- The truncated dyadic profile determines the exact modulus stratum
when the height exponent is below the primitive-factor exponent. At or
above that exponent it retains the full-width divisibility conclusion. -/
theorem modulus_stratum_of_dyadic_profile
    {e f h N : ℕ} (hprofile : ∀ t ≤ f, 2^(e+t) ∣ N ↔ t ≤ h) :
    (h < f ∧ ∃ q, Odd q ∧ N=2^(e+h)*q) ∨ (f ≤ h ∧ 2^(e+f) ∣ N) := by
  by_cases hh : h < f
  · left
    have hd : 2^(e+h) ∣ N := (hprofile h (by omega)).mpr le_rfl
    have hnot : ¬ 2^(e+(h+1)) ∣ N := by
      intro hd'
      have hc := (hprofile (h+1) (by omega)).mp hd'
      omega
    obtain ⟨q,hq⟩ := hd
    refine ⟨hh,q,?_,hq⟩
    by_contra hodd
    have heven : 2 ∣ q := even_iff_two_dvd.mp ((Nat.even_or_odd q).resolve_right hodd)
    obtain ⟨v,hv⟩ := heven
    apply hnot
    refine ⟨v,?_⟩
    simp only [hq,hv,pow_add,pow_succ]
    ring
  · right
    exact ⟨by omega,(hprofile f le_rfl).mpr (by omega)⟩

/-- Reduced primitive data below the maximal index determine the actual
modulus dyadic profile through the full companion width. -/
theorem equal_reduced_data_modulus_dyadic_profile
    {a e L n N h c V T : ℕ} [NeZero N]
    (he : 1 ≤ e) (hea : e < a) (hmax : a ≤ L)
    (x xa xb : ZMod N) (hindex : N.gcd x.val=2^e)
    (hdata : EqualCompanionReducedPrimitiveData n N (2^e) (2^(a-e)) (2^(a-1)) T
      (2^L) (2^h) c V x xa xb) :
    ∀ t ≤ a-e, 2^(e+t) ∣ N ↔ t ≤ h := by
  rcases hdata with ⟨_,_,_,α,z,r,q,_,_,_,_,_,_,_,hresidual,hap,_⟩
  have hFne : 2^(a-e) ≠ 1 := by
    have hp : 2 ≤ 2^(a-e) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ a-e)
    omega
  have hr : Odd r := hresidual.resolve_left hFne
  have hDN : 2^e ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hNM : N=2^e*(N/2^e) := (Nat.mul_div_cancel' hDN).symm
  have hFs : 2^(a-e) ∣ 2^(a-1) := Nat.pow_dvd_pow 2 (by omega)
  have hFK : 2^(a-e) ∣ 2^L := Nat.pow_dvd_pow 2 (by omega)
  exact equal_odd_phase_modulus_dyadic_profile hNM rfl hFs hFK hr hap

/-- Original genuine maximal equal-companion forests supply the modulus
profile as well as all reduced primitive data. Below the maximal index,
the half-profile height fixes every dyadic divisibility test through the
companion width, without supplied phase or stratum assumptions. -/
theorem even_axis_subglobal_maximal_equal_companion_modulus_profile
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a t : β) (haj : a ≠ j) (htj : t ≠ j) (hta : t ≠ a)
    (hlen : L a=L t) (hmax : ∀ i, L i ≤ L j)
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) (hsub : N < globalBound n) :
    let s := 2^(L a-1)
    ∃ e h d : ℕ, 1 ≤ e ∧ e ≤ L a ∧ N.gcd (x j).val=2^e ∧
      2^h+2^d ≤ n ∧ 2^h+2^d=(v j).val+1 ∧
      4*s*s*2^(L j) ≤ N+s*s*2^h ∧ 2^(Nat.log 2 n) < s*s*2^h ∧
      (EqualCompanionReducedPrimitiveData n N (2^e) (2^(L a-e)) s (2*s-1)
        (2^(L j)) (2^h) (2^d) (v j).val (x j) (x a) (x t) ∨
       EqualCompanionReducedPrimitiveData n N (2^e) (2^(L a-e)) s (2*s-1)
        (2^(L j)) (2^h) (2^d) (v j).val (x j) (x t) (x a)) ∧
      (e=L a ∨ ∀ t ≤ L a-e, 2^(e+t) ∣ N ↔ t ≤ h) := by
  classical
  dsimp only
  obtain ⟨e,h,d,hepos,hele,hindex,hnc,hbase,hgap,hcharge,hdata⟩ :=
    even_axis_subglobal_maximal_equal_companion_reduced_primitive_data hn hN hr L hL
      g hg E x b hchain hgen j a t haj htj hta hlen hmax hj hother v hv hvz hsub
  refine ⟨e,h,d,hepos,hele,hindex,hnc,hbase,hgap,hcharge,hdata,?_⟩
  by_cases heq : e=L a
  · exact Or.inl heq
  right
  have hea : e < L a := by omega
  rcases hdata with hd | hd
  · exact equal_reduced_data_modulus_dyadic_profile hepos hea (hmax a) (x j) (x a) (x t) hindex hd
  · exact equal_reduced_data_modulus_dyadic_profile hepos hea (hmax a) (x j) (x t) (x a) hindex hd

end MinModulus
