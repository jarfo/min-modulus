import MinModulus.ChainForestProfileUnequalEven

/-! Actual unequal primitive phases determine the complete truncated
modulus divisibility profile through the shorter companion half-width.
Both orientations and the largest possible index are included. -/

namespace MinModulus

/-- The long half orientation gives height minus phase times period,
with the same primitive-factor divisibility as the short orientation. -/
theorem unequal_long_primitive_factor_dvd_height_sub_phase_period
    {F T t K H c α r M : ℕ} (hFt : F ∣ t) (hFK : F ∣ K)
    (hphase : (F*T : ℕ)*(α : ℤ)=-(3*(t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c+(r : ℤ)*M) :
    (F : ℤ) ∣ (H : ℤ)-(r : ℤ)*M := by
  obtain ⟨u,hu⟩ := hFt
  obtain ⟨v,hv⟩ := hFK
  have htZ : (t : ℤ)=(F : ℤ)*u := by exact_mod_cast hu
  have hKZ : (K : ℤ)=(F : ℤ)*v := by exact_mod_cast hv
  refine ⟨(v : ℤ)-3*(u : ℤ)*((K : ℤ)-H)+(u : ℤ)*c-(T : ℤ)*α,?_⟩
  push_cast at hphase
  linear_combination hphase+hKZ+((c : ℤ)-3*((K : ℤ)-H))*htZ

/-- Reversing the sign of an odd phase leaves the entire truncated
height-period dyadic divisibility profile unchanged. -/
theorem dyadic_dvd_height_iff_dvd_period_of_odd_sub_phase
    {f t H r M : ℕ} (ht : t ≤ f) (hr : Odd r)
    (hlink : ((2^f : ℕ) : ℤ) ∣ (H : ℤ)-(r : ℤ)*M) :
    2^t ∣ H ↔ 2^t ∣ M := by
  have hpow : ((2^t : ℕ) : ℤ) ∣ ((2^f : ℕ) : ℤ) := by exact_mod_cast Nat.pow_dvd_pow 2 ht
  obtain ⟨l,hl⟩ := dvd_trans hpow hlink
  have hcop : Nat.Coprime (2^t) r := hr.coprime_two_left.pow_left t
  constructor
  · rintro ⟨h,hh⟩
    have hHZ : (H : ℤ)=(2^t : ℕ)*(h : ℤ) := by exact_mod_cast hh
    have hd : ((2^t : ℕ) : ℤ) ∣ (r : ℤ)*M := by
      refine ⟨(h : ℤ)-l,?_⟩
      linear_combination hHZ-hl
    have hdNat : 2^t ∣ r*M := by exact_mod_cast hd
    exact hcop.dvd_of_dvd_mul_left hdNat
  · rintro ⟨m,hm⟩
    have hMZ : (M : ℤ)=(2^t : ℕ)*(m : ℤ) := by exact_mod_cast hm
    have hd : ((2^t : ℕ) : ℤ) ∣ (H : ℤ) := by
      refine ⟨l+(r : ℤ)*m,?_⟩
      linear_combination hl+(r : ℤ)*hMZ
    exact_mod_cast hd

/-- Odd long-orientation phases determine all modulus divisibility
levels up to the dyadic primitive factor. -/
theorem unequal_long_odd_phase_modulus_dyadic_profile
    {e f h N M F T t K c α r : ℕ}
    (hN : N=2^e*M) (hF : F=2^f) (hFt : F ∣ t) (hFK : F ∣ K) (hr : Odd r)
    (hphase : (F*T : ℕ)*(α : ℤ)=-(3*(t : ℤ)-1)*((K : ℤ)-(2^h : ℕ))+(t : ℤ)*c+(r : ℤ)*M) :
    ∀ j ≤ f, 2^(e+j) ∣ N ↔ j ≤ h := by
  have hlink := unequal_long_primitive_factor_dvd_height_sub_phase_period hFt hFK hphase
  rw [hF] at hlink
  intro j hj
  have hh := dyadic_dvd_height_iff_dvd_period_of_odd_sub_phase hj hr hlink
  have hpow : 2^j ∣ 2^h ↔ j ≤ h := Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)
  have hcancel : 2^(e+j) ∣ N ↔ 2^j ∣ M := by
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

/-- Actual reduced unequal data give the complete truncated modulus
profile through the shorter companion half-width, in either orientation.
At the largest possible index the profile consists of its zeroth level. -/
theorem unequal_reduced_data_modulus_dyadic_profile
    {a b e L n N h c V T : ℕ} [NeZero N]
    (hepos : 1 ≤ e) (he : e < a) (hlen : a < b) (hmax : b ≤ L)
    (x xa xb : ZMod N) (hindex : N.gcd x.val=2^e)
    (hdata : UnequalCompanionReducedPrimitiveData n N (2^e) (2^(a-1-e))
      (2^(a-1)) (2^(b-1)) (2^(b-a)) T (2^L) (2^h) c V x xa xb) :
    ∀ j ≤ a-1-e, 2^(e+j) ∣ N ↔ j ≤ h := by
  have hDN : 2^e ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hNM : N=2^e*(N/2^e) := (Nat.mul_div_cancel' hDN).symm
  by_cases hf : a-1-e=0
  · intro j hj
    have hj0 : j=0 := by omega
    simp only [hj0,Nat.add_zero,Nat.zero_le,iff_true]
    exact hDN
  rcases hdata with ⟨_,α,z,r,q,_,_,_,_,_,hresidual,horient⟩
  have hFne : 2^(a-1-e) ≠ 1 := by
    have hp : 2 ≤ 2^(a-1-e) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ a-1-e)
    omega
  have hr : Odd r := hresidual.resolve_left hFne
  have hFt : 2^(a-1-e) ∣ 2^(b-1) := Nat.pow_dvd_pow 2 (by omega)
  have hFK : 2^(a-1-e) ∣ 2^L := Nat.pow_dvd_pow 2 (by omega)
  rcases horient with ⟨_,_,_,_,hap,_,_,_⟩ | ⟨_,_,_,_,_,hap,_⟩
  · exact equal_odd_phase_modulus_dyadic_profile hNM rfl hFt hFK hr hap
  · exact unequal_long_odd_phase_modulus_dyadic_profile hNM rfl hFt hFK hr hap

/-- The unequal profile fixes the exact stratum below its terminal
height, and otherwise retains divisibility by the short half-width. -/
theorem unequal_reduced_data_modulus_stratum
    {a b e L n N h c V T : ℕ} [NeZero N]
    (hepos : 1 ≤ e) (he : e < a) (hlen : a < b) (hmax : b ≤ L)
    (x xa xb : ZMod N) (hindex : N.gcd x.val=2^e)
    (hdata : UnequalCompanionReducedPrimitiveData n N (2^e) (2^(a-1-e))
      (2^(a-1)) (2^(b-1)) (2^(b-a)) T (2^L) (2^h) c V x xa xb) :
    (h < a-1-e ∧ ∃ q, Odd q ∧ N=2^(e+h)*q) ∨
      (a-1-e ≤ h ∧ 2^(a-1) ∣ N) := by
  have hp := unequal_reduced_data_modulus_dyadic_profile hepos he hlen hmax x xa xb hindex hdata
  have hh := modulus_stratum_of_dyadic_profile hp
  simpa only [show e+(a-1-e)=a-1 by omega] using hh

/-- Original genuine unequal forests determine every modulus dyadic
level through the shorter half-width, retaining all reduced data. The
largest-index case is included without an odd-phase assumption. -/
theorem even_axis_subglobal_maximal_unequal_companion_modulus_profile
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
      (∀ t ≤ L a-1-e, 2^(e+t) ∣ N ↔ t ≤ h) := by
  obtain ⟨e,h,d,hepos,he,hindex,hnc,hbase,hgap,hcharge,hdata⟩ :=
    even_axis_subglobal_maximal_unequal_companion_reduced_primitive_data hn hN hr L hL
      g hg E x b hchain hgen j a k haj hkj hka hlen hmax hj hother v hv hvz hsub
  exact ⟨e,h,d,hepos,he,hindex,hnc,hbase,hgap,hcharge,hdata,
    unequal_reduced_data_modulus_dyadic_profile hepos he hlen (hmax k)
      (x j) (x a) (x k) hindex hdata⟩

end MinModulus
