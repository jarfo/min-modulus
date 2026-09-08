import MinModulus.ChainForestProfileUnequalBasis

/-! Uniform bounded primitive phases for unequal companions. The actual
index, top and half-profile equations, dominant width and forest gap
supply both basis coefficients, their finite natural phase ranges, and
the full coupling. Targets may be signed; endpoint exclusions follow
from their signs. Arbitrary width ratios at least two are allowed.
Uniform larger coin budgets and the unrestricted conjecture remain open. -/

namespace MinModulus

/-- A signed target lying strictly between minus and plus one period
has a natural quotient phase between zero and the multiplier. Its sign
specifies which endpoint is excluded. -/
theorem exists_bounded_signed_axis_phase
    {G : Type*} [AddGroup G] {M T z : ℕ} (x : G) (C : ℤ)
    (ho : addOrderOf x=M) (hT : 0 < T) (hz : z < M)
    (hC : -(M : ℤ) < C ∧ C < M)
    (heq : (T*z) • x=C • x) :
    ∃ r : ℕ, r ≤ T ∧ (T : ℤ)*z=C+(r : ℤ)*M ∧
      (0 ≤ C → r < T) ∧ (C < 0 → 0 < r) := by
  have hMZ : (0 : ℤ) < M := by exact_mod_cast (show 0 < M by omega)
  have hnonneg : (0 : ℤ) ≤ (T : ℤ)*z := by positivity
  have hhigh : (T : ℤ)*z < (T : ℤ)*M := by
    exact_mod_cast Nat.mul_lt_mul_of_pos_left hz hT
  have heqZ : ((T : ℤ)*z) • x=C • x := by
    simpa only [← Nat.cast_mul,natCast_zsmul] using heq
  have hd : (M : ℤ) ∣ (T : ℤ)*z-C := by
    rw [← ho,addOrderOf_dvd_iff_zsmul_eq_zero]
    rw [sub_zsmul,heqZ,add_neg_cancel]
  obtain ⟨r,hr⟩ := hd
  have hr0 : 0 ≤ r := by
    by_contra hh
    have hmul := mul_le_mul_of_nonneg_left (by omega : r ≤ -1) (le_of_lt hMZ)
    nlinarith only [hr,hC.2,hnonneg,hmul]
  have hrhi : r ≤ T := by
    by_contra hh
    have hmul := mul_le_mul_of_nonneg_left (by omega : (T : ℤ)+1 ≤ r) (le_of_lt hMZ)
    nlinarith only [hr,hC.1,hhigh,hmul]
  have hrpos (hp : 0 ≤ C) : r < T := by
    by_contra hh
    have hmul := mul_le_mul_of_nonneg_left (by omega : (T : ℤ) ≤ r) (le_of_lt hMZ)
    nlinarith only [hr,hp,hhigh,hmul]
  have hrneg (hn : C < 0) : 0 < r := by
    by_contra hh
    have hzero : r=0 := by omega
    rw [hzero,mul_zero] at hr
    omega
  have hcast : (r.toNat : ℤ)=r := Int.toNat_of_nonneg hr0
  refine ⟨r.toNat,?_,?_,?_,?_⟩
  · exact_mod_cast (show (r.toNat : ℤ) ≤ T by simpa only [hcast] using hrhi)
  · rw [hcast]
    nlinarith only [hr]
  · intro hp
    exact_mod_cast (show (r.toNat : ℤ) < T by simpa only [hcast] using hrpos hp)
  · intro hn
    exact_mod_cast (show (0 : ℤ) < (r.toNat : ℤ) by simpa only [hcast] using hrneg hn)


/-- The forest gap and dominant width bound put all four signed
primitive targets inside one actual axis period. Their signs give the
endpoint exclusions needed by finite phase arguments. -/
theorem unequal_companion_signed_target_bounds
    {n t u T M K H c : ℕ}
    (hu : 2 ≤ u) (htu : 2*u ≤ t) (hT : T+u+1=4*t)
    (hH : 1 ≤ H) (hc : 0 < c) (hn : H+c ≤ n)
    (hdom : 4*t*n < K) (hperiod : 3*t*K ≤ M) :
    (0 < ((t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c ∧
      ((t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c < M) ∧
    (-(M : ℤ) < -(3*(t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c ∧
      -(3*(t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c < 0) ∧
    (-(M : ℤ) < (3-(u : ℤ))*K+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T ∧
      (3-(u : ℤ))*K+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T < M) ∧
    (0 < (3*(u : ℤ)-1)*K+((T : ℤ)-3*u+1)*H+((T : ℤ)-u-1)*c-T ∧
      (3*(u : ℤ)-1)*K+((T : ℤ)-3*u+1)*H+((T : ℤ)-u-1)*c-T < M) ∧
    (u ≤ 3 → 0 < (3-(u : ℤ))*K+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T) ∧
    (4 ≤ u → (3-(u : ℤ))*K+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T < 0) := by
  have huZ : (2 : ℤ) ≤ u := by exact_mod_cast hu
  have htuZ : 2*(u : ℤ) ≤ t := by exact_mod_cast htu
  have hTZ : (T : ℤ)+u+1=4*t := by exact_mod_cast hT
  have hHZ : (1 : ℤ) ≤ H := by exact_mod_cast hH
  have hcZ : (1 : ℤ) ≤ c := by exact_mod_cast hc
  have hnZ : (H : ℤ)+c ≤ n := by exact_mod_cast hn
  have hkZ : 4*(t : ℤ)*n < K := by exact_mod_cast hdom
  have hmZ : 3*(t : ℤ)*K ≤ M := by exact_mod_cast hperiod
  have htZ : (4 : ℤ) ≤ t := by omega
  have hnpos : (0 : ℤ) < n := by omega
  have hKpos : (0 : ℤ) < K := by exact_mod_cast (show 0 < K by omega)
  have htpos : (0 : ℤ) < t := by omega
  have hkN : (n : ℤ) ≤ K := by nlinarith only [hkZ,htZ,hnpos]
  have hkH : (H : ℤ) ≤ K := by omega
  have hMpos : (0 : ℤ) < M := by nlinarith only [hmZ,htpos,hKpos]
  have ha0 : 0 ≤ (4*((t : ℤ)-1))*((H : ℤ)-1) :=
    mul_nonneg (by omega) (by omega)
  have hb0 : 0 ≤ (4*(t : ℤ)-2*u-2)*((c : ℤ)-1) :=
    mul_nonneg (by omega) (by omega)
  have hd0 : 0 ≤ (4*((t : ℤ)-u))*((H : ℤ)-1) :=
    mul_nonneg (by omega) (by omega)
  have hrem : 0 ≤ 4*(t : ℤ)*((n : ℤ)-H-c) :=
    mul_nonneg (by positivity) (by omega)
  have huc : 0 ≤ (u : ℤ)*c := by positivity
  have huH : 0 ≤ (u : ℤ)*H := by positivity
  let A : ℤ := 4*((t : ℤ)-1)*H+(4*(t : ℤ)-2*u-2)*c-T
  let B : ℤ := 4*((t : ℤ)-u)*H+(4*(t : ℤ)-2*u-2)*c-T
  have hA : 0 < A ∧ A < 4*(t : ℤ)*n := by
    dsimp [A]
    constructor
    · nlinarith only [ha0,hb0,hTZ,htuZ,huZ]
    · nlinarith only [hrem,huc,hHZ,hcZ,hTZ,htuZ,huZ]
  have hB : 0 < B ∧ B < 4*(t : ℤ)*n := by
    dsimp [B]
    constructor
    · nlinarith only [hd0,hb0,hTZ,htuZ,huZ]
    · nlinarith only [hrem,huc,huH,hcZ,hTZ,htuZ,huZ]
  have hshort : (3-(u : ℤ))*K+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T =
      (3-(u : ℤ))*K+A := by dsimp [A]; nlinarith only [hTZ]
  have hlong : (3*(u : ℤ)-1)*K+((T : ℤ)-3*u+1)*H+((T : ℤ)-u-1)*c-T =
      (3*(u : ℤ)-1)*K+B := by dsimp [B]; nlinarith only [hTZ]
  have htc : 0 < (t : ℤ)*c := mul_pos htpos (by omega)
  have hKH : 0 ≤ ((t : ℤ)-1)*((K : ℤ)-H) := mul_nonneg (by omega) (by omega)
  have hH0 : 0 ≤ ((t : ℤ)-1)*H := mul_nonneg (by omega) (by omega)
  have hcn : 0 ≤ (t : ℤ)*((n : ℤ)-c) := mul_nonneg (by omega) (by omega)
  have hnK : 0 ≤ (t : ℤ)*((K : ℤ)-n) := mul_nonneg (by omega) (by omega)
  have htK : 0 < (t : ℤ)*K := mul_pos htpos hKpos
  have hLH : 0 ≤ (3*(t : ℤ)-1)*H := mul_nonneg (by omega) (by omega)
  have hLrem : 0 ≤ (3*(t : ℤ))*((n : ℤ)-H-c) := mul_nonneg (by omega) (by omega)
  have hLK : 0 ≤ (3*(t : ℤ)-2)*K := mul_nonneg (by omega) (by omega)
  have huK : 0 ≤ ((u : ℤ)-2)*K := mul_nonneg (by omega) (by omega)
  have htuK : 0 ≤ ((t : ℤ)-2*u)*K := mul_nonneg (by omega) (by omega)
  have hutK : 0 ≤ (3*(t : ℤ)-u+3)*K := mul_nonneg (by omega) (by omega)
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,?_,?_⟩
  · nlinarith only [hKH,htc]
  · nlinarith only [hH0,hcn,hnK,htK,hmZ,hKpos]
  · nlinarith only [hLH,htc,hmZ,hKpos]
  · nlinarith only [hLrem,hLK,htc,hHZ,hkZ]
  · rw [hshort]
    nlinarith only [hA.1,hutK,hmZ]
  · rw [hshort]
    nlinarith only [hA.2,hkZ,huK,htK,hmZ,htZ,hKpos]
  · rw [hlong]
    nlinarith only [hB.1,huK,hKpos]
  · rw [hlong]
    nlinarith only [hB.2,hkZ,htuK,huK,hmZ,hKpos]
  · intro hh
    have hhZ : (u : ℤ) ≤ 3 := by exact_mod_cast hh
    have hprod : 0 ≤ (3-(u : ℤ))*K := mul_nonneg (by omega) (by omega)
    rw [hshort]
    linarith [hA.1]
  · intro hh
    have hhZ : (4 : ℤ) ≤ u := by exact_mod_cast hh
    have hprod : 0 ≤ ((u : ℤ)-4)*K := mul_nonneg (by omega) (by omega)
    rw [hshort]
    nlinarith only [hprod,hA.2,hkZ]


/-- Dividing the forest gap by the actual index gives the period
bound needed by the uniform signed targets. -/
theorem unequal_companion_gap_period_bound
    {n D F s t M K H c : ℕ}
    (hs : 2 ≤ s) (ht : 1 ≤ t) (hDF : D*F=s)
    (hH : 1 ≤ H) (hc : 0 < c) (hn : H+c ≤ n)
    (hdom : n*(4*s*t+1) ≤ K)
    (hgap : 4*s*t*K ≤ D*M+s*t*H) : 4*t*n < K ∧ 3*t*K ≤ M := by
  have hD : 0 < D := by
    by_contra hh
    have hz : D=0 := by omega
    simp only [hz,Nat.zero_mul] at hDF
    omega
  have hF : 1 ≤ F := by
    by_contra hh
    have hz : F=0 := by omega
    simp only [hz,Nat.mul_zero] at hDF
    omega
  have hn0 : 0 < n := by omega
  have hsmall := Nat.mul_le_mul_right (4*t*n) (show 1 ≤ s by omega)
  have hdom' : 4*t*n < K := by nlinarith only [hdom,hsmall,hn0]
  have hnK : n ≤ K := by nlinarith only [hdom',ht,hn0]
  have hHK : H ≤ K := by omega
  have hgap' : D*(4*F*t*K) ≤ D*(M+F*t*H) := by
    rw [← hDF] at hgap
    nlinarith only [hgap]
  have hgap'' := Nat.le_of_mul_le_mul_left hgap' hD
  have hHK' := Nat.mul_le_mul_left (F*t) hHK
  have hF' := Nat.mul_le_mul_right (3*t*K) hF
  exact ⟨hdom',by nlinarith only [hgap'',hHK',hF']⟩

/-- Original top and short half relations, the actual index and the
forest gap supply bounded primitive phases with their full coupling.
No phase, sign or coprimality hypothesis is required. -/
theorem exists_unequal_companion_short_bounded_primitive_phases
    {n N D F s t u T K H c V : ℕ} [NeZero N] [NeZero D]
    (hs : 2 ≤ s) (hu : 2 ≤ u) (hDF : D*F=s) (htu : t=s*u)
    (hT : T+u+1=4*t) (hH : 1 ≤ H) (hc : 0 < c)
    (hn : H+c ≤ n) (hbase : H+c=V+1)
    (hdom : n*(4*s*t+1) ≤ K) (hgap : 4*s*t*K ≤ N+s*t*H)
    (x a b : ZMod N) (hindex : N.gcd x.val=D)
    (htop : (K-1) • x+(2*s-1) • a+(2*t-1) • b=V • x)
    (hhalf : (3*s-1) • a+(t-1) • b=c • x) :
    ∃ α z r q : ℕ, α < N/D ∧ z < N/D ∧
      α • x=D • a ∧ z • x+a+b=V • x ∧
      r < F*T ∧ q ≤ T ∧
      (F*T : ℕ)*(α : ℤ)=((t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c+(r : ℤ)*(N/D : ℕ) ∧
      (T : ℤ)*z=(3-(u : ℤ))*K+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*(N/D : ℕ) ∧
      T ∣ 4*r+q ∧
      (u ≤ 3 → q < T) ∧ (4 ≤ u → 1 ≤ q) := by
  have ht : 1 ≤ t := by nlinarith only [htu,hs,hu]
  have htu2 : 2*u ≤ t := by nlinarith only [htu,hs,hu]
  have hF : 0 < F := by
    by_contra hh
    have hz : F=0 := by omega
    simp only [hz,Nat.mul_zero] at hDF
    omega
  have hTpos : 0 < T := by omega
  have hK : 1 ≤ K := by
    have hh := Nat.le_mul_of_pos_right n (show 0 < 4*s*t+1 by omega)
    omega
  have hDN : D ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hNM : D*(N/D)=N := Nat.mul_div_cancel' hDN
  obtain ⟨hdom',hperiod⟩ := unequal_companion_gap_period_bound hs ht hDF hH hc hn hdom
    (show 4*s*t*K ≤ D*(N/D)+s*t*H by simpa only [hNM] using hgap)
  obtain ⟨hAS,hAL,hZS,hZL,hZSpos,hZSneg⟩ :=
    unequal_companion_signed_target_bounds hu htu2 hT hH hc hn hdom' hperiod
  obtain ⟨α,hαlt,hα⟩ := exists_companion_multiple_axis_coefficient x a hindex
  have hDA : D ∣ 2*s := dvd_mul_of_dvd_right (by rw [← hDF]; exact dvd_mul_right D F) 2
  have hDB : D ∣ 2*t := by rw [htu]; simpa only [Nat.mul_assoc] using dvd_mul_of_dvd_left hDA u
  obtain ⟨z,hzlt,hz⟩ := exists_one_each_axis_coefficient_of_companion_widths
    (by omega : 1 ≤ 2*s) (by omega : 1 ≤ 2*t) hDA hDB x a b hindex htop
  have ho : addOrderOf x=N/D := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hM : 0 < N/D := by omega
  have hMZ : (0 : ℤ) < (N/D : ℕ) := by exact_mod_cast hM
  have haeq := unequal_companion_short_axis_multiple_relation (by omega : 1 ≤ s) ht hK
    hDF htu hT hbase x a b hα htop hhalf
  have hzeq := unequal_companion_short_one_each_relation (by omega : 1 ≤ s) ht hK
    htu hT hbase x a b hz htop hhalf
  obtain ⟨r,hr,hrphase,hrpos,hrneg⟩ := exists_bounded_signed_axis_phase x
    (((t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c) ho (Nat.mul_pos hF hTpos) hαlt
    (by constructor <;> linarith [hAS.1,hAS.2])
    (by simpa only [Nat.mul_assoc] using haeq)
  obtain ⟨q,hq,hqphase,hqpos,hqneg⟩ := exists_bounded_signed_axis_phase x
    ((3-(u : ℤ))*K+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T) ho hTpos hzlt
    (by constructor <;> linarith [hZS.1,hZS.2]) hzeq
  have hlink := unequal_companion_short_primitive_phase_coupling
    (by omega : 1 ≤ s) ht hK hM hDF hT hbase hrphase hqphase x a b ho hα hz htop hhalf
  have hlinkN : T ∣ 4*r+q := by exact_mod_cast hlink
  exact ⟨α,z,r,q,hαlt,hzlt,hα,hz,hrpos (le_of_lt hAS.1),hq,
    hrphase,hqphase,hlinkN,fun hh ↦ hqpos (le_of_lt (hZSpos hh)),
    fun hh ↦ hqneg (hZSneg hh)⟩

/-- Original top and long half relations, the actual index and the
forest gap supply bounded primitive phases with their full coupling.
No phase, sign or coprimality hypothesis is required. -/
theorem exists_unequal_companion_long_bounded_primitive_phases
    {n N D F s t u T K H c V : ℕ} [NeZero N] [NeZero D]
    (hs : 2 ≤ s) (hu : 2 ≤ u) (hDF : D*F=s) (htu : t=s*u)
    (hT : T+u+1=4*t) (hH : 1 ≤ H) (hc : 0 < c)
    (hn : H+c ≤ n) (hbase : H+c=V+1)
    (hdom : n*(4*s*t+1) ≤ K) (hgap : 4*s*t*K ≤ N+s*t*H)
    (x a b : ZMod N) (hindex : N.gcd x.val=D)
    (htop : (K-1) • x+(2*s-1) • a+(2*t-1) • b=V • x)
    (hhalf : (s-1) • a+(3*t-1) • b=c • x) :
    ∃ α z r q : ℕ, α < N/D ∧ z < N/D ∧
      α • x=D • a ∧ z • x+a+b=V • x ∧
      1 ≤ r ∧ r ≤ F*T ∧ q < T ∧
      (F*T : ℕ)*(α : ℤ)=-(3*(t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c+(r : ℤ)*(N/D : ℕ) ∧
      (T : ℤ)*z=(3*(u : ℤ)-1)*K+((T : ℤ)-3*u+1)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*(N/D : ℕ) ∧
      T ∣ 4*r+q := by
  have ht : 1 ≤ t := by nlinarith only [htu,hs,hu]
  have htu2 : 2*u ≤ t := by nlinarith only [htu,hs,hu]
  have hF : 0 < F := by
    by_contra hh
    have hz : F=0 := by omega
    simp only [hz,Nat.mul_zero] at hDF
    omega
  have hTpos : 0 < T := by omega
  have hK : 1 ≤ K := by
    have hh := Nat.le_mul_of_pos_right n (show 0 < 4*s*t+1 by omega)
    omega
  have hDN : D ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hNM : D*(N/D)=N := Nat.mul_div_cancel' hDN
  obtain ⟨hdom',hperiod⟩ := unequal_companion_gap_period_bound hs ht hDF hH hc hn hdom
    (show 4*s*t*K ≤ D*(N/D)+s*t*H by simpa only [hNM] using hgap)
  obtain ⟨hAS,hAL,hZS,hZL,hZSpos,hZSneg⟩ :=
    unequal_companion_signed_target_bounds hu htu2 hT hH hc hn hdom' hperiod
  obtain ⟨α,hαlt,hα⟩ := exists_companion_multiple_axis_coefficient x a hindex
  have hDA : D ∣ 2*s := dvd_mul_of_dvd_right (by rw [← hDF]; exact dvd_mul_right D F) 2
  have hDB : D ∣ 2*t := by rw [htu]; simpa only [Nat.mul_assoc] using dvd_mul_of_dvd_left hDA u
  obtain ⟨z,hzlt,hz⟩ := exists_one_each_axis_coefficient_of_companion_widths
    (by omega : 1 ≤ 2*s) (by omega : 1 ≤ 2*t) hDA hDB x a b hindex htop
  have ho : addOrderOf x=N/D := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hM : 0 < N/D := by omega
  have hMZ : (0 : ℤ) < (N/D : ℕ) := by exact_mod_cast hM
  have haeq := unequal_companion_long_axis_multiple_relation (by omega : 1 ≤ s) ht hK
    hDF htu hT hbase x a b hα htop hhalf
  have hzeq := unequal_companion_long_one_each_relation (by omega : 1 ≤ s) ht hK
    htu hT hbase x a b hz htop hhalf
  obtain ⟨r,hr,hrphase,hrpos,hrneg⟩ := exists_bounded_signed_axis_phase x
    (-(3*(t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c) ho (Nat.mul_pos hF hTpos) hαlt
    (by constructor <;> linarith [hAL.1,hAL.2])
    (by simpa only [Nat.mul_assoc] using haeq)
  obtain ⟨q,hq,hqphase,hqpos,hqneg⟩ := exists_bounded_signed_axis_phase x
    ((3*(u : ℤ)-1)*K+((T : ℤ)-3*u+1)*H+((T : ℤ)-u-1)*c-T) ho hTpos hzlt
    (by constructor <;> linarith [hZL.1,hZL.2]) hzeq
  have hlink := unequal_companion_long_primitive_phase_coupling
    (by omega : 1 ≤ s) ht hK hM hDF hT hbase hrphase hqphase x a b ho hα hz htop hhalf
  have hlinkN : T ∣ 4*r+q := by exact_mod_cast hlink
  exact ⟨α,z,r,q,hαlt,hzlt,hα,hz,hrneg hAL.2,hr,hqpos (le_of_lt hZL.1),
    hrphase,hqphase,hlinkN⟩

end MinModulus
