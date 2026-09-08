import MinModulus.ChainForestProfileThreeFive

/-! Uniform primitive algebra for arbitrary unequal companion widths.
Both half-profile orientations give signed index-times-companion and
one-each relations. Combining the original top and half relations gives
the full primitive phase coupling, even for signed phases and without
any coprime assumption on a companion weight, denominator or period.
The factor and ratio relations are explicit, and binary widths are a
special case. Uniform larger coin budgets and the global conjecture
remain open. -/

namespace MinModulus

/-- The primitive index-times-companion relation for an arbitrary
unequal-width short half profile. The target coefficient is signed. -/
theorem unequal_companion_short_axis_multiple_relation
    {N D F s t u T K H c V α : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) (hK : 1 ≤ K)
    (hDF : D*F=s) (htu : t=s*u) (hT : T+u+1=4*t) (hbase : H+c=V+1)
    (x a b : ZMod N) (hα : α • x=D • a)
    (htop : (K-1) • x+(2*s-1) • a+(2*t-1) • b=V • x)
    (hhalf : (3*s-1) • a+(t-1) • b=c • x) :
    (F*T*α) • x=(((t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c) • x := by
  have h2s : 1 ≤ 2*s := by omega
  have h3s : 1 ≤ 3*s := by omega
  have h2t : 1 ≤ 2*t := by omega
  have h3t : 1 ≤ 3*t := by omega
  have hDcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) hDF
  have htcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) htu
  have hTcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) hT
  have hbcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) hbase
  push_cast at hDcast htcast hTcast hbcast
  simp only [nsmul_eq_mul,zsmul_eq_mul,Nat.cast_sub hK,Nat.cast_sub h2s,
    Nat.cast_sub h3s,Nat.cast_sub h2t,
    Nat.cast_sub ht,Nat.cast_one] at hα htop hhalf ⊢
  push_cast at hα htop hhalf ⊢
  linear_combination (F : ZMod N)*T*hα-((t : ZMod N)-1)*htop+(2*(t : ZMod N)-1)*hhalf+((t : ZMod N)-1)*hbcast*x+
    (T : ZMod N)*hDcast*a+(s : ZMod N)*hTcast*a+htcast*a

/-- The one-each coefficient has a uniform signed short phase
for arbitrary unequal binary companion widths. -/
theorem unequal_companion_short_one_each_relation
    {N s t u T K H c V z : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) (hK : 1 ≤ K)
    (htu : t=s*u) (hT : T+u+1=4*t) (hbase : H+c=V+1)
    (x a b : ZMod N) (hz : z • x+a+b=V • x)
    (htop : (K-1) • x+(2*s-1) • a+(2*t-1) • b=V • x)
    (hhalf : (3*s-1) • a+(t-1) • b=c • x) :
    (T*z) • x=((3-(u : ℤ))*K+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T) • x := by
  have h2s : 1 ≤ 2*s := by omega
  have h3s : 1 ≤ 3*s := by omega
  have h2t : 1 ≤ 2*t := by omega
  have h3t : 1 ≤ 3*t := by omega
  have htcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) htu
  have hTcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) hT
  have hbcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) hbase
  push_cast at htcast hTcast hbcast
  simp only [nsmul_eq_mul,zsmul_eq_mul,Nat.cast_sub hK,Nat.cast_sub h2s,
    Nat.cast_sub h3s,Nat.cast_sub h2t,
    Nat.cast_sub ht,Nat.cast_one] at hz htop hhalf ⊢
  push_cast at hz htop hhalf ⊢
  linear_combination (T : ZMod N)*hz-(3-(u : ZMod N))*htop-(2*(u : ZMod N)-2)*hhalf-
    ((T : ZMod N)-(3-(u : ZMod N)))*hbcast*x-hTcast*(a+b)-4*htcast*a

/-- The primitive index-times-companion relation for an arbitrary
unequal-width long half profile. The target coefficient is signed. -/
theorem unequal_companion_long_axis_multiple_relation
    {N D F s t u T K H c V α : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) (hK : 1 ≤ K)
    (hDF : D*F=s) (htu : t=s*u) (hT : T+u+1=4*t) (hbase : H+c=V+1)
    (x a b : ZMod N) (hα : α • x=D • a)
    (htop : (K-1) • x+(2*s-1) • a+(2*t-1) • b=V • x)
    (hhalf : (s-1) • a+(3*t-1) • b=c • x) :
    (F*T*α) • x=(-(3*(t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c) • x := by
  have h2s : 1 ≤ 2*s := by omega
  have h3s : 1 ≤ 3*s := by omega
  have h2t : 1 ≤ 2*t := by omega
  have h3t : 1 ≤ 3*t := by omega
  have hDcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) hDF
  have htcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) htu
  have hTcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) hT
  have hbcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) hbase
  push_cast at hDcast htcast hTcast hbcast
  simp only [nsmul_eq_mul,zsmul_eq_mul,Nat.cast_sub hK,Nat.cast_sub h2s,
    Nat.cast_sub h2t,Nat.cast_sub h3t,Nat.cast_sub hs,
    Nat.cast_one] at hα htop hhalf ⊢
  push_cast at hα htop hhalf ⊢
  linear_combination (F : ZMod N)*T*hα+(3*(t : ZMod N)-1)*htop-(2*(t : ZMod N)-1)*hhalf-(3*(t : ZMod N)-1)*hbcast*x+
    (T : ZMod N)*hDcast*a+(s : ZMod N)*hTcast*a+htcast*a

/-- The one-each coefficient has a uniform signed long phase
for arbitrary unequal binary companion widths. -/
theorem unequal_companion_long_one_each_relation
    {N s t u T K H c V z : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) (hK : 1 ≤ K)
    (htu : t=s*u) (hT : T+u+1=4*t) (hbase : H+c=V+1)
    (x a b : ZMod N) (hz : z • x+a+b=V • x)
    (htop : (K-1) • x+(2*s-1) • a+(2*t-1) • b=V • x)
    (hhalf : (s-1) • a+(3*t-1) • b=c • x) :
    (T*z) • x=((3*(u : ℤ)-1)*K+((T : ℤ)-3*u+1)*H+((T : ℤ)-u-1)*c-T) • x := by
  have h2s : 1 ≤ 2*s := by omega
  have h3s : 1 ≤ 3*s := by omega
  have h2t : 1 ≤ 2*t := by omega
  have h3t : 1 ≤ 3*t := by omega
  have htcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) htu
  have hTcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) hT
  have hbcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) hbase
  push_cast at htcast hTcast hbcast
  simp only [nsmul_eq_mul,zsmul_eq_mul,Nat.cast_sub hK,Nat.cast_sub h2s,
    Nat.cast_sub h2t,Nat.cast_sub h3t,Nat.cast_sub hs,
    Nat.cast_one] at hz htop hhalf ⊢
  push_cast at hz htop hhalf ⊢
  linear_combination (T : ZMod N)*hz-(3*(u : ZMod N)-1)*htop-(2-2*(u : ZMod N))*hhalf-
    ((T : ZMod N)-(3*(u : ZMod N)-1))*hbcast*x-hTcast*(a+b)-4*htcast*a


/-- Combining the top and short half relations gives the full
primitive phase coupling, without any coprime assumption on a weight,
the phase denominator, or the actual period. Signed phases are allowed. -/
theorem unequal_companion_short_primitive_phase_coupling
    {N D F s t u T M K H c V z α : ℕ} {r q : ℤ}
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hK : 1 ≤ K) (hM : 0 < M)
    (hDF : D*F=s) (hT : T+u+1=4*t) (_hbase : H+c=V+1)
    (hαphase : (F*T : ℕ)*(α : ℤ)=((t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c+r*M)
    (hzphase : (T : ℤ)*z=(3-(u : ℤ))*K+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T+q*M)
    (x a b : ZMod N) (ho : addOrderOf x=M)
    (hα : α • x=D • a) (hz : z • x+a+b=V • x)
    (htop : (K-1) • x+(2*s-1) • a+(2*t-1) • b=V • x)
    (hhalf : (3*s-1) • a+(t-1) • b=c • x) : (T : ℤ) ∣ 4*r+q := by
  let Y : ℤ := 4*F*α+z-K+1-2*c
  have hY : Y • x=0 := by
    have h2s : 1 ≤ 2*s := by omega
    have h3s : 1 ≤ 3*s := by omega
    have h2t : 1 ≤ 2*t := by omega
    have h3t : 1 ≤ 3*t := by omega
    have hDcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) hDF
    push_cast at hDcast
    simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_sub h2s,Nat.cast_sub h2t,
      Nat.cast_sub h3s,Nat.cast_sub ht,Nat.cast_one] at hα hz htop hhalf
    simp only [Y,zsmul_eq_mul]
    push_cast at hα hz htop hhalf ⊢
    linear_combination 4*(F : ZMod N)*hα+hz-htop+2*hhalf+4*hDcast*a
  have hd : (M : ℤ) ∣ Y := by
    rw [← ho,addOrderOf_dvd_iff_zsmul_eq_zero]
    exact hY
  obtain ⟨p,hp⟩ := hd
  have hTZ : (T : ℤ)+u+1=4*t := by exact_mod_cast hT
  have hscalar : (T : ℤ)*Y=(4*r+q)*M := by
    dsimp [Y]
    push_cast at hαphase
    linear_combination 4*hαphase+hzphase-hTZ*((K : ℤ)-H+c)
  have heq : (4*r+q)*(M : ℤ)=((T : ℤ)*p)*M := by
    rw [hp] at hscalar
    linear_combination -hscalar
  have hMne : (M : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  exact ⟨p,mul_right_cancel₀ hMne heq⟩

/-- Combining the top and long half relations gives the full
primitive phase coupling, without any coprime assumption on a weight,
the phase denominator, or the actual period. Signed phases are allowed. -/
theorem unequal_companion_long_primitive_phase_coupling
    {N D F s t u T M K H c V z α : ℕ} {r q : ℤ}
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hK : 1 ≤ K) (hM : 0 < M)
    (hDF : D*F=s) (hT : T+u+1=4*t) (hbase : H+c=V+1)
    (hαphase : (F*T : ℕ)*(α : ℤ)=-(3*(t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c+r*M)
    (hzphase : (T : ℤ)*z=(3*(u : ℤ)-1)*K+((T : ℤ)-3*u+1)*H+((T : ℤ)-u-1)*c-T+q*M)
    (x a b : ZMod N) (ho : addOrderOf x=M)
    (hα : α • x=D • a) (hz : z • x+a+b=V • x)
    (htop : (K-1) • x+(2*s-1) • a+(2*t-1) • b=V • x)
    (hhalf : (s-1) • a+(3*t-1) • b=c • x) : (T : ℤ) ∣ 4*r+q := by
  let Y : ℤ := 4*F*α+z+3*K-3-4*V+2*c
  have hY : Y • x=0 := by
    have h2s : 1 ≤ 2*s := by omega
    have h3s : 1 ≤ 3*s := by omega
    have h2t : 1 ≤ 2*t := by omega
    have h3t : 1 ≤ 3*t := by omega
    have hDcast := congrArg (fun n : ℕ ↦ (n : ZMod N)) hDF
    push_cast at hDcast
    simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_sub h2s,Nat.cast_sub h2t,
      Nat.cast_sub hs,Nat.cast_sub h3t,Nat.cast_one] at hα hz htop hhalf
    simp only [Y,zsmul_eq_mul]
    push_cast at hα hz htop hhalf ⊢
    linear_combination 4*(F : ZMod N)*hα+hz+3*htop-2*hhalf+4*hDcast*a
  have hd : (M : ℤ) ∣ Y := by
    rw [← ho,addOrderOf_dvd_iff_zsmul_eq_zero]
    exact hY
  obtain ⟨p,hp⟩ := hd
  have hTZ : (T : ℤ)+u+1=4*t := by exact_mod_cast hT
  have hbZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hscalar : (T : ℤ)*Y=(4*r+q)*M := by
    dsimp [Y]
    push_cast at hαphase
    linear_combination 4*hαphase+hzphase+4*(T : ℤ)*hbZ+hTZ*(3*(K : ℤ)-3*H-c)
  have heq : (4*r+q)*(M : ℤ)=((T : ℤ)*p)*M := by
    rw [hp] at hscalar
    linear_combination -hscalar
  have hMne : (M : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  exact ⟨p,mul_right_cancel₀ hMne heq⟩

end MinModulus
