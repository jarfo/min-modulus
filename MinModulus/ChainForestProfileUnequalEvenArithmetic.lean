import MinModulus.ChainForestProfileEqualUniform

/-! Every even unequal primitive phase below the largest possible index
realizes the midpoint of the top and half profiles. Both orientations
have an affordable actual rival uniformly in the companion lengths. -/

namespace MinModulus

/-- Compatible primitive phases realize the midpoint of the top and half
profiles whenever the signed period coefficient is integral. -/
theorem primitive_midpoint_rival_twice
    {G T K H c V M α z tb t v : ℕ} {P Q r q τ ν : ℤ}
    (hT : 0 < T) (hbase : H+c=V+1)
    (hap : (2*G*T : ℕ)*(α : ℤ)=P*((K : ℤ)-H)+(t : ℤ)*c+r*M)
    (hzp : (T : ℤ)*z=Q*K+((T : ℤ)-Q)*H+((T : ℤ)-v)*c-T+q*M)
    (hlead : 2*(tb : ℤ)*Q-τ*P=T)
    (hdrop : 2*(tb : ℤ)*v+τ*t=2*T)
    (hphase : 2*(tb : ℤ)*q-τ*r=2*(T : ℤ)*ν) :
    2*((tb : ℤ)*z-((G : ℤ)*τ)*α+(1-(tb : ℤ))*V-ν*M)=(K : ℤ)+H-2 := by
  have hb : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hTne : (T : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
  apply mul_left_cancel₀ hTne
  push_cast at hap
  linear_combination 2*(tb : ℤ)*hzp-τ*hap-2*(T : ℤ)*(1-(tb : ℤ))*hb+
    ((K : ℤ)-H)*hlead-(c : ℤ)*hdrop+(M : ℤ)*hphase

/-- Every even short primitive phase realizes the actual midpoint, with
both the drop and the period contribution cancelled exactly. -/
theorem unequal_short_even_midpoint_twice
    {G t u T K H c V M α z r p q : ℕ}
    (ht : 1 ≤ t) (hT : T+u+1=8*t) (hTpos : 0 < T) (hbase : H+c=V+1)
    (hlink : T*p=8*r+q)
    (hap : (2*G*T : ℕ)*(α : ℤ)=(2*(t : ℤ)-1)*((K : ℤ)-H)+2*(t : ℤ)*c+(2*(r : ℤ))*M)
    (hzp : (T : ℤ)*z=(3-(u : ℤ))*K+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*M) :
    2*(((3*t-1 : ℕ) : ℤ)*z-((G : ℤ)*(5-3*(u : ℤ)))*α+
      (1-((3*t-1 : ℕ) : ℤ))*V-(((3*t-1 : ℕ) : ℤ)*p-3*(r : ℤ))*M)=(K : ℤ)+H-2 := by
  have htZ : (T : ℤ)+u+1=8*t := by exact_mod_cast hT
  have hlZ : (T : ℤ)*p=8*(r : ℤ)+q := by exact_mod_cast hlink
  have htb : ((3*t-1 : ℕ) : ℤ)=3*(t : ℤ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 3*t)]
    push_cast
    rfl
  apply primitive_midpoint_rival_twice (t:=2*t) (v:=u+1)
    (P:=2*(t : ℤ)-1) (Q:=3-(u : ℤ)) (r:=2*(r : ℤ)) (q:=q) hTpos hbase
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hap)
    (by push_cast; convert hzp using 1; ring)
  · rw [htb]
    nlinarith only [htZ]
  · rw [htb]
    push_cast
    nlinarith only [htZ]
  · rw [htb]
    linear_combination -2*(3*(t : ℤ)-1)*hlZ+6*(r : ℤ)*htZ

/-- Every even long primitive phase realizes the same actual midpoint. -/
theorem unequal_long_even_midpoint_twice
    {G t u T K H c V M α z r p q : ℕ}
    (ht : 1 ≤ t) (hT : T+u+1=8*t) (hTpos : 0 < T) (hbase : H+c=V+1)
    (hlink : T*p=8*r+q)
    (hap : (2*G*T : ℕ)*(α : ℤ)=-(6*(t : ℤ)-1)*((K : ℤ)-H)+2*(t : ℤ)*c+(2*(r : ℤ))*M)
    (hzp : (T : ℤ)*z=(3*(u : ℤ)-1)*K+((T : ℤ)-3*u+1)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*M) :
    2*(((5*t-1 : ℕ) : ℤ)*z-((G : ℤ)*(3-5*(u : ℤ)))*α+
      (1-((5*t-1 : ℕ) : ℤ))*V-(((5*t-1 : ℕ) : ℤ)*p-5*(r : ℤ))*M)=(K : ℤ)+H-2 := by
  have htZ : (T : ℤ)+u+1=8*t := by exact_mod_cast hT
  have hlZ : (T : ℤ)*p=8*(r : ℤ)+q := by exact_mod_cast hlink
  have htb : ((5*t-1 : ℕ) : ℤ)=5*(t : ℤ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 5*t)]
    push_cast
    rfl
  apply primitive_midpoint_rival_twice (t:=2*t) (v:=u+1)
    (P:=-(6*(t : ℤ)-1)) (Q:=3*(u : ℤ)-1) (r:=2*(r : ℤ)) (q:=q) hTpos hbase
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hap)
    (by push_cast; convert hzp using 1; ring)
  · rw [htb]
    nlinarith only [htZ]
  · rw [htb]
    push_cast
    nlinarith only [htZ]
  · rw [htb]
    linear_combination -2*(5*(t : ℤ)-1)*hlZ+10*(r : ℤ)*htZ

/-- The actual midpoint lies inside the axis width and above the full
tuple length. Its integrality handles the smallest possible height. -/
theorem exists_axis_rep_of_top_half_midpoint
    {n L H : ℕ} {Z : ℤ} (hn : 1 ≤ n) (hwidth : 2*n ≤ 2^L)
    (hH : 1 ≤ H) (hHn : H ≤ n) (hmid : 2*Z=(2 : ℤ)^L+H-2) :
    (n : ℤ) ≤ Z ∧ ∃ k, val L k=Z.toNat ∧ dsum L k ≤ L := by
  have hwidthZ : 2*(n : ℤ) ≤ (2 : ℤ)^L := by exact_mod_cast hwidth
  have hHZ : (1 : ℤ) ≤ H := by exact_mod_cast hH
  have hHnZ : (H : ℤ) ≤ n := by exact_mod_cast hHn
  have hnZ : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hZ : (n : ℤ) ≤ Z := by omega
  have hZhi : Z < (2 : ℤ)^L := by omega
  have hZ0 : 0 ≤ Z := by omega
  have hcast := Int.toNat_of_nonneg hZ0
  have hlt : Z.toNat < 2^L := by exact_mod_cast (show (Z.toNat : ℤ) < (2 : ℤ)^L by omega)
  obtain ⟨k,_,hk,hkc⟩ := exists_rep_le L Z.toNat hlt
  exact ⟨hZ,k,hk,hkc⟩

/-- An actual midpoint with one companion coin saved gives a complete
three-axis rival using only the ordinary dominant-width bound. -/
theorem exists_rival_of_affordable_midpoint
    {n N L a b M α z V D ta tb H : ℕ} {κ ν : ℤ}
    (hn : 1 ≤ n) (hL : L+a+b=n) (hwidth : 2*n ≤ 2^L) (hH : 1 ≤ H) (hHn : H ≤ n)
    (hcomp : gmin (a-1) ta+gmin (b-1) tb ≤ a+b-1)
    (hdist : ta ≠ 2^a-1 ∨ tb ≠ 2^b-1)
    (hmid : 2*((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M)=(2 : ℤ)^L+H-2)
    (x y w : ZMod N) (hta : (ta : ℤ)=tb+(D : ℤ)*κ)
    (hα : α • x=D • y) (hz : z • x+y+w=V • x) (hmx : M • x=0) :
    ∃ Z, n ≤ Z ∧ (ta ≠ 2^a-1 ∨ tb ≠ 2^b-1) ∧ ∃ k,
      val L k=Z ∧ dsum L k+gmin (a-1) ta+gmin (b-1) tb ≤ n ∧
      Z • x+ta • y+tb • w=V • x := by
  obtain ⟨hZ,k,hk,hkc⟩ := exists_axis_rep_of_top_half_midpoint hn hwidth hH hHn hmid
  let Z : ℤ := (tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M
  have hZ0 : 0 ≤ Z := le_trans (by positivity) hZ
  have hcast := Int.toNat_of_nonneg hZ0
  have hnat : n ≤ Z.toNat := by exact_mod_cast (show (n : ℤ) ≤ (Z.toNat : ℤ) by omega)
  exact ⟨Z.toNat,hnat,hdist,k,hk,by omega,signed_axis_basis_rival_eq x y w κ ν hta hz hα hmx hZ0⟩

/-- Every even unequal primitive phase below the largest possible index
has a midpoint rival, uniformly in both lengths and both orientations. -/
theorem exists_unequal_even_primitive_rival
    {a b n N L D G s t u T M H c V α z r q : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hn : 1 ≤ n)
    (hs : s=2^(a-2)) (ht : t=2^(b-2)) (hDG : D*G=s) (htu : t=s*u)
    (hT : T+u+1=8*t) (hTpos : 0 < T) (hL : L+a+b=n) (hwidth : 2*n ≤ 2^L)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1) (heven : 2 ∣ r) (hlink : T ∣ 4*r+q)
    (hphases :
      ((2*G*T : ℕ)*(α : ℤ)=(2*(t : ℤ)-1)*((2 : ℤ)^L-H)+2*(t : ℤ)*c+(r : ℤ)*M ∧
       (T : ℤ)*z=(3-(u : ℤ))*(2 : ℤ)^L+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*M) ∨
      ((2*G*T : ℕ)*(α : ℤ)=-(6*(t : ℤ)-1)*((2 : ℤ)^L-H)+2*(t : ℤ)*c+(r : ℤ)*M ∧
       (T : ℤ)*z=(3*(u : ℤ)-1)*(2 : ℤ)^L+((T : ℤ)-3*u+1)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*M))
    (x y w : ZMod N) (hα : α • x=D • y) (hz : z • x+y+w=V • x) (hmx : M • x=0) :
    ∃ Z ta tb, n ≤ Z ∧ (ta ≠ 2^a-1 ∨ tb ≠ 2^b-1) ∧ ∃ k,
      val L k=Z ∧ dsum L k+gmin (a-1) ta+gmin (b-1) tb ≤ n ∧
      Z • x+ta • y+tb • w=V • x := by
  obtain ⟨r,rfl⟩ := heven
  obtain ⟨p,hp⟩ := hlink
  have hlink' : T*p=8*r+q := by omega
  have hspos : 1 ≤ s := by rw [hs]; exact Nat.one_le_two_pow
  have htpos : 1 ≤ t := by rw [ht]; exact Nat.one_le_two_pow
  have hDGZ : (D : ℤ)*G=s := by exact_mod_cast hDG
  have htuZ : (t : ℤ)=(s : ℤ)*u := by exact_mod_cast htu
  have hpa : 2^a=4*s := by rw [hs,show a=2+(a-2) by omega,pow_add]; norm_num
  have hpb : 2^b=4*t := by rw [ht,show b=2+(b-2) by omega,pow_add]; norm_num
  have hca := equal_even_phase_companion_coin_cost (a-2)
  have hcb := equal_even_phase_companion_coin_cost (b-2)
  rw [show a-2+1=a-1 by omega,show a-2+2=a by omega,← hs] at hca
  rw [show b-2+1=b-1 by omega,show b-2+2=b by omega,← ht] at hcb
  rcases hphases with ⟨hap,hzp⟩ | ⟨hap,hzp⟩
  · let κ : ℤ := (G : ℤ)*(5-3*(u : ℤ))
    let ν : ℤ := ((3*t-1 : ℕ) : ℤ)*p-3*(r : ℤ)
    have hmid := unequal_short_even_midpoint_twice (K:=2^L) htpos hT hTpos hbase hlink'
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_mul] using hap)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hzp)
    have hta : ((5*s-1 : ℕ) : ℤ)=(3*t-1 : ℕ)+(D : ℤ)*κ := by
      dsimp [κ]
      rw [Nat.cast_sub (by omega : 1 ≤ 5*s),Nat.cast_sub (by omega : 1 ≤ 3*t)]
      push_cast
      linear_combination -(5-3*(u : ℤ))*hDGZ-3*htuZ
    obtain ⟨Z,hZ,hd,k,hk,hkc,heq⟩ := exists_rival_of_affordable_midpoint (a:=a) (b:=b)
      hn hL hwidth hH (by omega) (by omega) (Or.inl (by omega))
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hmid) x y w hta hα hz hmx
    exact ⟨Z,5*s-1,3*t-1,hZ,hd,k,hk,hkc,heq⟩
  · let κ : ℤ := (G : ℤ)*(3-5*(u : ℤ))
    let ν : ℤ := ((5*t-1 : ℕ) : ℤ)*p-5*(r : ℤ)
    have hmid := unequal_long_even_midpoint_twice (K:=2^L) htpos hT hTpos hbase hlink'
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_mul] using hap)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hzp)
    have hta : ((3*s-1 : ℕ) : ℤ)=(5*t-1 : ℕ)+(D : ℤ)*κ := by
      dsimp [κ]
      rw [Nat.cast_sub (by omega : 1 ≤ 3*s),Nat.cast_sub (by omega : 1 ≤ 5*t)]
      push_cast
      linear_combination -(3-5*(u : ℤ))*hDGZ-5*htuZ
    obtain ⟨Z,hZ,hd,k,hk,hkc,heq⟩ := exists_rival_of_affordable_midpoint (a:=a) (b:=b)
      hn hL hwidth hH (by omega) (by omega) (Or.inl (by omega))
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hmid) x y w hta hα hz hmx
    exact ⟨Z,3*s-1,5*t-1,hZ,hd,k,hk,hkc,heq⟩
end MinModulus
