import MinModulus.ChainForestProfileTwoFour

/-! Algebraic tools for equal length-three companions: a modulo-sixteen
obstruction, general dominant-gcd membership, and signed rival identities.
No global-bound closure is asserted by these tools alone. -/

namespace MinModulus
open Finset

/-- A length-three half-profile cannot coexist with an even axis when
all three relevant axis weights vanish modulo sixteen. This is an
algebraic obstruction, without a validity or genuine-endpoint premise. -/
theorem three_three_half_relations_not_sixteen_dvd
    {N K H c V : ℕ} [NeZero N] (hK : 1 ≤ K)
    (hK8 : 8 ∣ K) (hH8 : 8 ∣ H) (hc8 : 8 ∣ c) (hbase : H+c=V+1)
    (x a b : ZMod N) (hx : Even x.val) (ha : Odd a.val)
    (htop : (K-1) • x+7 • a+7 • b=V • x)
    (hcomp : 11 • a+3 • b=c • x) : ¬ 16 ∣ N := by
  intro hN16
  let π := ZMod.castHom hN16 (ZMod 16)
  have h16 : (16 : ZMod 16)=0 := by decide
  have hπval : ∀ t : ZMod N, π t=(t.val : ZMod 16) := fun t ↦ ZMod.cast_eq_val t
  have h8x : (8 : ZMod 16)*π x=0 := by
    obtain ⟨u,hu⟩ := hx
    rw [hπval,hu]
    push_cast
    calc
      _ = (16 : ZMod 16)*u := by ring
      _ = 0 := by rw [h16,zero_mul]
  have hkill (t : ℕ) (ht : 8 ∣ t) : (t : ZMod 16)*π x=0 := by
    obtain ⟨s,rfl⟩ := ht
    push_cast
    calc
      _ = (s : ZMod 16)*(8*π x) := by ring
      _ = 0 := by rw [h8x,mul_zero]
  have hKx := hkill K hK8
  have hHx := hkill H hH8
  have hcx := hkill c hc8
  have hbaseZ : (H : ZMod 16)+(c : ZMod 16)=(V : ZMod 16)+1 := by
    have hh := congrArg (fun t : ℕ ↦ (t : ZMod 16)) hbase
    push_cast at hh
    exact hh
  have ht := congrArg π htop
  have hc := congrArg π hcomp
  simp only [map_add,map_nsmul] at ht hc
  simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at ht hc
  have hsum7 : (7 : ZMod 16)*(π a+π b)=0 := by
    linear_combination ht-hbaseZ*(π x)-hKx+hHx+hcx
  have hsum : π a+π b=0 := by
    have hh := congrArg (fun t : ZMod 16 ↦ 7*t) hsum7
    have h49 : (7 : ZMod 16)*7=1 := by decide
    simpa only [← mul_assoc,h49,one_mul,mul_zero] using hh
  have h8a : (8 : ZMod 16)*π a=0 := by
    linear_combination hc-3*hsum+hcx
  have h8odd : (8 : ZMod 16)*π a=8 := by
    obtain ⟨u,hu⟩ := ha
    rw [hπval,hu]
    push_cast
    calc
      _ = (16 : ZMod 16)*u+8 := by ring
      _ = 8 := by rw [h16,zero_mul,zero_add]
  have hh : (8 : ZMod 16)=0 := h8odd.symm.trans h8a
  exact (by decide : (8 : ZMod 16) ≠ 0) hh

/-- Divisibility by the actual dominant gcd gives a bounded axis
coefficient at the group level. -/
theorem exists_axis_coefficient_of_gcd_dvd_val
    {N D : ℕ} [NeZero N] (x y : ZMod N)
    (hindex : N.gcd x.val=D) (hy : D ∣ y.val) :
    ∃ z < N/D, z • x=y := by
  have ho : addOrderOf x=N/D := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hm : 0 < N/D := by rw [← ho]; exact addOrderOf_pos _
  have hinv : x*x⁻¹=(D : ZMod N) := by
    rw [ZMod.mul_inv_eq_gcd,Nat.gcd_comm,hindex]
  obtain ⟨u,hu⟩ := hy
  let a : ZMod N := (u : ZMod N)*x⁻¹
  have ha : a.val • x=y := by
    rw [nsmul_eq_mul,ZMod.natCast_zmod_val]
    change (u : ZMod N)*x⁻¹*x=y
    calc
      _ = (u : ZMod N)*(x*x⁻¹) := by ring
      _ = (y.val : ZMod N) := by rw [hinv,hu]; push_cast; ring
      _ = y := ZMod.natCast_zmod_val y
  refine ⟨a.val%(N/D),Nat.mod_lt _ hm,?_⟩
  rw [← ho,mod_addOrderOf_nsmul,ha]

/-- The equal length-three companions have a one-each axis coefficient
at every possible dominant index two, four or eight. -/
theorem exists_three_three_one_each_axis_coefficient
    {N D K V : ℕ} [NeZero N] [NeZero D] (hD : D ∣ 48)
    (x a b : ZMod N) (hindex : N.gcd x.val=D)
    (htop : (K-1) • x+7 • a+7 • b=V • x) :
    ∃ z < N/D, z • x+a+b=V • x := by
  have hDN : D ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  let π := ZMod.castHom hDN (ZMod D)
  have hπval : ∀ t : ZMod N, π t=(t.val : ZMod D) := fun t ↦ ZMod.cast_eq_val t
  have hπx : π x=0 := by
    rw [hπval,ZMod.natCast_eq_zero_iff,← hindex]
    exact Nat.gcd_dvd_right _ _
  have h48 : (48 : ZMod D)=0 := (ZMod.natCast_eq_zero_iff 48 D).mpr hD
  have h49 : (7 : ZMod D)*7=1 := by
    calc
      _ = (48 : ZMod D)+1 := by norm_num
      _ = 1 := by rw [h48,zero_add]
  have hh := congrArg π htop
  simp only [map_add,map_nsmul] at hh
  simp only [hπx,smul_zero,zero_add,nsmul_eq_mul] at hh
  have hsum7 : (7 : ZMod D)*(π a+π b)=0 := by linear_combination hh
  have hsum : π a+π b=0 := by
    have hh := congrArg (fun t : ZMod D ↦ 7*t) hsum7
    simpa only [← mul_assoc,h49,one_mul,mul_zero] using hh
  let y := V • x-(a+b)
  have hπy : π y=0 := by simp only [y,map_sub,map_nsmul,map_add,hπx,smul_zero,hsum,sub_self]
  have hy : D ∣ y.val := by rwa [hπval,ZMod.natCast_eq_zero_iff] at hπy
  obtain ⟨z,hz,hzy⟩ := exists_axis_coefficient_of_gcd_dvd_val x y hindex hy
  refine ⟨z,hz,?_⟩
  rw [hzy]
  dsimp [y]
  abel

/-- A companion relation evaluates its signed rival coefficient in
any cyclic group, without normalizing the seed. -/
theorem signed_companion_relation_rival_eq
    {N M z c V ta tb p q : ℕ} (x a b : ZMod N) (U W ν : ℤ)
    (hta : (ta : ℤ)=U-(p : ℤ)*W) (htb : (tb : ℤ)=U-(q : ℤ)*W)
    (hz : z • x+a+b=V • x) (hshort : p • a+q • b=c • x) (hM : M • x=0)
    (hpos : 0 ≤ U*z+(1-U)*V+W*c-ν*M) :
    (U*z+(1-U)*V+W*c-ν*M).toNat • x+ta • a+tb • b=V • x := by
  let Z : ℤ := U*z+(1-U)*V+W*c-ν*M
  change 0 ≤ Z at hpos
  change Z.toNat • x+ta • a+tb • b=V • x
  have hZeq : (Z.toNat : ZMod N)=(U : ZMod N)*z+(1-(U : ZMod N))*V+(W : ZMod N)*c-(ν : ZMod N)*M := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) (Int.toNat_of_nonneg hpos)
    dsimp [Z] at hh
    push_cast at hh
    exact hh
  have htaZ : (ta : ZMod N)=(U : ZMod N)-(p : ZMod N)*(W : ZMod N) := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) hta
    push_cast at hh
    exact hh
  have htbZ : (tb : ZMod N)=(U : ZMod N)-(q : ZMod N)*(W : ZMod N) := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) htb
    push_cast at hh
    exact hh
  simp only [nsmul_eq_mul] at hz hshort hM ⊢
  rw [hZeq,htaZ,htbZ]
  linear_combination (U : ZMod N)*hz-(W : ZMod N)*hshort-(ν : ZMod N)*hM


end MinModulus
