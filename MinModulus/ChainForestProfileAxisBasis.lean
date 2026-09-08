import MinModulus.ChainForestProfileEqualCorner

/-! A complete algebraic basis for axis rivals. One-each and
index-times-companion coefficients generate all companion weights
congruent modulo the actual index; a unit companion makes this congruence
necessary. Equal half-profile relations give the primitive coefficient
phase, retaining information lost by using the full companion width as
weight-difference modulus. Uniform larger coin budgets remain open. -/

namespace MinModulus

/-- Multiplying any companion by the actual dominant index puts it
in the axis subgroup, with a bounded coefficient. -/
theorem exists_companion_multiple_axis_coefficient
    {N D : ℕ} [NeZero N] [NeZero D] (x a : ZMod N)
    (hindex : N.gcd x.val=D) : ∃ α < N/D, α • x=D • a := by
  have hDN : D ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  let π := ZMod.castHom hDN (ZMod D)
  have hπval : ∀ t : ZMod N, π t=(t.val : ZMod D) := fun t ↦ ZMod.cast_eq_val t
  have hd : (D : ZMod D)=0 := ZMod.natCast_self _
  have hy : π (D • a)=0 := by rw [map_nsmul,nsmul_eq_mul,hd,zero_mul]
  have hdiv : D ∣ (D • a).val := by rwa [hπval,ZMod.natCast_eq_zero_iff] at hy
  exact exists_axis_coefficient_of_gcd_dvd_val x (D • a) hindex hdiv

/-- One-each and index-times-companion coefficients evaluate all signed
rivals whose companion weights differ by a multiple of the actual index. -/
theorem signed_axis_basis_rival_eq
    {N M z α V D ta tb : ℕ} (x a b : ZMod N) (κ ν : ℤ)
    (hta : (ta : ℤ)=tb+(D : ℤ)*κ)
    (hz : z • x+a+b=V • x) (hα : α • x=D • a) (hM : M • x=0)
    (hpos : 0 ≤ (tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M) :
    ((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M).toNat • x+ta • a+tb • b=V • x := by
  let Z : ℤ := (tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M
  change 0 ≤ Z at hpos
  change Z.toNat • x+ta • a+tb • b=V • x
  have hZeq : (Z.toNat : ZMod N)=(tb : ZMod N)*z-(κ : ZMod N)*α+(1-(tb : ZMod N))*V-(ν : ZMod N)*M := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) (Int.toNat_of_nonneg hpos)
    dsimp [Z] at hh
    push_cast at hh
    exact hh
  have htaZ : (ta : ZMod N)=(tb : ZMod N)+(D : ZMod N)*(κ : ZMod N) := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) hta
    push_cast at hh
    exact hh
  simp only [nsmul_eq_mul] at hz hα hM ⊢
  rw [hZeq,htaZ]
  linear_combination (tb : ZMod N)*hz-(κ : ZMod N)*hα-(ν : ZMod N)*hM

/-- The actual index congruence exactly characterizes which companion
weights admit a bounded axis coefficient; a unit companion makes the
condition necessary as well as sufficient. -/
theorem exists_axis_rival_coefficient_iff_companion_congruence
    {N D z V ta tb : ℕ} [NeZero N] [NeZero D]
    (x a b : ZMod N) (hindex : N.gcd x.val=D) (ha : Nat.Coprime a.val D)
    (hz : z • x+a+b=V • x) :
    (∃ s < N/D, s • x+ta • a+tb • b=V • x) ↔ ta%D=tb%D := by
  have hDN : D ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  let π := ZMod.castHom hDN (ZMod D)
  have hπval : ∀ t : ZMod N, π t=(t.val : ZMod D) := fun t ↦ ZMod.cast_eq_val t
  have hπx : π x=0 := by
    rw [hπval,ZMod.natCast_eq_zero_iff,← hindex]
    exact Nat.gcd_dvd_right _ _
  have hu : IsUnit (π a) := by rw [hπval,ZMod.isUnit_iff_coprime]; exact ha
  have hsum := congrArg π hz
  simp only [map_add,map_nsmul,hπx,smul_zero,zero_add] at hsum
  constructor
  · rintro ⟨s,_,heval⟩
    have hh := congrArg π heval
    simp only [map_add,map_nsmul] at hh
    simp only [hπx,smul_zero,zero_add,nsmul_eq_mul] at hh
    have hp : ((ta : ZMod D)-(tb : ZMod D))*π a=0 := by
      linear_combination hh-(tb : ZMod D)*hsum
    have heq : (ta : ZMod D)=(tb : ZMod D) := sub_eq_zero.mp (hu.mul_left_eq_zero.mp hp)
    have hv := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast] using hv
  · intro hmod
    have heq : (ta : ZMod D)=(tb : ZMod D) := by
      apply ZMod.val_injective
      simpa only [ZMod.val_natCast] using hmod
    let y := V • x-(ta • a+tb • b)
    have hπy : π y=0 := by
      simp only [y,map_sub,map_add,map_nsmul]
      simp only [hπx,smul_zero,nsmul_eq_mul]
      rw [heq,← mul_add,hsum,mul_zero,sub_self]
    have hy : D ∣ y.val := by rwa [hπval,ZMod.natCast_eq_zero_iff] at hπy
    obtain ⟨s,hs,hsy⟩ := exists_axis_coefficient_of_gcd_dvd_val x y hindex hy
    refine ⟨s,hs,?_⟩
    rw [hsy]
    dsimp [y]
    abel

/-- The index-times-companion coefficient satisfies the full primitive
phase relation for any equal companion half-width, retaining phases
that the one-each coefficient alone does not distinguish. -/
theorem equal_companion_axis_multiple_relation
    {N D F s K H c V α B : ℕ} (hs : 1 ≤ s) (hK : 1 ≤ K)
    (hDF : D*F=2*s) (hbase : H+c=V+1)
    (hB : B+(s-1)*H=(s-1)*K+s*c)
    (x a b : ZMod N) (hα : α • x=D • a)
    (htop : (K-1) • x+(2*s-1) • a+(2*s-1) • b=V • x)
    (hhalf : (3*s-1) • a+(s-1) • b=c • x) :
    (F*(2*s-1)*α) • x=B • x := by
  have h2s : 1 ≤ 2*s := by omega
  have h3s : 1 ≤ 3*s := by omega
  have hDcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hDF
  have hbcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hbase
  have hBcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hB
  push_cast at hDcast hbcast hBcast
  simp only [Nat.cast_sub hs,Nat.cast_one] at hBcast
  simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_sub h2s,Nat.cast_sub h3s,
    Nat.cast_sub hs,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] at hα htop hhalf ⊢
  linear_combination (F : ZMod N)*(2*(s : ZMod N)-1)*hα-
    ((s : ZMod N)-1)*htop+(2*(s : ZMod N)-1)*hhalf+
    ((s : ZMod N)-1)*hbcast*x-hBcast*x+hDcast*(2*(s : ZMod N)-1)*a

end MinModulus
