import MinModulus.ChainForestProfileComplementary
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-! Signed primitive multiples combined with the top relation give
actual complementary rivals and exact errors. A cancellation identity
controls the deficit coefficient. Integer Dirichlet approximation supplies
a bounded multiple but does not assert nonintegrality. The actual combined
companion cost gives a sharper representation budget than the uniform
crude bound. Uniform selection and integral cases remain open. -/

namespace MinModulus

/-- Adding a signed multiple of the top relation to a primitive axis
coefficient gives an actual rival whenever its weights and coefficient
are nonnegative. This applies to either sign of the primitive multiple. -/
theorem signed_axis_multiple_top_shift_rival_eq
    {N M D α K V p q ta tb : ℕ} (hK : 1 ≤ K)
    (x a b : ZMod N) (κ ν m : ℤ)
    (hta : (ta : ℤ)=D*κ+m*p) (htb : (tb : ℤ)=m*q)
    (hα : α • x=D • a) (htop : (K-1) • x+p • a+q • b=V • x)
    (hM : M • x=0)
    (hpos : 0 ≤ -κ*α+ν*M+m*((K : ℤ)-1-V)+V) :
    (-κ*α+ν*M+m*((K : ℤ)-1-V)+V).toNat • x+ta • a+tb • b=V • x := by
  let Z : ℤ := -κ*α+ν*M+m*((K : ℤ)-1-V)+V
  change 0 ≤ Z at hpos
  change Z.toNat • x+ta • a+tb • b=V • x
  have hZ : (Z.toNat : ZMod N)=-(κ : ZMod N)*α+(ν : ZMod N)*M+
      (m : ZMod N)*((K : ZMod N)-1-V)+V := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) (Int.toNat_of_nonneg hpos)
    dsimp [Z] at hh
    push_cast at hh
    exact hh
  have htaZ : (ta : ZMod N)=(D : ZMod N)*κ+(m : ZMod N)*p := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) hta
    push_cast at hh
    exact hh
  have htbZ : (tb : ZMod N)=(m : ZMod N)*q := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) htb
    push_cast at hh
    exact hh
  simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hα htop hM ⊢
  rw [hZ,htaZ,htbZ]
  linear_combination -(κ : ZMod N)*hα+(m : ZMod N)*htop+(ν : ZMod N)*hM

/-- The top-shift construction has one signed error formula for both
primitive orientations and both complementary choices. -/
theorem signed_axis_multiple_top_shift_error
    {M E K H c V α S W t : ℕ} {P r κ ν m R : ℤ}
    (hbase : H+c=V+1) (hM : M+E=W*K)
    (hα : (S : ℤ)*α=P*((K : ℤ)-H)+(t : ℤ)*c+r*M)
    (hR : R=-κ*(P+(W : ℤ)*r)+(S : ℤ)*ν*W+(S : ℤ)*m) :
    (S : ℤ)*(-κ*α+ν*M+m*((K : ℤ)-1-V)+V)-R*K =
      ((S : ℤ)*(1-m)+κ*P)*H+((S : ℤ)*(1-m)-κ*t)*c-S+
        (κ*r-(S : ℤ)*ν)*E := by
  have hbZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hMZ : (M : ℤ)+E=(W : ℤ)*K := by exact_mod_cast hM
  linear_combination -κ*hα-(S : ℤ)*(1-m)*hbZ-
    (κ*r-(S : ℤ)*ν)*hMZ-hR*(K : ℤ)

/-- The apparent phase-dependent deficit coefficient is controlled by
just the signed leading error and the primitive leading constant. -/
theorem top_shift_deficit_coefficient_identity
    {S W : ℕ} {P r κ ν m R : ℤ}
    (hR : R=-κ*(P+(W : ℤ)*r)+(S : ℤ)*ν*W+(S : ℤ)*m) :
    (W : ℤ)*(κ*r-(S : ℤ)*ν)=(S : ℤ)*m-R-κ*P := by
  linear_combination hR

/-- Dirichlet approximation in a purely integer form supplies a bounded
positive primitive multiple. No nonintegrality of that multiple is claimed. -/
theorem exists_bounded_integer_primitive_approximation
    (A : ℤ) {B Q : ℕ} (hB : 0 < B) (hQ : 0 < Q) :
    ∃ κ : ℕ, ∃ ν : ℤ, 0 < κ ∧ κ ≤ Q ∧
      |(κ : ℤ)*A-ν*B| *(Q+1 : ℕ) ≤ B := by
  obtain ⟨κ,hκ,hκQ,hh⟩ := Real.exists_nat_abs_mul_sub_round_le ((A : ℝ)/B) hQ
  let ν : ℤ := round ((κ : ℝ)*((A : ℝ)/B))
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hQR : (0 : ℝ) < (Q : ℝ)+1 := by positivity
  change |(κ : ℝ)*((A : ℝ)/B)-(ν : ℝ)| ≤ 1/((Q : ℝ)+1) at hh
  have hscaled := (le_div_iff₀ hQR).mp hh
  have hprod := mul_le_mul_of_nonneg_left hscaled (le_of_lt hBR)
  have heq : (κ : ℝ)*(A : ℝ)-(ν : ℝ)*B=
      ((κ : ℝ)*((A : ℝ)/B)-(ν : ℝ))*B := by
    field_simp
  have hbound : |(κ : ℝ)*(A : ℝ)-(ν : ℝ)*B| *((Q : ℝ)+1) ≤ B := by
    rw [heq,abs_mul,abs_of_pos hBR]
    nlinarith only [hprod]
  refine ⟨κ,ν,hκ,hκQ,?_⟩
  exact_mod_cast hbound

/-- An exact combined companion cost can replace the uniform crude
bound when a complementary pair is explicitly constructed. -/
theorem one_complementary_prefix_fits_combined_budget
    {n e w d m p q C₁ C₂ : ℕ} (hn : e+(w+1)+d=n)
    (hpq : p+q+1=2*m*2^w) (hcost : C₁+C₂+2*m ≤ w+2*d+4) :
    gmin w p+e+C₁ ≤ n ∨ gmin w q+e+C₂ ≤ n := by
  have hp := gmin_pair_of_sum_add_one_eq_top_multiple w p q (2*m) hpq
  omega

/-- Complementary signed windows give one actual representation using
only their combined companion cost, with no separate prefix budget. -/
theorem exists_one_complementary_representation_of_combined_cost
    {n L e w d m T R₁ R₂ Δ C₁ C₂ : ℕ} (Z₁ Z₂ : ℤ)
    (hL : e+(w+1)=L) (hn : L+d=n)
    (hT : 0 < T) (hThi : T ≤ 2^(w+1)) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hRsum : R₁+R₂=m*T) (hrem : 0 < (R₁*2^(w+1))%T)
    (hcost : C₁+C₂+2*m ≤ w+2*d+4) (herror : Δ < 2^e) (hnQ : n ≤ 2^e)
    (hw₁ : (R₁ : ℤ)*2^L < T*Z₁+Δ ∧ T*Z₁ < (R₁ : ℤ)*2^L+Δ)
    (hw₂ : (R₂ : ℤ)*2^L < T*Z₂+Δ ∧ T*Z₂ < (R₂ : ℤ)*2^L+Δ) :
    (0 ≤ Z₁ ∧ n ≤ Z₁.toNat ∧ ∃ u, val L u=Z₁.toNat ∧ dsum L u+C₁ ≤ n) ∨
    (0 ≤ Z₂ ∧ n ≤ Z₂.toNat ∧ ∃ u, val L u=Z₂.toNat ∧ dsum L u+C₂ ≤ n) := by
  have hsum : R₁*2^(w+1)+R₂*2^(w+1)=(2*m*2^w)*T := by
    calc R₁*2^(w+1)+R₂*2^(w+1)=(R₁+R₂)*2^(w+1) := by ring
      _ = (m*T)*2^(w+1) := by rw [hRsum]
      _ = (2*m*2^w)*T := by rw [pow_succ]; ring
  obtain ⟨hrem₂,hpair⟩ := quotient_pair_of_nonintegral_sum_eq_multiple hT hsum hrem
  have hbudget := one_complementary_prefix_fits_combined_budget (n := n) (e := e)
    (d := d) (by omega) hpair hcost
  rcases hbudget with hbudget | hbudget
  · obtain ⟨hpos,hnz,_,u,hu,hc⟩ := exists_rep_of_int_binary_prefix_fraction
      Z₁ hL hT hThi hR₁ hrem hbudget herror hnQ hw₁
    exact Or.inl ⟨hpos,hnz,u,hu,hc⟩
  · obtain ⟨hpos,hnz,_,u,hu,hc⟩ := exists_rep_of_int_binary_prefix_fraction
      Z₂ hL hT hThi hR₂ hrem₂ hbudget herror hnQ hw₂
    exact Or.inr ⟨hpos,hnz,u,hu,hc⟩

end MinModulus
