import MinModulus.ChainForestProfileUnequalForest

/-! Uniform scalar formulas for signed unequal-companion rivals. The
compatible phases reduce the two basis coefficients to one primitive
coefficient. Every signed rival has an exact error formula separating
the dominant width from height, drop and period deficit. A coefficient
certificate supplies a strict linear window across the entire allowed
region. Uniform coin choices and budgets remain open. -/

namespace MinModulus

/-- The compatible short phases reduce the two basis coefficients
to one primitive axis coefficient and an exact period multiple. -/
theorem unequal_companion_short_primitive_basis_sum
    {F t u T M K H c α z : ℕ} {r q p : ℤ}
    (hTpos : 0 < T) (hT : T+u+1=4*t)
    (hαphase : (F*T : ℕ)*(α : ℤ)=((t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c+r*M)
    (hzphase : (T : ℤ)*z=(3-(u : ℤ))*K+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T+q*M)
    (hlink : 4*r+q=(T : ℤ)*p) :
    4*(F : ℤ)*α+z=(K : ℤ)+2*c-1+p*M := by
  have hTZ : (T : ℤ)+u+1=4*t := by exact_mod_cast hT
  have hTne : (T : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hTpos
  apply mul_left_cancel₀ hTne
  push_cast at hαphase
  linear_combination 4*hαphase+hzphase-hTZ*((K : ℤ)-H+c)+hlink*(M : ℤ)

/-- Every signed basis rival has a uniform exact short error
formula. The leading term separates the dominant width from the
height, drop and period deficit; no fixed companion lengths occur. -/
theorem unequal_companion_short_signed_rival_error
    {F t u T M E K H c V α z tb : ℕ} {r q κ ν R : ℤ}
    (hbase : H+c=V+1) (hM : M+E=4*F*t*K)
    (hαphase : (F*T : ℕ)*(α : ℤ)=((t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c+r*M)
    (hzphase : (T : ℤ)*z=(3-(u : ℤ))*K+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T+q*M)
    (hR : R=(F : ℤ)*tb*((3-(u : ℤ))+4*F*t*q)-κ*(((t : ℤ)-1)+4*F*t*r)-(F*T : ℕ)*ν*(4*F*t)) :
    (F*T : ℕ)*((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M)-R*K =
      ((F*T : ℕ)+(F : ℤ)*tb*((u : ℤ)-3)+κ*((t : ℤ)-1))*H+
      ((F*T : ℕ)-(F : ℤ)*tb*((u : ℤ)+1)-κ*t)*c-(F*T : ℕ)+
      ((F*T : ℕ)*ν-(F : ℤ)*tb*q+κ*r)*E := by
  have hbZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hMZ : (M : ℤ)+E=4*F*t*K := by exact_mod_cast hM
  push_cast at hαphase hR ⊢
  linear_combination (F : ℤ)*tb*hzphase-κ*hαphase-
    (F : ℤ)*T*(1-(tb : ℤ))*hbZ-
    ((F : ℤ)*T*ν-(F : ℤ)*tb*q+κ*r)*hMZ-hR*(K : ℤ)

/-- The compatible long phases reduce the two basis coefficients
to one primitive axis coefficient and an exact period multiple. -/
theorem unequal_companion_long_primitive_basis_sum
    {F t u T M K H c α z : ℕ} {r q p : ℤ}
    (hTpos : 0 < T) (hT : T+u+1=4*t)
    (hαphase : (F*T : ℕ)*(α : ℤ)=-(3*(t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c+r*M)
    (hzphase : (T : ℤ)*z=(3*(u : ℤ)-1)*K+((T : ℤ)-3*u+1)*H+((T : ℤ)-u-1)*c-T+q*M)
    (hlink : 4*r+q=(T : ℤ)*p) :
    4*(F : ℤ)*α+z=-3*(K : ℤ)+4*H+2*c-1+p*M := by
  have hTZ : (T : ℤ)+u+1=4*t := by exact_mod_cast hT
  have hTne : (T : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hTpos
  apply mul_left_cancel₀ hTne
  push_cast at hαphase
  linear_combination 4*hαphase+hzphase+hTZ*(3*(K : ℤ)-3*H-c)+hlink*(M : ℤ)

/-- Every signed basis rival has a uniform exact long error
formula. The leading term separates the dominant width from the
height, drop and period deficit; no fixed companion lengths occur. -/
theorem unequal_companion_long_signed_rival_error
    {F t u T M E K H c V α z tb : ℕ} {r q κ ν R : ℤ}
    (hbase : H+c=V+1) (hM : M+E=4*F*t*K)
    (hαphase : (F*T : ℕ)*(α : ℤ)=-(3*(t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c+r*M)
    (hzphase : (T : ℤ)*z=(3*(u : ℤ)-1)*K+((T : ℤ)-3*u+1)*H+((T : ℤ)-u-1)*c-T+q*M)
    (hR : R=(F : ℤ)*tb*((3*(u : ℤ)-1)+4*F*t*q)-κ*((-(3*(t : ℤ)-1))+4*F*t*r)-(F*T : ℕ)*ν*(4*F*t)) :
    (F*T : ℕ)*((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M)-R*K =
      ((F*T : ℕ)+(F : ℤ)*tb*(1-3*(u : ℤ))-κ*(3*(t : ℤ)-1))*H+
      ((F*T : ℕ)-(F : ℤ)*tb*((u : ℤ)+1)-κ*t)*c-(F*T : ℕ)+
      ((F*T : ℕ)*ν-(F : ℤ)*tb*q+κ*r)*E := by
  have hbZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hMZ : (M : ℤ)+E=4*F*t*K := by exact_mod_cast hM
  push_cast at hαphase hR ⊢
  linear_combination (F : ℤ)*tb*hzphase-κ*hαphase-
    (F : ℤ)*T*(1-(tb : ℤ))*hbZ-
    ((F : ℤ)*T*ν-(F : ℤ)*tb*q+κ*r)*hMZ-hR*(K : ℤ)

/-- Coefficient bounds certify a strict linear window for a signed
rival error throughout the entire allowed height/drop/deficit region. -/
theorem signed_rival_linear_error_window
    {n H c E W S : ℕ} {A B J C : ℤ}
    (hH : 1 ≤ H) (hn : H+c ≤ n) (hE : E ≤ W*H) (hS : 0 < S) (hC : 0 ≤ C)
    (hloA : -C < A-S+min J 0*W) (hloB : -C ≤ B)
    (hhiA : A+max J 0*W ≤ C) (hhiB : B ≤ C) :
    -C*n < A*H+B*c-S+J*E ∧ A*H+B*c-S+J*E < C*n := by
  have hHZ : (1 : ℤ) ≤ H := by exact_mod_cast hH
  have hnZ : (H : ℤ)+c ≤ n := by exact_mod_cast hn
  have hEZ : (E : ℤ) ≤ (W : ℤ)*H := by exact_mod_cast hE
  have hSZ : (0 : ℤ) < S := by exact_mod_cast hS
  have hJlo : min J 0*(W : ℤ)*H ≤ J*E := by
    by_cases hJ : 0 ≤ J
    · rw [min_eq_right hJ,zero_mul,zero_mul]
      exact mul_nonneg hJ (by positivity)
    · have hJ' : J ≤ 0 := by omega
      rw [min_eq_left hJ']
      have hh := mul_le_mul_of_nonpos_left hEZ hJ'
      nlinarith only [hh]
  have hJhi : J*E ≤ max J 0*(W : ℤ)*H := by
    by_cases hJ : 0 ≤ J
    · rw [max_eq_left hJ]
      have hh := mul_le_mul_of_nonneg_left hEZ hJ
      nlinarith only [hh]
    · have hJ' : J ≤ 0 := by omega
      rw [max_eq_right hJ',zero_mul,zero_mul]
      exact mul_nonpos_of_nonpos_of_nonneg hJ' (by positivity)
  have hlow := mul_pos (show 0 < A-S+min J 0*W+C by linarith) (show (0 : ℤ) < H by omega)
  have hlowB : 0 ≤ (B+C)*(c : ℤ) := mul_nonneg (by linarith) (by positivity)
  have hhigh : 0 ≤ (C-A-max J 0*W)*(H : ℤ) := mul_nonneg (by linarith) (by positivity)
  have hhighB : 0 ≤ (C-B)*(c : ℤ) := mul_nonneg (by linarith) (by positivity)
  have hshift : 0 ≤ (S : ℤ)*((H : ℤ)-1) := mul_nonneg (by omega) (by omega)
  have hbudget := mul_le_mul_of_nonneg_left hnZ hC
  constructor
  · nlinarith only [hJlo,hlow,hlowB,hshift,hbudget]
  · nlinarith only [hJhi,hhigh,hhighB,hSZ,hbudget]

end MinModulus
