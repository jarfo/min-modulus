import MinModulus.FibreOvercountGap
import MinModulus.MidpointFibreOvercountParity

namespace MinModulus
open Finset
open scoped Classical

/-- Odd correction lies outside the intrinsic half-exponent regime. -/
theorem dimension_le_twice_log_loss_of_odd_fibre_overcount
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hodd : Odd (tupleBinaryFibreOvercount g b)) :
    n ≤ 2*Nat.log 2 (tupleBinaryCollisionLoss g b) := by
  by_contra h
  have he := Nat.even_iff.mp (even_fibre_overcount_of_intrinsic_half_exponent g b (by omega))
  have ho := Nat.odd_iff.mp hodd
  omega

/-- The sharp balanced loss threshold forces even correction even
when non-midpoint fibres have arbitrary multiplicity. -/
theorem even_fibre_overcount_of_balanced_loss_bound
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hsmall : tupleBinaryCollisionLoss g b+1 < 2^(n/2)+2^(n-n/2)) :
    Even (tupleBinaryFibreOvercount g b) := by
  exact even_fibre_overcount_of_midpoint_fibres_le_two g b
    (fun z hz ↦ midpoint_fibre_card_le_two_of_balanced_loss_bound g b z hsmall hz)

/-- Odd total correction forces the sharp balanced two-block loss
threshold, without validity or a cap on other fibres. -/
theorem balanced_power_sum_le_loss_add_one_of_odd_fibre_overcount
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hodd : Odd (tupleBinaryFibreOvercount g b)) :
    2^(n/2)+2^(n-n/2) ≤ tupleBinaryCollisionLoss g b+1 := by
  by_contra h
  have he := Nat.even_iff.mp (even_fibre_overcount_of_balanced_loss_bound g b (by omega))
  have ho := Nat.odd_iff.mp hodd
  omega

/-- For valid tuples, odd correction forces core charge at least
the balanced power sum plus two, including the correction gap. -/
theorem balanced_power_sum_add_two_le_core_sum_of_odd_overcount
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hodd : Odd (tupleBinaryFibreOvercount g b)) :
    2^(n/2)+2^(n-n/2)+2 ≤
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  have hL := balanced_power_sum_le_loss_add_one_of_odd_fibre_overcount g b hodd
  have hD := Nat.odd_iff.mp hodd
  have hne := tuple_binary_fibre_overcount_ne_one g b
  have he := intrinsic_loss_add_fibre_overcount_eq_core_cube_sum g hg b
  omega

/-- Core charge below the balanced odd-correction threshold forces
even correction without any global fibre-size cap. -/
theorem even_fibre_overcount_of_core_sum_lt_balanced_sum_add_two
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hsmall : (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card)) <
      2^(n/2)+2^(n-n/2)+2) : Even (tupleBinaryFibreOvercount g b) := by
  apply Nat.even_iff.mpr
  by_contra h
  have hodd : Odd (tupleBinaryFibreOvercount g b) := Nat.odd_iff.mpr (by omega)
  have hbound := balanced_power_sum_add_two_le_core_sum_of_odd_overcount g hg b hodd
  omega

/-- Below the balanced core-charge threshold, core charge and actual
intrinsic loss have the same parity at arbitrary multiplicity. -/
theorem intrinsic_loss_mod_two_eq_core_sum_of_balanced_core_bound
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hsmall : (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card)) <
      2^(n/2)+2^(n-n/2)+2) :
    tupleBinaryCollisionLoss g b%2=
      (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card))%2 := by
  have hp := Nat.even_iff.mp (even_fibre_overcount_of_core_sum_lt_balanced_sum_add_two g hg b hsmall)
  have he := intrinsic_loss_add_fibre_overcount_eq_core_cube_sum g hg b
  omega

/-- Core charge at most 2n+1 is below the odd-correction threshold
in every dimension. -/
theorem even_fibre_overcount_of_core_sum_le_twice_dimension_add_one
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hsmall : (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card)) ≤ 2*n+1) :
    Even (tupleBinaryFibreOvercount g b) := by
  apply even_fibre_overcount_of_core_sum_lt_balanced_sum_add_two g hg b
  have h1 : 2*(n/2) ≤ 2^(n/2) := Nat.mul_le_pow (by decide) _
  have h2 : 2*(n-n/2) ≤ 2^(n-n/2) := Nat.mul_le_pow (by decide) _
  omega

end MinModulus
