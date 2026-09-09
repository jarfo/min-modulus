import MinModulus.OddModulusCorrectionParity
import MinModulus.OddCorrectionCoreBoundary

namespace MinModulus
open Finset
open scoped Classical

/-- In dimension at least two, the balanced sum of powers is even. -/
theorem even_balanced_power_sum_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    Even (2^(n/2)+2^(n-n/2)) := by
  have h1 : Even (2^(n/2)) := by
    apply even_iff_two_dvd.mpr
    simpa only [pow_one] using pow_dvd_pow 2 (by omega : 1 ≤ n/2)
  have h2 : Even (2^(n-n/2)) := by
    apply even_iff_two_dvd.mpr
    simpa only [pow_one] using pow_dvd_pow 2 (by omega : 1 ≤ n-n/2)
  exact h1.add h2

/-- Odd-modulus parity leaves no next-charge value for odd correction:
the relaxed bound C<=S+3 still forces the exact boundary C=S+2. -/
theorem odd_cyclic_core_boundary_of_odd_overcount_and_relaxed_bound
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hodd : Odd (tupleBinaryFibreOvercount g b))
    (hbound : (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card)) ≤
      2^(n/2)+2^(n-n/2)+3) :
    (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card))=
      2^(n/2)+2^(n-n/2)+2 := by
  have hlow := balanced_power_sum_add_two_le_core_sum_of_odd_overcount g hg b hodd
  have hC := Nat.even_iff.mp (even_core_sum_of_odd_cyclic_overcount (by omega) hN g hg b hodd)
  have hS := Nat.even_iff.mp (even_balanced_power_sum_of_two_le hn)
  omega

/-- At odd moduli, excluding the four-core family extends the even
correction criterion one unit beyond the balanced charge boundary. -/
theorem even_overcount_of_odd_cyclic_relaxed_bound_and_card_ne_four
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hbound : (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card)) ≤
      2^(n/2)+2^(n-n/2)+3) (hne : (tupleBinaryCollisionCores g b).card ≠ 4) :
    Even (tupleBinaryFibreOvercount g b) := by
  apply Nat.even_iff.mpr
  by_contra h
  have hodd : Odd (tupleBinaryFibreOvercount g b) := Nat.odd_iff.mpr (by omega)
  have he := odd_cyclic_core_boundary_of_odd_overcount_and_relaxed_bound hn hN g hg b hodd hbound
  exact hne (binary_core_card_eq_four_at_odd_core_boundary g hg b hodd he)

/-- The relaxed odd-modulus budget preserves equality of core and
loss parity outside the classified four-core boundary. -/
theorem loss_mod_two_eq_core_sum_of_odd_cyclic_relaxed_bound
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hbound : (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card)) ≤
      2^(n/2)+2^(n-n/2)+3) (hne : (tupleBinaryCollisionCores g b).card ≠ 4) :
    tupleBinaryCollisionLoss g b%2=
      (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card))%2 := by
  have hp := Nat.even_iff.mp (even_overcount_of_odd_cyclic_relaxed_bound_and_card_ne_four hn hN g hg b hbound hne)
  have he := intrinsic_loss_add_fibre_overcount_eq_core_cube_sum g hg b
  omega

/-- At the charge value immediately above the odd-correction boundary,
an odd-modulus tuple has even correction and odd intrinsic loss. -/
theorem even_overcount_and_odd_loss_at_next_odd_cyclic_charge
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hcharge : (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card))=
      2^(n/2)+2^(n-n/2)+3) :
    Even (tupleBinaryFibreOvercount g b) ∧ Odd (tupleBinaryCollisionLoss g b) := by
  apply even_overcount_and_odd_loss_of_odd_cyclic_core_sum (by omega) hN g hg b
  apply Nat.odd_iff.mpr
  have hs := Nat.even_iff.mp (even_balanced_power_sum_of_two_le hn)
  omega

end MinModulus
