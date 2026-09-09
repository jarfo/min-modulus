import MinModulus.MidpointFibreOvercountParity

namespace MinModulus
open Finset
open scoped Classical

/-- Odd correction at an odd cyclic modulus forces exactly one
attained midpoint value, since doubling has no nontrivial kernel. -/
theorem odd_cyclic_attained_midpoint_card_eq_one_of_odd_overcount
    {n N : ℕ} [NeZero N] (hn : 0 < n) (hN : Odd N)
    (g : Fin n → ZMod N) (b : ZMod N) (hodd : Odd (tupleBinaryFibreOvercount g b)) :
    ((tupleBinarySumImage g b).filter (fun z ↦ 2 • z=∑ i, (g i+b))).card=1 := by
  classical
  let M := (tupleBinarySumImage g b).filter (fun z ↦ 2 • z=∑ i, (g i+b))
  change M.card=1
  have hle : M.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro z hz w hw
    apply add_self_injective_zmod hN
    have he := (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2.symm
    simpa only [two_nsmul] using he
  obtain ⟨z,hz,hmid,_⟩ := exists_four_point_midpoint_of_odd_fibre_overcount hn g b hodd
  have hpos : 0 < M.card := by
    apply Finset.card_pos.mpr
    refine ⟨z,Finset.mem_filter.mpr ⟨hz,?_⟩⟩
    simpa only [Finset.sum_eq_multiset_sum] using hmid
  omega

/-- At odd cyclic moduli, odd full correction forces odd intrinsic
loss without any tuple-validity or fibre-size assumption. -/
theorem odd_intrinsic_loss_of_odd_cyclic_overcount
    {n N : ℕ} [NeZero N] (hn : 0 < n) (hN : Odd N)
    (g : Fin n → ZMod N) (b : ZMod N) (hodd : Odd (tupleBinaryFibreOvercount g b)) :
    Odd (tupleBinaryCollisionLoss g b) := by
  have hc := odd_cyclic_attained_midpoint_card_eq_one_of_odd_overcount hn hN g b hodd
  have hp := intrinsic_loss_mod_two_eq_midpoint_count hn g b
  simp only [Finset.sum_eq_multiset_sum] at hp hc
  apply Nat.odd_iff.mpr
  omega

/-- For valid odd cyclic tuples, odd correction makes the total
complementary-core charge even at every affine shift. -/
theorem even_core_sum_of_odd_cyclic_overcount
    {n N : ℕ} [NeZero N] (hn : 0 < n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hodd : Odd (tupleBinaryFibreOvercount g b)) :
    Even (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card)) := by
  have hL := Nat.odd_iff.mp (odd_intrinsic_loss_of_odd_cyclic_overcount hn hN g b hodd)
  have hD := Nat.odd_iff.mp hodd
  have he := intrinsic_loss_add_fibre_overcount_eq_core_cube_sum g hg b
  apply Nat.even_iff.mpr
  omega

/-- Odd core charge at an odd modulus forces even correction and
odd actual loss, with no bound on charge, loss, or fibre multiplicity. -/
theorem even_overcount_and_odd_loss_of_odd_cyclic_core_sum
    {n N : ℕ} [NeZero N] (hn : 0 < n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hodd : Odd (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card))) :
    Even (tupleBinaryFibreOvercount g b) ∧ Odd (tupleBinaryCollisionLoss g b) := by
  have hC := Nat.odd_iff.mp hodd
  have hD : Even (tupleBinaryFibreOvercount g b) := by
    apply Nat.even_iff.mpr
    by_contra h
    have ho : Odd (tupleBinaryFibreOvercount g b) := Nat.odd_iff.mpr (by omega)
    have he := Nat.even_iff.mp (even_core_sum_of_odd_cyclic_overcount hn hN g hg b ho)
    omega
  refine ⟨hD,?_⟩
  have hp := Nat.even_iff.mp hD
  have he := intrinsic_loss_add_fibre_overcount_eq_core_cube_sum g hg b
  apply Nat.odd_iff.mpr
  omega

end MinModulus
