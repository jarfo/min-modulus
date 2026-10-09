/-
Copyright (c) 2026 José A. R. Fonollosa. All rights reserved.
Released under Apache 2.0 license.
-/
import MinModulus.StratumOneCancel

/-!
# The parity half of a stratum-one rival

At the first even stratum `N = 2 * M` with `M` odd, CRT splits
`ZMod N ≅ ZMod 2 × ZMod M`.  `StratumOneCancel.sheet_gap_of_valid` says that a
nontrivial multiset matching the target modulo `M` must miss it by exactly the
sheet `M`.  Reading that identity in the *other* CRT factor is this file: the
parity vector of the tuple must satisfy one affine condition for every such
multiset.  This is Glynn's `±1` factor of the stratum-one scheme, and it is the
input the rigidity branch of the classification consumes.
-/

namespace MinModulus

namespace StratumOne

/-- The parity component of the first even stratum. -/
abbrev parityHom (M : ℕ) : ZMod (2 * M) →+* ZMod 2 :=
  ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)

theorem natCast_odd_eq_one {M : ℕ} (hodd : Odd M) : ((M : ℕ) : ZMod 2) = 1 := by
  have h : M % 2 = 1 := Nat.odd_iff.mp hodd
  calc ((M : ℕ) : ZMod 2) = ((M % 2 : ℕ) : ZMod 2) := (ZMod.natCast_mod M 2).symm
    _ = 1 := by rw [h]; norm_num

/-- **The parity condition.**  In a valid tuple at the first even stratum with
`M` odd, every nontrivial multiset that matches the target modulo `M` forces one
affine condition on the parity vector: its parity sum is *off by one*. -/
theorem sheet_parity_of_valid {n M : ℕ} (hM : 1 ≤ M) (hodd : Odd M)
    {g : Fin n → ZMod (2 * M)} (hg : ValidTuple g) {k : Fin n → ℕ}
    (hcard : ∑ j, k j = n) (hne : ∃ j, k j ≠ 1)
    (hmod : ZMod.castHom (dvd_mul_left M 2) (ZMod M) ((∑ j, k j • g j) - ∑ j, g j) = 0) :
    ∑ j, k j • parityHom M (g j) = (∑ j, parityHom M (g j)) + 1 := by
  have h := congrArg (parityHom M) (sheet_gap_of_valid hM hg hcard hne hmod)
  rw [map_sum, map_add, map_sum, map_natCast, natCast_odd_eq_one hodd] at h
  simpa only [map_nsmul] using h

/-- The same condition written multiplicatively: Glynn's functional evaluated at
the parity vector is `1`. -/
theorem sheet_parity_mul_of_valid {n M : ℕ} (hM : 1 ≤ M) (hodd : Odd M)
    {g : Fin n → ZMod (2 * M)} (hg : ValidTuple g) {k : Fin n → ℕ}
    (hcard : ∑ j, k j = n) (hne : ∃ j, k j ≠ 1)
    (hmod : ZMod.castHom (dvd_mul_left M 2) (ZMod M) ((∑ j, k j • g j) - ∑ j, g j) = 0) :
    ∑ j, ((k j : ZMod 2) + 1) * parityHom M (g j) = 1 := by
  have h := sheet_parity_of_valid hM hodd hg hcard hne hmod
  have hexp : ∀ j, ((k j : ZMod 2) + 1) * parityHom M (g j)
      = k j • parityHom M (g j) + parityHom M (g j) := by
    intro j; rw [add_mul, one_mul, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => hexp j), Finset.sum_add_distrib, h]
  ring_nf
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2]
  ring

end StratumOne

end MinModulus
