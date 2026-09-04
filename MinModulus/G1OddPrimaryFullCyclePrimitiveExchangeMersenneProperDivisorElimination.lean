/-
# Proper Mersenne divisors are incompatible with a valid full leaf cycle

The two proper-divisor capacity arms retain more structure than their
numerical statements display: all `d` leaf coordinates form a valid subtuple
inside one coset of the cyclic odd kernel.  The subgroup-scale set-free bound
therefore gives `2^(d-1) <= q`.  If `q` is a proper divisor of the odd number
`2^d-1`, its cofactor is at least three, which is immediately incompatible
with that lower bound.

This argument is dimension-free and eliminates both proper-divisor arms at
their common source.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneLayerBucketEndpoint

namespace MinModulus

open Finset

variable {n : ℕ}

/-- At every two-adic stratum, a valid injective full doubling cycle spanning
the full odd kernel forces the odd factor to be the whole Mersenne number.
The proof is independent of the ambient two-adic exponent. -/
theorem oddFactor_eq_mersenne_of_valid_fullCycle_doubling_span
    {d t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hRcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ t * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y) :
    q = 2 ^ d - 1 := by
  classical
  let disp : Fin d → ZMod (2 ^ t * q) :=
    fun i ↦ g (leaf i) - base
  have hd : 0 < d := by
    by_contra hdZero
    have hdEq : d = 0 := by omega
    subst d
    exact Fin.elim0 (Classical.choose hRcycle)
  have horderDvd : addOrderOf y ∣ 2 ^ d - 1 := by
    have h := addOrderOf_dvd_mersenne_of_isCycle_doubling_span
      R hRcycle hRne disp (by simpa only [disp] using hdouble) y
        (by simpa only [disp] using hspan)
    simpa using h
  have horder : addOrderOf y = q :=
    Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd
  have hqDvd : q ∣ 2 ^ d - 1 := by
    simpa only [horder] using horderDvd
  let L : Finset (Fin n) :=
    (Finset.univ : Finset (Fin d)).image leaf
  have hLnonempty : L.Nonempty := by
    exact ⟨leaf ⟨0, hd⟩,
      Finset.mem_image.mpr ⟨⟨0, hd⟩, Finset.mem_univ _, rfl⟩⟩
  have hdispMem : ∀ i : Fin d,
      disp i ∈ AddSubgroup.zmultiples y := by
    intro i
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨i, rfl⟩
  have hLcoset : ∀ b ∈ L, ∀ c ∈ L,
      g b - g c ∈ AddSubgroup.zmultiples y := by
    intro b hb c hc
    rcases Finset.mem_image.mp hb with ⟨i, _hi, rfl⟩
    rcases Finset.mem_image.mp hc with ⟨j, _hj, rfl⟩
    have hmem := (AddSubgroup.zmultiples y).sub_mem (hdispMem i) (hdispMem j)
    convert hmem using 1
    simp only [disp]
    abel
  have hlower : 2 ^ (d - 1) ≤ q := by
    have h := two_pow_pred_le_addOrderOf_of_valid_kernelCoset
      g hg y L hLnonempty hLcoset
    rw [horder] at h
    simpa only [L, Finset.card_image_of_injective _ hleaf,
      Finset.card_univ, Fintype.card_fin] using h
  rcases eq_or_three_mul_le_of_dvd_of_odd
      (odd_two_pow_sub_one hd) hqDvd with hexact | hproper
  · exact hexact
  · have hpow : 2 ^ d = 2 * 2 ^ (d - 1) := by
      cases d with
      | zero => omega
      | succ k => simp [pow_succ, Nat.mul_comm]
    have hpositive : 0 < 2 ^ (d - 1) := pow_pos (by decide) _
    omega

/-- A valid injective full doubling cycle spanning the full odd kernel forces
the kernel order to be the whole Mersenne number, not a proper divisor. -/
theorem addOrderOf_eq_mersenne_of_valid_fullCycle_doubling_span
    {d q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hRcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ 6 * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y) :
    q = 2 ^ d - 1 :=
  oddFactor_eq_mersenne_of_valid_fullCycle_doubling_span
    g hg y hyq hfullOdd leaf hleaf R hRcycle hRne base hdouble hspan

/-- In particular, the full windowed critical coset residual's Mersenne split
always takes its exact branch; its two quantified proper-divisor outputs are
unreachable. -/
theorem PrimitiveMiddleWindowedCriticalCosetResidual.mersenneOrder_eq
    {d q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hRcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ 6 * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y)
    (_hresidual : PrimitiveMiddleWindowedCriticalCosetResidual g y B leaf) :
    q = 2 ^ d - 1 :=
  addOrderOf_eq_mersenne_of_valid_fullCycle_doubling_span
    g hg y hyq hfullOdd leaf hleaf R hRcycle hRne base hdouble hspan

end MinModulus
