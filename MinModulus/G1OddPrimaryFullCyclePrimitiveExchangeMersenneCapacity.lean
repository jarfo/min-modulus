/-
# Mersenne arithmetic for the primitive middle capacity residual

The full leaf permutation was not used by the residue-capacity argument.
Reinstalling its doubling recurrence gives the missing arithmetic constraint:
if the translated leaf range spans `Z*y`, then `addOrderOf y` divides the
full-cycle Mersenne number.  In the live full-odd-factor branch this says

    q | 2^d - 1.

An odd proper divisor has cofactor at least three.  Combining this divisor
gap with the all-layer capacity of the equal-coset arm, and with the existing
two-coset capacity of the separated arm, produces an exact-Mersenne-or-
threefold-capacity split.  This is the first direct coupling of the leaf-cycle
arithmetic to the exhaustive residue partition.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangePrimaryUnionCapacity

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- If one fixed-point-free full cycle acts by doubling on a family spanning
`Z*y`, then the order of `y` divides the Mersenne number of the full carrier
cardinality. -/
theorem addOrderOf_dvd_mersenne_of_isCycle_doubling_span
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : Equiv.Perm α) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i) (disp : α → G)
    (hdouble : ∀ i, disp (R i) = 2 • disp i)
    (y : G)
    (hspan : AddSubgroup.closure (Set.range disp) =
      AddSubgroup.zmultiples y) :
    addOrderOf y ∣ 2 ^ Fintype.card α - 1 := by
  have hsupport : R.support = Finset.univ := by
    ext i
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    exact hRne i
  have horder : orderOf R = Fintype.card α := by
    rw [hcycle.orderOf, hsupport]
    simp
  have hperiod : ∀ i, R^[Fintype.card α] i = i := by
    intro i
    rw [Equiv.Perm.iterate_eq_pow, ← horder, pow_orderOf_eq_one]
    rfl
  have htorsion : ∀ i,
      (2 ^ Fintype.card α - 1) • disp i = 0 := by
    intro i
    exact pow_two_sub_one_nsmul_eq_zero_of_iterate_eq
      R disp hdouble (hperiod i)
  have hclosure : AddSubgroup.closure (Set.range disp) ≤
      (nsmulAddMonoidHom (2 ^ Fintype.card α - 1)).ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨i, rfl⟩
    change (2 ^ Fintype.card α - 1) • disp i = 0
    exact htorsion i
  have hyClosure : y ∈ AddSubgroup.closure (Set.range disp) := by
    rw [hspan]
    exact AddSubgroup.mem_zmultiples y
  have hyTorsion := hclosure hyClosure
  rw [AddMonoidHom.mem_ker] at hyTorsion
  exact addOrderOf_dvd_of_nsmul_eq_zero hyTorsion

/-- A positive divisor of an odd number is either the whole number or has
cofactor at least three. -/
theorem eq_or_three_mul_le_of_dvd_of_odd
    {q M : ℕ} (hM : Odd M) (hdvd : q ∣ M) :
    q = M ∨ 3 * q ≤ M := by
  let k := M / q
  have hfactor : q * k = M := by
    exact Nat.mul_div_cancel' hdvd
  have hqkOdd : Odd (q * k) := by
    rw [hfactor]
    exact hM
  have hkOdd : Odd k := Nat.Odd.of_mul_right hqkOdd
  rcases hkOdd with ⟨a, ha⟩
  by_cases hkOne : k = 1
  · left
    simpa only [hkOne, mul_one] using hfactor
  · right
    have hkThree : 3 ≤ k := by omega
    calc
      3 * q ≤ k * q := Nat.mul_le_mul_right q hkThree
      _ = q * k := Nat.mul_comm k q
      _ = M := hfactor

/-- Numerical endpoint obtained by coupling the exhaustive residue-capacity
split to a full doubling cycle.  Either the odd factor is the exact Mersenne
number, or one of the two middle arms has a threefold central-layer product
below that Mersenne number.  In the merged arm `u` contains all `d` leaf
coordinates; its full `u`-`t`-`f` capacity and critical residual are retained.
-/
theorem PrimitiveMiddleWindowedCriticalCosetResidual.mersenneCapacitySplit
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hRcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ 6 * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y)
    (hresidual :
      PrimitiveMiddleWindowedCriticalCosetResidual g y B leaf) :
    q = 2 ^ d - 1 ∨
      (∃ u t f : ℕ,
        d ≤ u ∧ 3 ≤ t ∧
        (∀ i j k : ℕ, u.choose i * t.choose j * f.choose k ≤ q) ∧
        3 * (u.choose (u / 2) * t.choose (t / 2) *
          f.choose (f / 2)) ≤ 2 ^ d - 1 ∧
        48 * (u.choose (u / 2) * f.choose (f / 2)) < 2 ^ B.card) ∨
      (∃ s : ℕ,
        16 ≤ s ∧
        (∀ i j : ℕ, d.choose i * (s + 1).choose j ≤ q) ∧
        3 * (d.choose (d / 2) * (s + 1).choose ((s + 1) / 2)) ≤
          2 ^ d - 1 ∧
        388960 * d.choose (d / 2) < 2 ^ B.card) := by
  classical
  let disp : Fin d → ZMod (2 ^ 6 * q) :=
    fun i ↦ g (leaf i) - base
  have horderDvd : addOrderOf y ∣ 2 ^ d - 1 := by
    have h := addOrderOf_dvd_mersenne_of_isCycle_doubling_span
      R hRcycle hRne disp (by simpa only [disp] using hdouble) y
        (by simpa only [disp] using hspan)
    simpa using h
  have horder : addOrderOf y = q :=
    Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd
  have hqDvd : q ∣ 2 ^ d - 1 := by
    simpa only [horder] using horderDvd
  have hd : 0 < d := by
    by_contra hdZero
    have hdEq : d = 0 := by omega
    subst d
    exact Fin.elim0 (Classical.choose hRcycle)
  rcases eq_or_three_mul_le_of_dvd_of_odd
      (odd_two_pow_sub_one hd) hqDvd with hqExact | hproper
  · exact Or.inl hqExact
  · right
    rcases hresidual with
      ⟨p, S, k₀, hprimitive, hScard, hSsub, hmiddle, hrows,
        hScomplete, hwindow, hCcard, hcase⟩
    let r : Fin n := primitiveMiddleInsertedCoordinate p k₀
    let C : Finset (Fin n) := insert r S
    let L : Finset (Fin n) :=
      (Finset.univ : Finset (Fin d)).image leaf
    let U : Finset (Fin n) := L ∪ C
    rcases hcase with hmerged | hseparated
    · rcases hmerged with
        ⟨_hUbase, hUcoset, _hUgap, _hfive, _hseparated,
          hsecondary, _hsecondaryCritical⟩
      have hrU : r ∈ U := by
        exact Finset.mem_union_right L (Finset.mem_insert_self r S)
      have hUnonempty : U.Nonempty := ⟨r, hrU⟩
      have hSrows : ∀ b : ↥B, (b : Fin n) ∈ S →
          p.weight b = 2 * k₀ := by
        intro b hbS
        exact (hrows b hbS).1
      have hthree := hsecondary.toThreeResiduePartition
        g y B U S p k₀ hprimitive hyq hfullOdd hmiddle hwindow
          hSsub hSrows hScomplete
      obtain ⟨T, F, hTcard, _hpartition, _hFsub, hcap, hcrit⟩ :=
        hthree.exists_primaryUnionCriticalBound
          g hg y B U S p k₀ hyq hfullOdd hretained hcritical
            hUnonempty hUcoset hrU hScomplete
      have hLcard : L.card = d := by
        simp only [L]
        rw [Finset.card_image_of_injective _ hleaf]
        simp
      have hdU : d ≤ U.card := by
        rw [← hLcard]
        exact Finset.card_le_card Finset.subset_union_left
      have hcentralCap :=
        hcap (U.card / 2) (T.card / 2) (F.card / 2)
      have hcentralMersenne :
          3 * (U.card.choose (U.card / 2) *
            T.card.choose (T.card / 2) *
            F.card.choose (F.card / 2)) ≤ 2 ^ d - 1 :=
        (Nat.mul_le_mul_left 3 hcentralCap).trans hproper
      exact Or.inl ⟨U.card, T.card, F.card, hdU, hTcard,
        hcap, hcentralMersenne, hcrit⟩
    · rcases hseparated with ⟨_hcross, hcap, hcrit⟩
      have hcentralCap :=
        hcap (d / 2) ((S.card + 1) / 2)
      have hcentralMersenne :
          3 * (d.choose (d / 2) *
            (S.card + 1).choose ((S.card + 1) / 2)) ≤
              2 ^ d - 1 :=
        (Nat.mul_le_mul_left 3 hcentralCap).trans hproper
      exact Or.inr ⟨S.card, hScard, hcap, hcentralMersenne, hcrit⟩

end MinModulus
