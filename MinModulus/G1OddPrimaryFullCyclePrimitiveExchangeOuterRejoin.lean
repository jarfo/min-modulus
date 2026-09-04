/-
# Rejoining the exact outer family to the middle exchange path

An outer canonical row still has two coefficient `-1` positions: its owner
and one retained coordinate.  Exchanging the latter into the transversal
leaves a retained difference of primitive quotient order `64`.  The two outer
orientations therefore use exactly the same literal exchange sets as the
middle parameters `0` and `-1`, respectively.

Thus the common outer family is not a parallel terminal.  Either one of its
exchanges enters the three-retained C2 arm, or the entire family rejoins the
existing `PrimitiveMiddleAllExactExchangeFamily` pipeline.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneProperDivisorElimination

namespace MinModulus

open Finset

variable {n : ℕ}

/-- For an outer quotient parameter, exchange the retained coordinate with
coefficient `-1`.  The new retained difference still has primitive order
`64`. -/
theorem primitive_outerParameter_exchange_geometry
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (x z b : Fin n) (k : ℤ)
    (hprimitive :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g x - g z)) =
          64)
    (hquotient :
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g b - g z) =
        -(k •
          (QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g x - g z)))
    (houter : k = -2 ∨ k = 1) :
    (k = -2 ∧
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g b - g x)) = 64) ∨
      (k = 1 ∧
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g b - g z)) = 64) := by
  let H : AddSubgroup (ZMod (2 ^ 6 * q)) :=
    AddSubgroup.zmultiples y
  let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
    QuotientAddGroup.mk' H
  let deltaQ := pi (g x - g z)
  have hprimitive' : addOrderOf deltaQ = 64 := by
    simpa only [deltaQ, pi, H] using hprimitive
  rcases houter with hk | hk
  · left
    refine ⟨hk, ?_⟩
    have hdecomp : g b - g x = (g b - g z) - (g x - g z) := by
      abel
    have hq : pi (g b - g x) = deltaQ := by
      rw [hdecomp, map_sub]
      have hb : pi (g b - g z) = (2 : ℤ) • deltaQ := by
        simpa only [pi, H, deltaQ, hk, neg_zsmul, Int.reduceNeg,
          neg_neg] using hquotient
      rw [hb]
      module
    simpa only [pi, H, hq] using hprimitive'
  · right
    refine ⟨hk, ?_⟩
    have hq : pi (g b - g z) = -deltaQ := by
      simpa only [pi, H, deltaQ, hk, one_zsmul] using hquotient
    simpa only [pi, H, hq, addOrderOf_neg] using hprimitive'

/-- The canonical residue class has only one exchange continuation: C2, or
the already established all-exact middle exchange family.  In particular the
outer pure-heavy family is no longer a separate terminal. -/
theorem PrimitiveCanonicalResidueClass.three_or_allExactExchangeFamily
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hretained : n - B.card = 2)
    (hclass : PrimitiveCanonicalResidueClass g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      PrimitiveMiddleAllExactExchangeFamily g y B := by
  classical
  rcases hclass with
    ⟨p, S, k₀, hprimitive, hScard, hSsub, _hk₀Mem, hrow,
      _hwindow, hsplit⟩
  rcases hsplit with hmiddle | ⟨houter, _howner⟩
  · have hfamily : PrimitiveMiddleExchangeFamily g y B := by
      refine ⟨p, S, k₀, hScard, hSsub, hmiddle, ?_⟩
      intro b hbS
      have hr := hrow b hbS
      refine ⟨hr.2.1, ?_⟩
      exact primitive_middleParameter_geometry
        g y p.x p.z (b : Fin n) k₀ hprimitive
          hr.2.2.1 hr.2.2.2 hmiddle
    exact hfamily.three_or_allExactExchangeFamily
      g hg hh hne hunique hno y hyq hfullOdd B hmin hretained hminimal
  · have houtcomes : ∀ b : ↥B, (b : Fin n) ∈ S →
        (∃ B₀ : Finset (Fin n),
            MinimalCyclicKernelSupportTransversal g y B₀ ∧
              3 ≤ n - B₀.card) ∨
          (k₀ = -2 ∧
            PrimitiveTwoRetainedSixthStratumRows g y
              (insert p.z (B.erase (b : Fin n)))) ∨
          (k₀ = 1 ∧
            PrimitiveTwoRetainedSixthStratumRows g y
              (insert p.x (B.erase (b : Fin n)))) := by
      intro b hbS
      have hgeometry := primitive_outerParameter_exchange_geometry
        g y p.x p.z (b : Fin n) k₀ hprimitive (hrow b hbS).2.2.2 houter
      rcases hgeometry with hminus | hplus
      · have hcomplementReverse : Finset.univ \ B = {p.z, p.x} := by
          simpa only [pair_comm] using p.complement_eq
        rcases exists_minimalCyclicKernelTransversal_exchange_fixed_primitive_or_three
          g hg hh hne hunique hno y hyq hfullOdd hmin hretained
            b.property p.z_not_mem p.x_not_mem p.x_ne_z.symm
            hcomplementReverse hminus.2 hminimal with hthree | hexact
        · exact Or.inl hthree
        · exact Or.inr (Or.inl ⟨hminus.1, hexact⟩)
      · rcases exists_minimalCyclicKernelTransversal_exchange_fixed_primitive_or_three
          g hg hh hne hunique hno y hyq hfullOdd hmin hretained
            b.property p.x_not_mem p.z_not_mem p.x_ne_z
            p.complement_eq hplus.2 hminimal with hthree | hexact
        · exact Or.inl hthree
        · exact Or.inr (Or.inr ⟨hplus.1, hexact⟩)
    by_cases hthree :
        ∃ b : ↥B, (b : Fin n) ∈ S ∧
          ∃ B₀ : Finset (Fin n),
            MinimalCyclicKernelSupportTransversal g y B₀ ∧
              3 ≤ n - B₀.card
    · left
      obtain ⟨_b, _hbS, B₀, hB₀⟩ := hthree
      exact ⟨B₀, hB₀⟩
    · right
      let kmid : ℤ := if k₀ = -2 then 0 else -1
      have hkmid : kmid = -1 ∨ kmid = 0 := by
        rcases houter with hk | hk
        · right
          simp [kmid, hk]
        · left
          simp [kmid, hk]
      refine ⟨p, S, kmid, hScard, hSsub, hkmid, ?_⟩
      intro b hbS
      rcases houtcomes b hbS with hB₀ | hminus | hplus
      · exact (hthree ⟨b, hbS, hB₀⟩).elim
      · have hzeroNe : (0 : ℤ) ≠ -1 := by omega
        simpa only [kmid, hminus.1, if_true, middleExchangeSet,
          hzeroNe, if_false]
          using hminus.2
      · have honeNe : (1 : ℤ) ≠ -2 := by omega
        simpa only [kmid, hplus.1, honeNe, if_false, middleExchangeSet,
          if_true] using hplus.2

end MinModulus
