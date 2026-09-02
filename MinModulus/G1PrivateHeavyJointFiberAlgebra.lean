/-
# Algebra inside a joint private-heavy escape fiber

Distinct witnesses at the same target have a nonzero difference relation.
Validity forces that difference to violate the witness floor, hence one
coefficient exceeds the other by at least two.  For private witnesses the gap
coordinate is the target owner or is external to the deletion set.

Applying this in both directions to two members of one joint external
`(heavy, escape)` fiber expands the repeated signature: the pair has a common
external omission and two distinct directed gap coordinates, neither equal to
that omission.  The common heavy and escape coordinates are also distinct
from the omission.
-/
import MinModulus.G1PrivateHeavyJointEscapeFibers

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Validity forces an ordered coefficient gap between any two distinct
witnesses at the same target. -/
theorem exists_coefficient_add_two_le_of_distinct_witnesses
    (g : Fin m → G) (hg : ValidTuple g)
    {h : G} {c u : Fin m → ℤ}
    (hc : Witness g h c) (hu : Witness g h u) (hcu : c ≠ u) :
    ∃ i : Fin m, c i + 2 ≤ u i := by
  by_contra hgap
  push Not at hgap
  apply (validTuple_iff_no_zero_witness g).mp hg (c - u)
  apply witness_sub_at_zero_of_floor g hc hu
  · intro hzero
    apply hcu
    funext i
    have hi := congrFun hzero i
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hi
    exact hi
  · intro i
    have hi := hgap i
    simp only [Pi.sub_apply]
    omega

/-- For an ordered pair of distinct private witnesses, a coefficient gap can
only occur at the target witness's owner or outside the deletion set. -/
theorem exists_minimalSupportPrivateCoefficientGap_eq_targetOwner_or_external
    (g : Fin m → G) (hg : ValidTuple g) (h : G)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b u : ↥B) (hbu : b ≠ u) :
    ∃ i : Fin m,
      minimalSupportPrivateWitness g h hmin b i + 2 ≤
          minimalSupportPrivateWitness g h hmin u i ∧
        (i = u ∨ i ∉ B) := by
  have hne : minimalSupportPrivateWitness g h hmin b ≠
      minimalSupportPrivateWitness g h hmin u := by
    intro heq
    exact hbu (minimalSupportPrivateWitness_injective g h hmin heq)
  obtain ⟨i, hi⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
    g hg
      (minimalSupportPrivateWitness_isWitness g h hmin b)
      (minimalSupportPrivateWitness_isWitness g h hmin u) hne
  refine ⟨i, hi, ?_⟩
  by_cases hiu : i = u
  · exact Or.inl hiu
  · right
    intro hiB
    have huzero := minimalSupportPrivateWitness_eq_zero_of_ne
      g h hmin u hiB hiu
    have hbfloor :=
      (minimalSupportPrivateWitness_isWitness g h hmin b).2.1 i
    omega

/-- A pair in one joint external heavy/escape fiber carries a common omission
and two mutually directed, distinct coefficient-gap coordinates. -/
theorem minimalSupportPrivateJointExternalHeavyEscapeFiber_pairExpansion
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e : Fin (m + 1))
    (b u : ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (hb : b ∈ minimalSupportPrivateJointExternalHeavyEscapeFiber
      g hg h t q ht hq hmin hqzero z e)
    (hu : u ∈ minimalSupportPrivateJointExternalHeavyEscapeFiber
      g hg h t q ht hq hmin hqzero z e)
    (hbu : b ≠ u) :
    ∃ w i j : Fin (m + 1),
      w ∉ B ∧
      minimalSupportPrivateWitness g h hmin b.val w = -1 ∧
      minimalSupportPrivateWitness g h hmin u.val w = -1 ∧
      2 ≤ minimalSupportPrivateWitness g h hmin b.val z ∧
      2 ≤ minimalSupportPrivateWitness g h hmin u.val z ∧
      2 * q e + 2 ≤ minimalSupportPrivateWitness g h hmin b.val e ∧
      2 * q e + 2 ≤ minimalSupportPrivateWitness g h hmin u.val e ∧
      minimalSupportPrivateWitness g h hmin b.val i + 2 ≤
        minimalSupportPrivateWitness g h hmin u.val i ∧
      (i = u.val ∨ i ∉ B) ∧
      minimalSupportPrivateWitness g h hmin u.val j + 2 ≤
        minimalSupportPrivateWitness g h hmin b.val j ∧
      (j = b.val ∨ j ∉ B) ∧
      i ≠ j ∧ i ≠ w ∧ j ≠ w ∧ z ≠ w ∧ e ≠ w := by
  have hbJoint :
      b ∈ minimalSupportPrivateDoubleExternalHeavyVertices
          g hg h t q ht hq hmin hqzero z ∧
        minimalSupportPrivateHeavyEscapeCoordinate
          g hg h t q ht hq hmin hqzero b = e := by
    simpa [minimalSupportPrivateJointExternalHeavyEscapeFiber] using hb
  have huJoint :
      u ∈ minimalSupportPrivateDoubleExternalHeavyVertices
          g hg h t q ht hq hmin hqzero z ∧
        minimalSupportPrivateHeavyEscapeCoordinate
          g hg h t q ht hq hmin hqzero u = e := by
    simpa [minimalSupportPrivateJointExternalHeavyEscapeFiber] using hu
  have hbHeavyFiber : b ∈ minimalSupportPrivateExternalHeavyFiber
      g h hmin z := by
    exact (Finset.mem_filter.mp hbJoint.1).1
  have huHeavyFiber : u ∈ minimalSupportPrivateExternalHeavyFiber
      g h hmin z := by
    exact (Finset.mem_filter.mp huJoint.1).1
  have hbCoordinate : minimalSupportPrivateHeavyCoordinate
      g h hmin b = z :=
    (mem_minimalSupportPrivateExternalHeavyFiber_iff
      g h hmin z b).mp hbHeavyFiber |>.2
  have huCoordinate : minimalSupportPrivateHeavyCoordinate
      g h hmin u = z :=
    (mem_minimalSupportPrivateExternalHeavyFiber_iff
      g h hmin z u).mp huHeavyFiber |>.2
  have hbHeavy := minimalSupportPrivateHeavyCoordinate_spec g h hmin b
  have huHeavy := minimalSupportPrivateHeavyCoordinate_spec g h hmin u
  rw [hbCoordinate] at hbHeavy
  rw [huCoordinate] at huHeavy
  have hbEscapeMem := minimalSupportPrivateHeavyEscapeCoordinate_mem
    g hg h t q ht hq hmin hqzero b
  have huEscapeMem := minimalSupportPrivateHeavyEscapeCoordinate_mem
    g hg h t q ht hq hmin hqzero u
  have hbEscape := (mem_minimalSupportPrivateEscapePairs_iff
    g h q hmin b.val _).mp hbEscapeMem
  have huEscape := (mem_minimalSupportPrivateEscapePairs_iff
    g h q hmin u.val _).mp huEscapeMem
  rw [hbJoint.2] at hbEscape
  rw [huJoint.2] at huEscape
  have howners : b.val ≠ u.val := by
    intro hval
    exact hbu (Subtype.ext hval)
  obtain ⟨w, hwExternal, hbw, huw⟩ :=
    exists_external_common_omission_of_distinct_minimalSupportPrivateWitnesses
      g hg hh hmin b.val u.val howners
  obtain ⟨i, hi, hiLocation⟩ :=
    exists_minimalSupportPrivateCoefficientGap_eq_targetOwner_or_external
      g hg h hmin b.val u.val howners
  obtain ⟨j, hj, hjLocation⟩ :=
    exists_minimalSupportPrivateCoefficientGap_eq_targetOwner_or_external
      g hg h hmin u.val b.val (Ne.symm howners)
  have hij : i ≠ j := by
    intro hij
    rw [hij] at hi
    omega
  have hiw : i ≠ w := by
    intro hiw
    rw [hiw, hbw, huw] at hi
    omega
  have hjw : j ≠ w := by
    intro hjw
    rw [hjw, hbw, huw] at hj
    omega
  have hzw : z ≠ w := by
    intro hzw
    rw [hzw, hbw] at hbHeavy
    omega
  have hew : e ≠ w := by
    intro hew
    subst e
    have hqfloor := hq.2.1 w
    rw [hbw] at hbEscape
    omega
  exact ⟨w, i, j, hwExternal, hbw, huw, hbHeavy, huHeavy,
    hbEscape, huEscape, hi, hiLocation, hj, hjLocation,
    hij, hiw, hjw, hzw, hew⟩

end MinModulus
