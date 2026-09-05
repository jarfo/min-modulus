/-
# Eliminating global pure-edge stars without three omissions

Avoiding the center of a nonempty pure-edge omission star forces a heavy
coefficient.  Without three omissions, this same avoiding witness is a pure
edge.  The global star condition says it omits the center it avoids, a
contradiction.  No critical range, cyclicity, or odd-stratum bound is needed.
-/
import MinModulus.G1PrivateHeavyTargetPureEdgeFamily

namespace MinModulus

open Finset

/-- Outside the three-omission frontier, any heavy coefficient, including
the anchor, supplies an actual member of the global pure-edge family. -/
theorem witnessPureEdgeOmissionPairs_nonempty_of_heavy_of_no_three
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m + 1) → G) {h : G}
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    {c : Fin (m + 1) → ℤ} (hc : Witness g h c)
    {e : Fin (m + 1)} (he : 2 ≤ c e) :
    (witnessPureEdgeOmissionPairs g h).Nonempty := by
  classical
  have hcard := card_witnessOmissionCoordinates_le_two_of_no_threeDistinctOmissions
    g hthree c hc
  have hupper := witness_coeff_le_card_witnessOmissionCoordinates g hc
    (show c e ≠ -1 by omega)
  have hcardEq : (witnessOmissionCoordinates c).card = 2 := by omega
  have heEq : c e = 2 := by omega
  exact ⟨witnessOmissionCoordinates c,
    (mem_witnessPureEdgeOmissionPairs_iff g h _).2
      ⟨hcardEq, c, e, hc, witnessOmissionCoordinates_exact c, heEq⟩⟩

/-- A nonempty global pure-edge star and failure of common touch force a
three-omission witness.  The heavy coordinate may be the anchor. -/
theorem globalPureEdgeStar_threeDistinctOmissions_of_no_common_touched
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (r : Fin (m + 1))
    (hstar : ∀ P ∈ witnessPureEdgeOmissionPairs g h, r ∈ P)
    (hF : (witnessPureEdgeOmissionPairs g h).Nonempty) :
    WitnessThreeDistinctOmissions g h := by
  classical
  by_contra hthree
  obtain ⟨P, hP⟩ := hF
  obtain ⟨hPcard, edge, _center, hedge, homit, _htwo⟩ :=
    (mem_witnessPureEdgeOmissionPairs_iff g h P).1 hP
  obtain ⟨a, b, _hab, hPpair⟩ := Finset.card_eq_two.mp hPcard
  have hr : r = a ∨ r = b := by simpa [hPpair] using hstar P hP
  obtain ⟨p, hp⟩ : ∃ p : Fin (m + 1),
      ∀ i, edge i = -1 ↔ i = p ∨ i = r := by
    rcases hr with rfl | rfl
    · exact ⟨b, fun i ↦ by simpa [hPpair, or_comm] using homit i⟩
    · exact ⟨a, fun i ↦ by simpa [hPpair] using homit i⟩
  let c := supportAvoidingWitnessAt g hno r
  have hc : Witness g h c := supportAvoidingWitnessAt_isWitness g hno r
  have hcr : c r = 0 := supportAvoidingWitnessAt_eq_zero g hno r
  have hcp : c p = -1 :=
    omitted_other_of_zero_at_exact_pair g hg hh hedge hc p r hp hcr
  obtain ⟨e, he⟩ := exists_coeff_ge_two_of_omit_other_and_zero_at_exact_pair
    g hg hh hedge hc p r hp hcp hcr
  have hcard := card_witnessOmissionCoordinates_le_two_of_no_threeDistinctOmissions
    g hthree c hc
  have hupper := witness_coeff_le_card_witnessOmissionCoordinates g hc
    (show c e ≠ -1 by omega)
  have hcardEq : (witnessOmissionCoordinates c).card = 2 := by omega
  have heEq : c e = 2 := by omega
  have hmem : witnessOmissionCoordinates c ∈ witnessPureEdgeOmissionPairs g h :=
    (mem_witnessPureEdgeOmissionPairs_iff g h _).2
      ⟨hcardEq, c, e, hc, witnessOmissionCoordinates_exact c, heEq⟩
  have hcrNeg := (witnessOmissionCoordinates_exact c r).2 (hstar _ hmem)
  omega

/-- A nonempty pure-edge family reaches common touch, three omissions, or
the established exact-triangle frontier.  There is no residual star arm. -/
theorem witnessPureEdgeOmissionPairs_commonTouched_or_threeOmissions_or_exactTriangle
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0)
    (hF : (witnessPureEdgeOmissionPairs g h).Nonempty) :
    (∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0) ∨
      WitnessThreeDistinctOmissions g h ∨ WitnessExactOmissionTriangle g h := by
  classical
  by_cases hno : ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0
  · exact Or.inl hno
  · right
    rcases witnessPureEdgeOmissionPairs_common_or_exactTriangle g hg hh hF with
      ⟨r, hstar⟩ | htriangle
    · exact Or.inl (globalPureEdgeStar_threeDistinctOmissions_of_no_common_touched
        g hg hh hno r hstar hF)
    · exact Or.inr htriangle

end MinModulus
