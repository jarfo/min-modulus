/-
# Location of the heavy coordinate of a star-avoiding witness

The fixed star leaves are all omissions of the avoiding witness.  A heavy
coordinate of that witness is therefore neither a leaf nor the zero-valued
star center.  If it is also outside the minimal transversal, it consumes one
additional external coordinate beyond the center and all leaves.  Otherwise
it is an internal heavy coordinate in the transversal.

This is the first normalization of the heavy star branch: outside a sharp
four-part capacity bound, the heavy coordinate is forced into `B`.
-/
import MinModulus.G1PrivateHeavySelfHeavyStarCapacity

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- A heavy coordinate disjoint from a fixed external omission reservoir and
its zero center is either in the transversal or pays one further unit of
ambient capacity. -/
theorem heavyCoordinate_mem_transversal_or_card_add_reservoir_add_two_le
    (c : Fin (m + 1) → ℤ)
    (B L : Finset (Fin (m + 1))) (z e : Fin (m + 1))
    (hLC : L ⊆ (Finset.univ \ B).erase z)
    (hLO : L ⊆ witnessOmissionCoordinates c)
    (hzB : z ∉ B) (hz : c z = 0) (he : 2 ≤ c e) :
    e ∈ B ∨ B.card + L.card + 2 ≤ m + 1 := by
  by_cases heB : e ∈ B
  · exact Or.inl heB
  · right
    have hez : e ≠ z := by
      intro hez
      subst e
      omega
    have heL : e ∉ L := by
      intro heL
      have heO := hLO heL
      have hce : c e = -1 :=
        (witnessOmissionCoordinates_exact c e).mpr heO
      omega
    let C := (Finset.univ \ B).erase z
    have heC : e ∈ C := by
      exact Finset.mem_erase.mpr ⟨hez,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, heB⟩⟩
    have hinsert : insert e L ⊆ C := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxL
      · exact heC
      · exact hLC hxL
    have hcardInsert : (insert e L).card = L.card + 1 := by
      rw [Finset.card_insert_of_notMem heL]
    have hleC : L.card + 1 ≤ C.card := by
      rw [← hcardInsert]
      exact Finset.card_le_card hinsert
    have hzCompl : z ∈ Finset.univ \ B := by
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzB⟩
    have hCcard : C.card + 1 = (Finset.univ \ B).card := by
      exact Finset.card_erase_add_one hzCompl
    have hComplCard : (Finset.univ \ B).card = m + 1 - B.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
      simp
    have hBcard : B.card ≤ m + 1 := by
      simpa using Finset.card_le_univ B
    dsimp only [C] at hleC hCcard
    omega

/-- For a fixed self-heavy star, the selected heavy coordinate of the
center-avoiding witness lies in `B` unless the center, leaves, and coordinate
together force the stronger ambient capacity bound. -/
theorem minimalSupportPrivateSelfHeavyStar_heavyCoordinate_mem_transversal_or_capacity
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1)
    (hzB : z ∉ B)
    (k : Fin m)
    (hk : 2 ≤ supportAvoidingWitnessAt g hno z k.succ) :
    k.succ ∈ B ∨
      B.card +
          (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card + 2 ≤
        m + 1 := by
  let L := minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz
  have hlocation :=
    heavyCoordinate_mem_transversal_or_card_add_reservoir_add_two_le
      (supportAvoidingWitnessAt g hno z) B L z k.succ
      (minimalSupportPrivateSelfHeavyStarLeaves_subset_compl_erase
        g h hmin z hz)
      (minimalSupportPrivateSelfHeavyStarLeaves_subset_avoidingOmissions
        g hg h hh hmin hno z hz)
      hzB (supportAvoidingWitnessAt_eq_zero g hno z) hk
  rcases hlocation with hinternal | hcapacity
  · exact Or.inl hinternal
  · right
    rw [card_minimalSupportPrivateSelfHeavyStarLeaves
      g hg h hh hne hunique hmin hno z hz] at hcapacity
    exact hcapacity

/-- Global normalized star endpoint.  Outside the small and stronger-capacity
arms, the light branch supplies exponential canonical upper-face mass, while
the heavy branch supplies an explicit heavy coordinate lying in `B` together
with the full fixed external leaf reservoir. -/
theorem card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_canonicalFace_or_strongCapacity_or_internalHeavy
    [DecidableEq G]
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) :
    (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤ 3 ∨
      (∃ z : Fin (m + 1), z ∉ B ∧
        supportAvoidingWitnessAt g hno z z = 0 ∧
        ∃ r : ReducedSubsetSumCollision g h,
          r ∈ canonicalReducedCollisions (g := g) hh ∧
          (minimalSupportPrivateSelfHeavyExactTwoVertices
            g h hmin).card ≤ r.val.2.card + 1 ∧
          2 ^ ((minimalSupportPrivateSelfHeavyExactTwoVertices
                g h hmin).card - 1) *
              reducedCollisionWeight (m := m) r ≤
            (blockedSignatureUpperValueLayer g r.val.1).card ∧
          (subsetCollisionCoeffs r.val.1 r.val.2 =
              supportAvoidingWitnessAt g hno z ∨
            subsetCollisionCoeffs r.val.1 r.val.2 =
              -supportAvoidingWitnessAt g hno z)) ∨
      B.card +
          (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card + 2 ≤
        m + 1 ∨
      ∃ z : Fin (m + 1),
      ∃ hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
        minimalSupportPrivateWitness g h hmin b.val z = -1,
      ∃ k : Fin m,
        z ∉ B ∧ supportAvoidingWitnessAt g hno z z = 0 ∧
        (minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz).card =
          (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ∧
        minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz ⊆
          (Finset.univ \ B).erase z ∧
        minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz ⊆
          witnessOmissionCoordinates (supportAvoidingWitnessAt g hno z) ∧
        k.succ ∈ B ∧ 2 ≤ supportAvoidingWitnessAt g hno z k.succ := by
  rcases
      card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_fixedStarReservoir
        g hg h hh hne hunique hmin hno with
    hsmall | ⟨z, hz, hzB, hz0, hLcard, hLC, hLO, _hcapacity, hlight | hheavy⟩
  · exact Or.inl hsmall
  · exact Or.inr (Or.inl ⟨z, hzB, hz0, hlight⟩)
  · obtain ⟨k, hk⟩ := hheavy
    rcases
        minimalSupportPrivateSelfHeavyStar_heavyCoordinate_mem_transversal_or_capacity
          g hg h hh hne hunique hmin hno z hz hzB k hk with
      hkB | hcapacity
    · exact Or.inr (Or.inr (Or.inr
        ⟨z, hz, k, hzB, hz0, hLcard, hLC, hLO, hkB, hk⟩))
    · exact Or.inr (Or.inr (Or.inl hcapacity))

end MinModulus
