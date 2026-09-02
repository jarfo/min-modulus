/-
# Instantiating omission extension at two fixed coordinates

Flatten the doubly fixed higher-omission fiber into a subfamily of `H3`, then
apply the generic extension theorem with `R = {z,w}`.  Since `|R| = 2`, every
owner contributes at least one residual omission.  The result is a third
ambient-capacity alternative or a large family sharing three distinct
external omissions.
-/
import MinModulus.G1PrivateHeavySelfHeavyOmissionExtension

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The doubly fixed owner family as a direct subfamily of `H3`, rather than
as a nested subtype of `H3(z)`. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w : Fin (m + 1)) :
    Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin) := by
  classical
  exact (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
    g h hmin z).filter (fun b ↦
      w ≠ z ∧ w ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val.val))

@[simp] theorem mem_minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w : Fin (m + 1))
    (b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin)) :
    b ∈ minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
        g h hmin z w ↔
      z ∈ witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val.val) ∧
        w ≠ z ∧ w ∈ witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val.val) := by
  classical
  simp [minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners,
    minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber]

/-- Flattening the nested double fiber loses no owners. -/
theorem card_minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners_eq
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionFiber
        g h hmin z w).card =
      (minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
        g h hmin z w).card := by
  classical
  apply Finset.card_bij (fun b _hb ↦ b.val)
  · intro b hb
    have hb' := Finset.mem_filter.mp hb
    apply
      (mem_minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners_iff
        g h hmin z w b.val).mpr
    exact ⟨(Finset.mem_filter.mp b.property).2, hb'.2.1, hb'.2.2⟩
  · intro b hb c hc hbc
    exact Subtype.ext hbc
  · intro b hb
    have hb' :=
      (mem_minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners_iff
        g h hmin z w b).mp hb
    let b' : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
        g h hmin z) :=
      ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'.1⟩⟩
    refine ⟨b', ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'.2.1, hb'.2.2⟩

/-- Owners in the doubly fixed family omit the pair `{z,w}`. -/
theorem pair_subset_omissions_of_mem_minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w : Fin (m + 1))
    {b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
      g h hmin z w) :
    ({z, w} : Finset (Fin (m + 1))) ⊆
      witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val.val) := by
  have hb' :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners_iff
      g h hmin z w b).mp hb
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact hb'.1
  · exact hb'.2.2

/-- The pair of distinct external omissions is disjoint from the minimal
transversal and has cardinality two. -/
theorem doubleOmissionPair_disjoint_and_card
    {B : Finset (Fin (m + 1))} {z w : Fin (m + 1)}
    (hzB : z ∉ B) (hwB : w ∉ B) (hwz : w ≠ z) :
    Disjoint ({z, w} : Finset (Fin (m + 1))) B ∧
      ({z, w} : Finset (Fin (m + 1))).card = 2 := by
  constructor
  · rw [Finset.disjoint_left]
    intro i hi hiB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hzB hiB
    · exact hwB hiB
  · have hzw : z ≠ w := Ne.symm hwz
    simp [hzw]

/-- Triple-fixed higher-owner fiber returned by extending the fixed pair
`{z,w}` with a fresh omission `u`. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :=
  minimalSupportPrivateSelfHeavyOmissionExtensionFiber
    g h hmin
      (minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
        g h hmin z w)
      ({z, w} : Finset (Fin (m + 1))) u

/-- Membership in the triple fiber displays three distinct omitted external
coordinates at the level of one owner. -/
theorem minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber_spec
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1))
    {b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
      g h hmin z w)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber
      g h hmin z w u) :
    u ≠ z ∧ u ≠ w ∧
      z ∈ witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val.val.val) ∧
      w ∈ witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val.val.val) ∧
      u ∈ witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val.val.val) := by
  have hb' := Finset.mem_filter.mp hb
  have huPair : u ∉ ({z, w} : Finset (Fin (m + 1))) := hb'.2.1
  have hbDouble :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners_iff
      g h hmin z w b.val).mp b.property
  have huNe : u ≠ z ∧ u ≠ w := by simpa using huPair
  exact ⟨huNe.1, huNe.2,
    hbDouble.1, hbDouble.2.2, hb'.2.2⟩

/-- Instantiation of the generic extension theorem at the fixed pair
`R={z,w}`. -/
theorem minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmission_capacity_or_tripleFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w : Fin (m + 1)) (hzB : z ∉ B) (hwB : w ∉ B) (hwz : w ≠ z)
    (L r : ℕ)
    (hcount : L * r <
      (minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
        g h hmin z w).card) :
    B.card + 2 + L ≤ m + 1 ∨
      ∃ u : Fin (m + 1), u ∉ B ∧ u ≠ z ∧ u ≠ w ∧
        r < (minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber
          g h hmin z w u).card := by
  let S := minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
    g h hmin z w
  let R : Finset (Fin (m + 1)) := {z, w}
  have hpair := doubleOmissionPair_disjoint_and_card hzB hwB hwz
  have hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val.val) := by
    intro b hb
    exact pair_subset_omissions_of_mem_minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
      g h hmin z w hb
  have hcount' : L * r < (3 - R.card) * S.card := by
    rw [hpair.2]
    simpa [S] using hcount
  rcases
      minimalSupportPrivateSelfHeavyOmissionExtension_capacity_or_largeFiber
        g h hmin S R hfixed hpair.1 L r hcount' with
    hcapacity | ⟨u, huB, huR, huFiber⟩
  · left
    rw [hpair.2] at hcapacity
    exact hcapacity
  · right
    have huz : u ≠ z := by
      intro huz
      subst u
      exact huR (by simp [R])
    have huw : u ≠ w := by
      intro huw
      subst u
      exact huR (by simp [R])
    exact ⟨u, huB, huz, huw, by simpa [S, R,
      minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber] using
        huFiber⟩

/-- Three-stage global omission frontier.  A lower bound on the full
self-heavy family yields a large exact-two layer, one of three accumulated
capacity bounds, or a large family sharing three distinct external
omissions. -/
theorem minimalSupportPrivateSelfHeavy_exactTwo_or_higherOmission_capacity_or_tripleFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (K L r L' r' L'' r'' : ℕ)
    (hself : K ≤
      (minimalSupportPrivateSelfHeavyVertices g h hmin).card)
    (hfirst : 2 * (L * r) < 3 * K)
    (hsecond : L' * r' < 2 * (r + 1))
    (hthird : L'' * r'' < r' + 1) :
    K ≤ 2 *
        (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ∨
      B.card + L ≤ m + 1 ∨
      B.card + 1 + L' ≤ m + 1 ∨
      B.card + 2 + L'' ≤ m + 1 ∨
      ∃ z w u : Fin (m + 1),
        z ∉ B ∧ w ∉ B ∧ u ∉ B ∧
        w ≠ z ∧ u ≠ z ∧ u ≠ w ∧
        r'' < (minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber
          g h hmin z w u).card := by
  rcases
      minimalSupportPrivateSelfHeavy_exactTwo_or_higherOmission_capacity_or_doubleFiber
        g h hmin K L r L' r' hself hfirst hsecond with
    htwo | hcapacity | hcapacity' | ⟨z, w, hzB, hwB, hwz, hdouble⟩
  · exact Or.inl htwo
  · exact Or.inr (Or.inl hcapacity)
  · exact Or.inr (Or.inr (Or.inl hcapacity'))
  · have hflat : r' <
        (minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
          g h hmin z w).card := by
      rw [← card_minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners_eq]
      exact hdouble
    have hinner : L'' * r'' <
        (minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners
          g h hmin z w).card := by omega
    rcases
        minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmission_capacity_or_tripleFiber
          g h hmin z w hzB hwB hwz L'' r'' hinner with
      hcapacity'' | ⟨u, huB, huz, huw, htriple⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl hcapacity'')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨z, w, u, hzB, hwB, huB, hwz, huz, huw, htriple⟩)))

end MinModulus
