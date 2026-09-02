/-
# Iterating higher-omission fibers to two fixed omissions

After fixing one omission `z` in the at-least-three self-heavy layer, every
remaining owner has at least two further omissions.  Counting those residual
incidences gives either another unit of ambient complement capacity or a
large owner fiber sharing two distinct external omissions.
-/
import MinModulus.G1PrivateHeavySelfHeavyHigherOmissionFibers

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Residual owner/omission incidences in `H3(z)`, with the already fixed
coordinate `z` erased. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1)) :
    Finset (Σ _b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
        g h hmin z), Fin (m + 1)) := by
  classical
  exact Finset.univ.sigma (fun b ↦
    (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val.val.val)).erase z)

@[simp] theorem mem_minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (p : Σ _b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
        g h hmin z), Fin (m + 1)) :
    p ∈ minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences
        g h hmin z ↔
      p.2 ∈ (witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin p.1.val.val.val)).erase z := by
  classical
  simp [minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences]

/-- Exact owner-fiber sum for the residual incidences after fixing `z`. -/
theorem card_minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences
        g h hmin z).card =
      ∑ b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
          g h hmin z),
        ((witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val.val.val)).erase z).card := by
  classical
  exact Finset.card_sigma _ _

/-- Every owner in `H3(z)` retains at least two omissions after erasing `z`. -/
theorem two_mul_card_minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber_le_residualIncidences
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1)) :
    2 * (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
        g h hmin z).card ≤
      (minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences
        g h hmin z).card := by
  classical
  rw [card_minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences]
  calc
    2 * (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
          g h hmin z).card =
        ∑ _b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
          g h hmin z), 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
          g h hmin z),
        ((witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val.val.val)).erase z).card := by
      apply Finset.sum_le_sum
      intro b _hb
      have hbFiber := Finset.mem_filter.mp b.property
      have hzO := hbFiber.2
      have hbThree :=
        (mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
          g h hmin b.val.val).mp b.val.property |>.2
      rw [Finset.card_erase_of_mem hzO]
      omega

/-- The residual omission coordinate attached to an incidence. -/
def minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabel
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (p : Σ _b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
        g h hmin z), Fin (m + 1)) : Fin (m + 1) :=
  p.2

/-- Residual omission labels used by `H3(z)`. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabels
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1)) : Finset (Fin (m + 1)) := by
  classical
  exact (minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences
    g h hmin z).image
      (minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabel
        g h hmin z)

/-- Residual incidences with a fixed second omission `w`. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidenceFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w : Fin (m + 1)) :=
  (minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences
    g h hmin z).filter (fun p ↦
      minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabel
        g h hmin z p = w)

/-- Owners in `H3(z)` whose private witness also omits `w`. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w : Fin (m + 1)) :
    Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
      g h hmin z) := by
  classical
  exact Finset.univ.filter (fun b ↦
    w ≠ z ∧ w ∈ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val.val.val))

/-- A residual label is an omission outside `B` and is different from the
already fixed omission `z`. -/
theorem minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabel_spec
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (p : Σ _b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
        g h hmin z), Fin (m + 1))
    (hp : p ∈
      minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences
        g h hmin z) :
    minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabel
        g h hmin z p ∉ B ∧
      minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabel
        g h hmin z p ≠ z := by
  have hpErase :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences_iff
      g h hmin z p).mp hp
  have hpO := (Finset.mem_erase.mp hpErase).2
  have hpNe := (Finset.mem_erase.mp hpErase).1
  have hbSelf :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
      g h hmin p.1.val.val).mp p.1.val.property |>.1
  have hsubset := minimalSupportPrivateSelfHeavy_omissions_subset_compl
    g h hmin hbSelf
  exact ⟨(Finset.mem_sdiff.mp (hsubset hpO)).2, hpNe⟩

/-- All residual labels are external to `B`. -/
theorem minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabels_disjoint
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1)) :
    Disjoint (minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabels
      g h hmin z) B := by
  classical
  rw [Finset.disjoint_left]
  intro w hw hwB
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
  exact
    (minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabel_spec
      g h hmin z p hp).1 hwB

/-- The fixed first omission is absent from the residual label set. -/
theorem minimalSupportPrivateSelfHeavyAtLeastThree_fixed_not_mem_residualOmissionLabels
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1)) :
    z ∉ minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabels
      g h hmin z := by
  classical
  intro hz
  obtain ⟨p, hp, hpz⟩ := Finset.mem_image.mp hz
  exact
    (minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabel_spec
      g h hmin z p hp).2 hpz

/-- At fixed `(z,w)`, residual incidences are in bijection with the distinct
owners sharing both omissions. -/
theorem card_minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidenceFiber_eq
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidenceFiber
        g h hmin z w).card =
      (minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionFiber
        g h hmin z w).card := by
  classical
  apply Finset.card_bij (fun p _hp ↦ p.1)
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpErase :=
      (mem_minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences_iff
        g h hmin z p).mp hp'.1
    have hpO := (Finset.mem_erase.mp hpErase).2
    rw [show p.2 = w by exact hp'.2] at hpO
    have hpNe := (Finset.mem_erase.mp hpErase).1
    rw [show p.2 = w by exact hp'.2] at hpNe
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpNe, hpO⟩
  · intro p hp q hq hpq
    have hpw := (Finset.mem_filter.mp hp).2
    have hqw := (Finset.mem_filter.mp hq).2
    apply Sigma.ext hpq
    exact heq_of_eq (hpw.trans hqw.symm)
  · intro b hb
    have hb' := Finset.mem_filter.mp hb
    let p : Σ _b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
        g h hmin z), Fin (m + 1) := ⟨b, w⟩
    refine ⟨p, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply
        (mem_minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences_iff
          g h hmin z p).mpr
      apply Finset.mem_erase.mpr
      exact ⟨hb'.2.1, hb'.2.2⟩
    · rfl

/-- Exact label/fiber dichotomy after one omission has already been fixed. -/
theorem minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmission_labelImage_or_largeFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1)) (L r : ℕ)
    (hcount : L * r <
      (minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences
        g h hmin z).card) :
    L ≤ (minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabels
        g h hmin z).card ∨
      ∃ w ∈ minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabels
          g h hmin z,
        r < (minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionFiber
          g h hmin z w).card := by
  classical
  let I := minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences
    g h hmin z
  let label := minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabel
    g h hmin z
  let labels := minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabels
    g h hmin z
  by_cases hlarge : L ≤ labels.card
  · exact Or.inl hlarge
  · right
    have hlabelLe : labels.card ≤ L :=
      Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
    have hmul : labels.card * r < I.card :=
      lt_of_le_of_lt (Nat.mul_le_mul_right r hlabelLe) hcount
    have hmaps : ∀ p ∈ I, label p ∈ labels := by
      intro p hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    obtain ⟨w, hw, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (f := label) hmaps hmul
    refine ⟨w, hw, ?_⟩
    rw [← card_minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidenceFiber_eq
      g h hmin z w]
    simpa [label, I,
      minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidenceFiber] using
        hfiber

/-- A large one-omission higher-owner fiber either consumes further ambient
coordinates or contains a large fiber sharing a second distinct external
omission. -/
theorem minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmission_capacity_or_largeFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1)) (hzB : z ∉ B) (L r : ℕ)
    (hcount : L * r < 2 *
      (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
        g h hmin z).card) :
    B.card + 1 + L ≤ m + 1 ∨
      ∃ w : Fin (m + 1), w ∉ B ∧ w ≠ z ∧
        r < (minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionFiber
          g h hmin z w).card := by
  have hinc :=
    two_mul_card_minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber_le_residualIncidences
      g h hmin z
  have hcount' : L * r <
      (minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences
        g h hmin z).card := lt_of_lt_of_le hcount hinc
  rcases
      minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmission_labelImage_or_largeFiber
        g h hmin z L r hcount' with hlabels | hfiber
  · left
    let labels :=
      minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabels
        g h hmin z
    have hzLabels : z ∉ labels :=
      minimalSupportPrivateSelfHeavyAtLeastThree_fixed_not_mem_residualOmissionLabels
        g h hmin z
    have hdisj : Disjoint (insert z labels) B := by
      rw [Finset.disjoint_left]
      intro i hi hiB
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hzB hiB
      · exact Finset.disjoint_left.mp
          (minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabels_disjoint
            g h hmin z) hi hiB
    have hcap : B.card + (insert z labels).card ≤ m + 1 := by
      rw [← Finset.card_union_of_disjoint hdisj.symm]
      simpa using Finset.card_le_univ (B ∪ insert z labels)
    rw [Finset.card_insert_of_notMem hzLabels] at hcap
    change L ≤ labels.card at hlabels
    omega
  · right
    obtain ⟨w, hwLabel, hwFiber⟩ := hfiber
    have hwSpec : w ∉ B ∧ w ≠ z := by
      obtain ⟨p, hp, hpw⟩ := Finset.mem_image.mp hwLabel
      have hpSpec :=
        minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabel_spec
          g h hmin z p hp
      rw [hpw] at hpSpec
      exact hpSpec
    exact ⟨w, hwSpec.1, hwSpec.2, hwFiber⟩

/-- Two-stage global omission-fiber frontier for an arbitrary lower bound on
the full self-heavy family. -/
theorem minimalSupportPrivateSelfHeavy_exactTwo_or_higherOmission_capacity_or_doubleFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (K L r L' r' : ℕ)
    (hself : K ≤
      (minimalSupportPrivateSelfHeavyVertices g h hmin).card)
    (hfirst : 2 * (L * r) < 3 * K)
    (hsecond : L' * r' < 2 * (r + 1)) :
    K ≤ 2 *
        (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ∨
      B.card + L ≤ m + 1 ∨
      B.card + 1 + L' ≤ m + 1 ∨
      ∃ z w : Fin (m + 1), z ∉ B ∧ w ∉ B ∧ w ≠ z ∧
        r' < (minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionFiber
          g h hmin z w).card := by
  rcases
      minimalSupportPrivateSelfHeavy_exactTwo_or_higherOmission_capacity_or_largeFiber
        g h hmin K L r hself hfirst with htwo | hcapacity | ⟨z, hzB, hzFiber⟩
  · exact Or.inl htwo
  · exact Or.inr (Or.inl hcapacity)
  · have hfiberCard : r + 1 ≤
        (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
          g h hmin z).card := by omega
    have hinner : L' * r' < 2 *
        (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
          g h hmin z).card := by omega
    rcases
        minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmission_capacity_or_largeFiber
          g h hmin z hzB L' r' hinner with hcapacity | hdouble
    · exact Or.inr (Or.inr (Or.inl hcapacity))
    · obtain ⟨w, hwB, hwz, hwFiber⟩ := hdouble
      exact Or.inr (Or.inr (Or.inr ⟨z, w, hzB, hwB, hwz, hwFiber⟩))

end MinModulus
