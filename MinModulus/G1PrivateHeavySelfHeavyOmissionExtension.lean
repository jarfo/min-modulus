/-
# A generic fixed-omission extension step

Let `S` be any subfamily of the at-least-three self-heavy owners, and suppose
every witness in `S` omits a fixed coordinate set `R`.  After erasing `R`,
the total residual omission incidence is at least
`(3 - |R|) * |S|`.  All residual labels are external to the minimal
transversal and fresh relative to `R`.

This packages the preceding one- and two-label counts as one reusable
extension step: either the labels consume ambient complement capacity or a
large subfamily shares one additional omission.
-/
import MinModulus.G1PrivateHeavySelfHeavyHigherDoubleOmissionFibers

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Residual omission incidences for an arbitrary higher-owner subfamily `S`
after erasing a fixed omission set `R`. -/
noncomputable def minimalSupportPrivateSelfHeavyOmissionExtensionIncidences
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
      g h hmin))
    (R : Finset (Fin (m + 1))) :
    Finset (Σ _b : ↥S, Fin (m + 1)) := by
  classical
  exact Finset.univ.sigma (fun b ↦
    witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val.val.val) \ R)

@[simp] theorem mem_minimalSupportPrivateSelfHeavyOmissionExtensionIncidences_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
      g h hmin))
    (R : Finset (Fin (m + 1)))
    (p : Σ _b : ↥S, Fin (m + 1)) :
    p ∈ minimalSupportPrivateSelfHeavyOmissionExtensionIncidences
        g h hmin S R ↔
      p.2 ∈ witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin p.1.val.val.val) \ R := by
  classical
  simp [minimalSupportPrivateSelfHeavyOmissionExtensionIncidences]

/-- Exact owner-fiber sum for the generic residual incidence family. -/
theorem card_minimalSupportPrivateSelfHeavyOmissionExtensionIncidences
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
      g h hmin))
    (R : Finset (Fin (m + 1))) :
    (minimalSupportPrivateSelfHeavyOmissionExtensionIncidences
        g h hmin S R).card =
      ∑ b : ↥S,
        (witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val.val.val) \ R).card := by
  classical
  exact Finset.card_sigma _ _

/-- If every owner in `S` omits `R`, then at least `3-|R|` residual
incidences remain per owner. -/
theorem card_sub_mul_card_le_minimalSupportPrivateSelfHeavyOmissionExtensionIncidences
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
      g h hmin))
    (R : Finset (Fin (m + 1)))
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val.val)) :
    (3 - R.card) * S.card ≤
      (minimalSupportPrivateSelfHeavyOmissionExtensionIncidences
        g h hmin S R).card := by
  classical
  rw [card_minimalSupportPrivateSelfHeavyOmissionExtensionIncidences]
  calc
    (3 - R.card) * S.card = ∑ _b : ↥S, (3 - R.card) := by
      simp [Nat.mul_comm]
    _ ≤ ∑ b : ↥S,
        (witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val.val.val) \ R).card := by
      apply Finset.sum_le_sum
      intro b _hb
      have hbThree :=
        (mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
          g h hmin b.val.val).mp b.val.property |>.2
      have hRsubset := hfixed b.val b.property
      rw [Finset.card_sdiff_of_subset hRsubset]
      exact Nat.sub_le_sub_right hbThree R.card

/-- Coordinate label of a generic residual omission incidence. -/
def minimalSupportPrivateSelfHeavyOmissionExtensionLabel
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
      g h hmin))
    (_R : Finset (Fin (m + 1)))
    (p : Σ _b : ↥S, Fin (m + 1)) : Fin (m + 1) :=
  p.2

/-- Residual omission labels used by `S` after the fixed set `R` is erased. -/
noncomputable def minimalSupportPrivateSelfHeavyOmissionExtensionLabels
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
      g h hmin))
    (R : Finset (Fin (m + 1))) : Finset (Fin (m + 1)) := by
  classical
  exact (minimalSupportPrivateSelfHeavyOmissionExtensionIncidences
    g h hmin S R).image
      (minimalSupportPrivateSelfHeavyOmissionExtensionLabel
        g h hmin S R)

/-- Generic residual incidence fiber over one new omission label. -/
noncomputable def minimalSupportPrivateSelfHeavyOmissionExtensionIncidenceFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
      g h hmin))
    (R : Finset (Fin (m + 1))) (z : Fin (m + 1)) :=
  (minimalSupportPrivateSelfHeavyOmissionExtensionIncidences
    g h hmin S R).filter (fun p ↦
      minimalSupportPrivateSelfHeavyOmissionExtensionLabel
        g h hmin S R p = z)

/-- Subfamily of `S` whose witnesses also omit a new coordinate `z`. -/
noncomputable def minimalSupportPrivateSelfHeavyOmissionExtensionFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
      g h hmin))
    (R : Finset (Fin (m + 1))) (z : Fin (m + 1)) : Finset ↥S := by
  classical
  exact Finset.univ.filter (fun b ↦
    z ∉ R ∧ z ∈ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val.val.val))

/-- Every extension label is external to `B` and fresh relative to `R`. -/
theorem minimalSupportPrivateSelfHeavyOmissionExtensionLabel_spec
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
      g h hmin))
    (R : Finset (Fin (m + 1)))
    (p : Σ _b : ↥S, Fin (m + 1))
    (hp : p ∈ minimalSupportPrivateSelfHeavyOmissionExtensionIncidences
      g h hmin S R) :
    minimalSupportPrivateSelfHeavyOmissionExtensionLabel
        g h hmin S R p ∉ B ∧
      minimalSupportPrivateSelfHeavyOmissionExtensionLabel
        g h hmin S R p ∉ R := by
  have hpDiff :=
    (mem_minimalSupportPrivateSelfHeavyOmissionExtensionIncidences_iff
      g h hmin S R p).mp hp
  have hpO := (Finset.mem_sdiff.mp hpDiff).1
  have hpR := (Finset.mem_sdiff.mp hpDiff).2
  have hbSelf :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
      g h hmin p.1.val.val).mp p.1.val.property |>.1
  have hsubset := minimalSupportPrivateSelfHeavy_omissions_subset_compl
    g h hmin hbSelf
  exact ⟨(Finset.mem_sdiff.mp (hsubset hpO)).2, hpR⟩

/-- Generic extension labels are disjoint from `B`. -/
theorem minimalSupportPrivateSelfHeavyOmissionExtensionLabels_disjoint_left
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
      g h hmin))
    (R : Finset (Fin (m + 1))) :
    Disjoint (minimalSupportPrivateSelfHeavyOmissionExtensionLabels
      g h hmin S R) B := by
  classical
  rw [Finset.disjoint_left]
  intro z hz hzB
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  exact (minimalSupportPrivateSelfHeavyOmissionExtensionLabel_spec
    g h hmin S R p hp).1 hzB

/-- Generic extension labels are disjoint from the fixed set `R`. -/
theorem minimalSupportPrivateSelfHeavyOmissionExtensionLabels_disjoint_fixed
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
      g h hmin))
    (R : Finset (Fin (m + 1))) :
    Disjoint (minimalSupportPrivateSelfHeavyOmissionExtensionLabels
      g h hmin S R) R := by
  classical
  rw [Finset.disjoint_left]
  intro z hz hzR
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  exact (minimalSupportPrivateSelfHeavyOmissionExtensionLabel_spec
    g h hmin S R p hp).2 hzR

/-- At a fixed new coordinate, residual incidences are in bijection with the
distinct owners in the extension fiber. -/
theorem card_minimalSupportPrivateSelfHeavyOmissionExtensionIncidenceFiber_eq
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
      g h hmin))
    (R : Finset (Fin (m + 1))) (z : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyOmissionExtensionIncidenceFiber
        g h hmin S R z).card =
      (minimalSupportPrivateSelfHeavyOmissionExtensionFiber
        g h hmin S R z).card := by
  classical
  apply Finset.card_bij (fun p _hp ↦ p.1)
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpDiff :=
      (mem_minimalSupportPrivateSelfHeavyOmissionExtensionIncidences_iff
        g h hmin S R p).mp hp'.1
    have hpSpec := Finset.mem_sdiff.mp hpDiff
    rw [show p.2 = z by exact hp'.2] at hpSpec
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpSpec.2, hpSpec.1⟩
  · intro p hp q hq hpq
    have hpz := (Finset.mem_filter.mp hp).2
    have hqz := (Finset.mem_filter.mp hq).2
    apply Sigma.ext hpq
    exact heq_of_eq (hpz.trans hqz.symm)
  · intro b hb
    have hb' := Finset.mem_filter.mp hb
    let p : Σ _b : ↥S, Fin (m + 1) := ⟨b, z⟩
    refine ⟨p, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply
        (mem_minimalSupportPrivateSelfHeavyOmissionExtensionIncidences_iff
          g h hmin S R p).mpr
      exact Finset.mem_sdiff.mpr ⟨hb'.2.2, hb'.2.1⟩
    · rfl

/-- Exact image/fiber dichotomy for the generic extension step. -/
theorem minimalSupportPrivateSelfHeavyOmissionExtension_labelImage_or_largeFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
      g h hmin))
    (R : Finset (Fin (m + 1))) (L r : ℕ)
    (hcount : L * r <
      (minimalSupportPrivateSelfHeavyOmissionExtensionIncidences
        g h hmin S R).card) :
    L ≤ (minimalSupportPrivateSelfHeavyOmissionExtensionLabels
        g h hmin S R).card ∨
      ∃ z ∈ minimalSupportPrivateSelfHeavyOmissionExtensionLabels
          g h hmin S R,
        r < (minimalSupportPrivateSelfHeavyOmissionExtensionFiber
          g h hmin S R z).card := by
  classical
  let I := minimalSupportPrivateSelfHeavyOmissionExtensionIncidences
    g h hmin S R
  let label := minimalSupportPrivateSelfHeavyOmissionExtensionLabel
    g h hmin S R
  let labels := minimalSupportPrivateSelfHeavyOmissionExtensionLabels
    g h hmin S R
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
    obtain ⟨z, hz, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (f := label) hmaps hmul
    refine ⟨z, hz, ?_⟩
    rw [← card_minimalSupportPrivateSelfHeavyOmissionExtensionIncidenceFiber_eq
      g h hmin S R z]
    simpa [label, I,
      minimalSupportPrivateSelfHeavyOmissionExtensionIncidenceFiber] using
        hfiber

/-- Generic fixed-omission extension theorem: residual density yields ambient
capacity or a large subfamily sharing one fresh external omission. -/
theorem minimalSupportPrivateSelfHeavyOmissionExtension_capacity_or_largeFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
      g h hmin))
    (R : Finset (Fin (m + 1)))
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val.val))
    (hRB : Disjoint R B) (L r : ℕ)
    (hcount : L * r < (3 - R.card) * S.card) :
    B.card + R.card + L ≤ m + 1 ∨
      ∃ z : Fin (m + 1), z ∉ B ∧ z ∉ R ∧
        r < (minimalSupportPrivateSelfHeavyOmissionExtensionFiber
          g h hmin S R z).card := by
  have hinc :=
    card_sub_mul_card_le_minimalSupportPrivateSelfHeavyOmissionExtensionIncidences
      g h hmin S R hfixed
  have hcount' : L * r <
      (minimalSupportPrivateSelfHeavyOmissionExtensionIncidences
        g h hmin S R).card := lt_of_lt_of_le hcount hinc
  rcases
      minimalSupportPrivateSelfHeavyOmissionExtension_labelImage_or_largeFiber
        g h hmin S R L r hcount' with hlabels | hfiber
  · left
    let labels := minimalSupportPrivateSelfHeavyOmissionExtensionLabels
      g h hmin S R
    have hBL : Disjoint labels B :=
      minimalSupportPrivateSelfHeavyOmissionExtensionLabels_disjoint_left
        g h hmin S R
    have hRL : Disjoint labels R :=
      minimalSupportPrivateSelfHeavyOmissionExtensionLabels_disjoint_fixed
        g h hmin S R
    have hBRL : Disjoint (B ∪ R) labels := by
      rw [Finset.disjoint_left]
      intro z hzBR hzLabels
      rcases Finset.mem_union.mp hzBR with hzB | hzR
      · exact Finset.disjoint_left.mp hBL hzLabels hzB
      · exact Finset.disjoint_left.mp hRL hzLabels hzR
    have hcap : (B ∪ R).card + labels.card ≤ m + 1 := by
      rw [← Finset.card_union_of_disjoint hBRL]
      simpa using Finset.card_le_univ ((B ∪ R) ∪ labels)
    rw [Finset.card_union_of_disjoint hRB.symm] at hcap
    change L ≤ labels.card at hlabels
    omega
  · right
    obtain ⟨z, hzLabel, hzFiber⟩ := hfiber
    obtain ⟨p, hp, hpz⟩ := Finset.mem_image.mp hzLabel
    have hzSpec := minimalSupportPrivateSelfHeavyOmissionExtensionLabel_spec
      g h hmin S R p hp
    rw [hpz] at hzSpec
    exact ⟨z, hzSpec.1, hzSpec.2, hzFiber⟩

end MinModulus
