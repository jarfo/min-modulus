/-
# Fixed-omission extension at an arbitrary omission degree

The earlier extension API was tied to the at-least-three owner subtype.  This
module extracts its actual invariant.  For any subfamily of private tail-heavy
owners whose witnesses are self-heavy and have at least `q` omissions, erasing
a fixed omitted set `R` leaves at least `(q-|R|)` incidences per owner.  Exact
image/fiber counting yields ambient capacity or a large fiber sharing one new
external omission.

The generic theorem is then instantiated on the triple-fixed at-least-four
layer.  This restarts omission growth after the exact-three layer has been
bounded by cyclic scalar fibers.
-/
import MinModulus.G1PrivateHeavySelfHeavyExactThreeCyclicBounds

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Residual omission incidences for a private self-heavy owner family with
an arbitrary supplied omission-degree lower bound. -/
noncomputable def minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) :
    Finset (Σ _b : ↥S, Fin (m + 1)) := by
  classical
  exact Finset.univ.sigma (fun b ↦
    witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val.val) \ R)

@[simp] theorem mem_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1)))
    (p : Σ _b : ↥S, Fin (m + 1)) :
    p ∈ minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
        g h hmin S R ↔
      p.2 ∈ witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin p.1.val.val) \ R := by
  classical
  simp [minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences]

/-- Exact owner-fiber sum for arbitrary-degree residual incidences. -/
theorem card_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) :
    (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
        g h hmin S R).card =
      ∑ b : ↥S,
        (witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val.val) \ R).card := by
  classical
  exact Finset.card_sigma _ _

/-- If every owner has at least `q` omissions and contains the fixed omitted
set `R`, at least `q-|R|` residual incidences remain per owner. -/
theorem card_sub_mul_card_le_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (q : ℕ)
    (hdegree : ∀ b ∈ S, q ≤ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card)
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)) :
    (q - R.card) * S.card ≤
      (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
        g h hmin S R).card := by
  classical
  rw [card_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences]
  calc
    (q - R.card) * S.card = ∑ _b : ↥S, (q - R.card) := by
      simp [Nat.mul_comm]
    _ ≤ ∑ b : ↥S,
        (witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val.val) \ R).card := by
      apply Finset.sum_le_sum
      intro b _hb
      have hbDegree := hdegree b.val b.property
      have hRsubset := hfixed b.val b.property
      rw [Finset.card_sdiff_of_subset hRsubset]
      exact Nat.sub_le_sub_right hbDegree R.card

/-- Coordinate label of an arbitrary-degree residual omission incidence. -/
def minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabel
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (_R : Finset (Fin (m + 1)))
    (p : Σ _b : ↥S, Fin (m + 1)) : Fin (m + 1) :=
  p.2

/-- Residual omission labels after the fixed set `R` is erased. -/
noncomputable def minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabels
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) : Finset (Fin (m + 1)) := by
  classical
  exact (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
    g h hmin S R).image
      (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabel
        g h hmin S R)

/-- Residual incidence fiber over one new label. -/
noncomputable def minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidenceFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (z : Fin (m + 1)) :=
  (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
    g h hmin S R).filter (fun p ↦
      minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabel
        g h hmin S R p = z)

/-- Subfamily of `S` sharing one fresh omission `z`. -/
noncomputable def minimalSupportPrivateSelfHeavyOmissionDegreeExtensionFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (z : Fin (m + 1)) : Finset ↥S := by
  classical
  exact Finset.univ.filter (fun b ↦
    z ∉ R ∧ z ∈ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val.val))

/-- Every arbitrary-degree extension label is external to `B` and fresh
relative to `R`. -/
theorem minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabel_spec
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1)))
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (p : Σ _b : ↥S, Fin (m + 1))
    (hp : p ∈
      minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
        g h hmin S R) :
    minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabel
        g h hmin S R p ∉ B ∧
      minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabel
        g h hmin S R p ∉ R := by
  have hpDiff :=
    (mem_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences_iff
      g h hmin S R p).mp hp
  have hpO := (Finset.mem_sdiff.mp hpDiff).1
  have hpR := (Finset.mem_sdiff.mp hpDiff).2
  have hbSelf := hself p.1.val p.1.property
  have hsubset := minimalSupportPrivateSelfHeavy_omissions_subset_compl
    g h hmin hbSelf
  exact ⟨(Finset.mem_sdiff.mp (hsubset hpO)).2, hpR⟩

/-- Arbitrary-degree residual labels are disjoint from `B`. -/
theorem minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabels_disjoint_left
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1)))
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin) :
    Disjoint (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabels
      g h hmin S R) B := by
  classical
  rw [Finset.disjoint_left]
  intro z hz hzB
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  exact (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabel_spec
    g h hmin S R hself p hp).1 hzB

/-- Arbitrary-degree residual labels are disjoint from `R`. -/
theorem minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabels_disjoint_fixed
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) :
    Disjoint (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabels
      g h hmin S R) R := by
  classical
  rw [Finset.disjoint_left]
  intro z hz hzR
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  have hpDiff :=
    (mem_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences_iff
      g h hmin S R p).mp hp
  exact (Finset.mem_sdiff.mp hpDiff).2 hzR

/-- At a fixed new label, residual incidences are in bijection with distinct
members of the extended family. -/
theorem card_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidenceFiber_eq
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (z : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidenceFiber
        g h hmin S R z).card =
      (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionFiber
        g h hmin S R z).card := by
  classical
  apply Finset.card_bij (fun p _hp ↦ p.1)
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpDiff :=
      (mem_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences_iff
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
        (mem_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences_iff
          g h hmin S R p).mpr
      exact Finset.mem_sdiff.mpr ⟨hb'.2.2, hb'.2.1⟩
    · rfl

/-- Exact image/fiber dichotomy for the arbitrary-degree extension. -/
theorem minimalSupportPrivateSelfHeavyOmissionDegreeExtension_labelImage_or_largeFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (L r : ℕ)
    (hcount : L * r <
      (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
        g h hmin S R).card) :
    L ≤ (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabels
        g h hmin S R).card ∨
      ∃ z ∈ minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabels
          g h hmin S R,
        r < (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionFiber
          g h hmin S R z).card := by
  classical
  let I := minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
    g h hmin S R
  let label := minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabel
    g h hmin S R
  let labels := minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabels
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
    rw [← card_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidenceFiber_eq
      g h hmin S R z]
    simpa [label, I,
      minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidenceFiber] using
        hfiber

/-- Arbitrary-degree fixed-omission recurrence: residual density yields
ambient capacity or a large family sharing one fresh external omission. -/
theorem minimalSupportPrivateSelfHeavyOmissionDegreeExtension_capacity_or_largeFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (q : ℕ)
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (hdegree : ∀ b ∈ S, q ≤ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card)
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val))
    (hRB : Disjoint R B) (L r : ℕ)
    (hcount : L * r < (q - R.card) * S.card) :
    B.card + R.card + L ≤ m + 1 ∨
      ∃ z : Fin (m + 1), z ∉ B ∧ z ∉ R ∧
        r < (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionFiber
          g h hmin S R z).card := by
  have hinc :=
    card_sub_mul_card_le_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
      g h hmin S R q hdegree hfixed
  have hcount' : L * r <
      (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences
        g h hmin S R).card := lt_of_lt_of_le hcount hinc
  rcases
      minimalSupportPrivateSelfHeavyOmissionDegreeExtension_labelImage_or_largeFiber
        g h hmin S R L r hcount' with hlabels | hfiber
  · left
    let labels := minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabels
      g h hmin S R
    have hBL : Disjoint labels B :=
      minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabels_disjoint_left
        g h hmin S R hself
    have hRL : Disjoint labels R :=
      minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabels_disjoint_fixed
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
    have hzSpec :=
      minimalSupportPrivateSelfHeavyOmissionDegreeExtensionLabel_spec
        g h hmin S R hself p hp
    rw [hpz] at hzSpec
    exact ⟨z, hzSpec.1, hzSpec.2, hzFiber⟩

/-- The triple-fixed at-least-four layer represented directly as a subfamily
of private tail-heavy owners.  This removes the nested `H3`/double-fiber
subtypes before applying the arbitrary-degree recurrence. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :
    Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) := by
  classical
  exact (minimalSupportPrivateSelfHeavyAtLeastFourVertices g h hmin).filter
    (fun b ↦
      w ≠ z ∧ u ≠ z ∧ u ≠ w ∧
      z ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) ∧
      w ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) ∧
      u ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val))

@[simp] theorem mem_minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1))
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    b ∈ minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners
        g h hmin z w u ↔
      b ∈ minimalSupportPrivateSelfHeavyAtLeastFourVertices g h hmin ∧
      w ≠ z ∧ u ≠ z ∧ u ≠ w ∧
      z ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) ∧
      w ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) ∧
      u ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) := by
  classical
  simp [minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners]

/-- Flattening the nested triple-fixed `H4` fiber into the direct owner family
does not lose members. -/
theorem card_minimalSupportPrivateSelfHeavyTripleAtLeastFourFiber_le_direct
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyTripleAtLeastFourFiber
        g h hmin z w u).card ≤
      (minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners
        g h hmin z w u).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun b ↦ b.val.val)
  · intro b hb
    have hb' := Finset.mem_filter.mp hb
    have htriple :=
      minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber_spec
        g h hmin z w u hb'.1
    have hbDouble :=
      (mem_minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners_iff
        g h hmin z w b.val).mp b.property
    apply
      (mem_minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners_iff
        g h hmin z w u b.val.val).mpr
    have hfour : b.val.val ∈
        minimalSupportPrivateSelfHeavyAtLeastFourVertices g h hmin :=
      (mem_minimalSupportPrivateSelfHeavyAtLeastFourVertices_iff
        g h hmin b.val.val).mpr ⟨b.val.property, hb'.2⟩
    exact ⟨hfour, hbDouble.2.1, htriple.1, htriple.2.1,
      htriple.2.2.1, htriple.2.2.2.1, htriple.2.2.2.2⟩
  · intro b _hb c _hc hbc
    apply Subtype.ext
    apply Subtype.ext
    exact hbc

/-- Three pairwise-distinct external omissions form a three-element set
disjoint from the minimal transversal. -/
theorem tripleOmissionSet_disjoint_and_card
    {B : Finset (Fin (m + 1))} {z w u : Fin (m + 1)}
    (hzB : z ∉ B) (hwB : w ∉ B) (huB : u ∉ B)
    (hwz : w ≠ z) (huz : u ≠ z) (huw : u ≠ w) :
    Disjoint ({z, w, u} : Finset (Fin (m + 1))) B ∧
      ({z, w, u} : Finset (Fin (m + 1))).card = 3 := by
  constructor
  · rw [Finset.disjoint_left]
    intro i hi hiB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact hzB hiB
    · exact hwB hiB
    · exact huB hiB
  · have hzw : z ≠ w := Ne.symm hwz
    have hzu : z ≠ u := Ne.symm huz
    have hwu : w ≠ u := Ne.symm huw
    simp [hzw, hzu, hwu]

/-- The at-least-four owner family sharing `z,w,u`, further restricted to a
fresh fourth omission `v`. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1)) :=
  minimalSupportPrivateSelfHeavyOmissionDegreeExtensionFiber
    g h hmin
      (minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners
        g h hmin z w u)
      ({z, w, u} : Finset (Fin (m + 1))) v

/-- A member of the fourth-omission fiber retains all four distinct omitted
coordinates and the at-least-four degree. -/
theorem minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionFiber_spec
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1))
    {b : ↥(minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners
      g h hmin z w u)}
    (hb : b ∈
      minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionFiber
        g h hmin z w u v) :
    v ≠ z ∧ v ≠ w ∧ v ≠ u ∧
      4 ≤ (witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val.val)).card ∧
      z ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val.val) ∧
      w ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val.val) ∧
      u ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val.val) ∧
      v ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val.val) := by
  have hb' := Finset.mem_filter.mp hb
  have hvFresh : v ∉ ({z, w, u} : Finset (Fin (m + 1))) := hb'.2.1
  have hbDirect :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners_iff
      g h hmin z w u b.val).mp b.property
  have hdegree :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastFourVertices_iff
      g h hmin b.val).mp hbDirect.1 |>.2
  have hvNe : v ≠ z ∧ v ≠ w ∧ v ≠ u := by simpa using hvFresh
  exact ⟨hvNe.1, hvNe.2.1, hvNe.2.2, hdegree,
    hbDirect.2.2.2.2.1, hbDirect.2.2.2.2.2.1,
    hbDirect.2.2.2.2.2.2, hb'.2.2⟩

/-- Baseline-four instantiation at three fixed omissions.  Density yields
one more ambient-capacity bound or a large four-fixed owner family. -/
theorem minimalSupportPrivateSelfHeavyAtLeastFourTripleOmission_capacity_or_quadrupleFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u : Fin (m + 1))
    (hzB : z ∉ B) (hwB : w ∉ B) (huB : u ∉ B)
    (hwz : w ≠ z) (huz : u ≠ z) (huw : u ≠ w)
    (L r : ℕ)
    (hcount : L * r <
      (minimalSupportPrivateSelfHeavyTripleAtLeastFourFiber
        g h hmin z w u).card) :
    B.card + 3 + L ≤ m + 1 ∨
      ∃ v : Fin (m + 1), v ∉ B ∧ v ≠ z ∧ v ≠ w ∧ v ≠ u ∧
        r < (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionFiber
          g h hmin z w u v).card := by
  let S := minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners
    g h hmin z w u
  let R : Finset (Fin (m + 1)) := {z, w, u}
  have hset := tripleOmissionSet_disjoint_and_card
    hzB hwB huB hwz huz huw
  have hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin := by
    intro b hb
    have hbDirect :=
      (mem_minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners_iff
        g h hmin z w u b).mp hb
    have hbH3 :=
      (mem_minimalSupportPrivateSelfHeavyAtLeastFourVertices_iff
        g h hmin b).mp hbDirect.1 |>.1
    exact (mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
      g h hmin b).mp hbH3 |>.1
  have hdegree : ∀ b ∈ S, 4 ≤ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card := by
    intro b hb
    have hbDirect :=
      (mem_minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners_iff
        g h hmin z w u b).mp hb
    exact (mem_minimalSupportPrivateSelfHeavyAtLeastFourVertices_iff
      g h hmin b).mp hbDirect.1 |>.2
  have hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val) := by
    intro b hb i hi
    have hbDirect :=
      (mem_minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners_iff
        g h hmin z w u b).mp hb
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact hbDirect.2.2.2.2.1
    · exact hbDirect.2.2.2.2.2.1
    · exact hbDirect.2.2.2.2.2.2
  have hflat :=
    card_minimalSupportPrivateSelfHeavyTripleAtLeastFourFiber_le_direct
      g h hmin z w u
  have hcount' : L * r < (4 - R.card) * S.card := by
    rw [hset.2]
    simpa using hcount.trans_le hflat
  rcases
      minimalSupportPrivateSelfHeavyOmissionDegreeExtension_capacity_or_largeFiber
        g h hmin S R 4 hself hdegree hfixed hset.1 L r hcount' with
    hcapacity | ⟨v, hvB, hvR, hvFiber⟩
  · left
    rw [hset.2] at hcapacity
    exact hcapacity
  · right
    have hvNe : v ≠ z ∧ v ≠ w ∧ v ≠ u := by simpa [R] using hvR
    exact ⟨v, hvB, hvNe.1, hvNe.2.1, hvNe.2.2, by simpa [S, R,
      minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionFiber] using
        hvFiber⟩

/-- Four-stage cyclic omission endpoint.  Exact-three is replaced by its
uniform linear bound, while the at-least-four arm either pays one more
capacity unit or reaches four fixed external omissions. -/
theorem minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_boundedExactThree_or_quadrupleFiber
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (K L r L' r' L'' r'' L''' r''' : ℕ)
    (hself : K ≤
      (minimalSupportPrivateSelfHeavyVertices g h hmin).card)
    (hfirst : 2 * (L * r) < 3 * K)
    (hsecond : L' * r' < 2 * (r + 1))
    (hthird : L'' * r'' < r' + 1)
    (hfourth : 2 * (L''' * r''') < r'' + 1) :
    K ≤ 2 *
        (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ∨
      B.card + L ≤ m + 1 ∨
      B.card + 1 + L' ≤ m + 1 ∨
      B.card + 2 + L'' ≤ m + 1 ∨
      r'' + 1 ≤ 2 * (3 + 2 * (m + 1 - B.card)) ∨
      B.card + 3 + L''' ≤ m + 1 ∨
      ∃ z w u v : Fin (m + 1),
        z ∉ B ∧ w ∉ B ∧ u ∉ B ∧ v ∉ B ∧
        w ≠ z ∧ u ≠ z ∧ u ≠ w ∧
        v ≠ z ∧ v ≠ w ∧ v ≠ u ∧
        r''' <
          (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionFiber
            g h hmin z w u v).card := by
  rcases
      minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_boundedExactThree_or_tripleAtLeastFour
        g hg hmin K L r L' r' L'' r'' hself hfirst hsecond hthird with
    htwo | hcap | hcap' | hcap'' | hexact |
      ⟨z, w, u, hzB, hwB, huB, hwz, huz, huw, hfour⟩
  · exact Or.inl htwo
  · exact Or.inr (Or.inl hcap)
  · exact Or.inr (Or.inr (Or.inl hcap'))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hcap'')))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hexact))))
  · have hinner : L''' * r''' <
        (minimalSupportPrivateSelfHeavyTripleAtLeastFourFiber
          g h hmin z w u).card := by omega
    rcases
        minimalSupportPrivateSelfHeavyAtLeastFourTripleOmission_capacity_or_quadrupleFiber
          g h hmin z w u hzB hwB huB hwz huz huw L''' r''' hinner with
      hcap''' | ⟨v, hvB, hvz, hvw, hvu, hvFiber⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcap''')))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨z, w, u, v, hzB, hwB, huB, hvB, hwz, huz, huw,
          hvz, hvw, hvu, hvFiber⟩)))))

end MinModulus
