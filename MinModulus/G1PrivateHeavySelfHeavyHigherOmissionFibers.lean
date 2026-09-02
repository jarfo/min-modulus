/-
# Omission fibers of higher-omission self-heavy owners

Every owner in the at-least-three self-heavy layer contributes at least three
owner/omission incidences, and privacy puts every omission outside the minimal
transversal.  Exact image/fiber counting therefore turns a large higher-
omission population into ambient complement capacity or many distinct owners
sharing one fixed external omission.
-/
import MinModulus.G1PrivateHeavySelfHeavyHigherOmissions

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Owner/coordinate pairs where a higher-omission self-heavy private witness
omits the displayed coordinate. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Finset (Σ _b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
        g h hmin), Fin (m + 1)) := by
  classical
  exact Finset.univ.sigma (fun b ↦
    witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val.val))

@[simp] theorem mem_minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (p : Σ _b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
        g h hmin), Fin (m + 1)) :
    p ∈ minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences
        g h hmin ↔
      p.2 ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin p.1.val.val) := by
  classical
  simp [minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences]

/-- Exact owner-fiber sum for all higher-omission incidences. -/
theorem card_minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences
        g h hmin).card =
      ∑ b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin),
        (witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val.val)).card := by
  classical
  exact Finset.card_sigma _ _

/-- Every higher-omission owner contributes at least three incidences. -/
theorem three_mul_card_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_le_incidences
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    3 * (minimalSupportPrivateSelfHeavyAtLeastThreeVertices
        g h hmin).card ≤
      (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences
        g h hmin).card := by
  classical
  rw [card_minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences]
  calc
    3 * (minimalSupportPrivateSelfHeavyAtLeastThreeVertices
          g h hmin).card =
        ∑ _b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
          g h hmin), 3 := by simp [Nat.mul_comm]
    _ ≤ ∑ b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
          g h hmin),
        (witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val.val)).card := by
      apply Finset.sum_le_sum
      intro b _hb
      exact
        (mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
          g h hmin b.val).mp b.property |>.2

/-- The coordinate label of one higher-omission incidence. -/
def minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabel
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (p : Σ _b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
        g h hmin), Fin (m + 1)) : Fin (m + 1) :=
  p.2

/-- External omission coordinates used by the higher-omission layer. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabels
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Finset (Fin (m + 1)) := by
  classical
  exact (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences
    g h hmin).image
      (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabel g h hmin)

/-- Incidences carrying one fixed omission coordinate. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidenceFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1)) :=
  (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences
    g h hmin).filter (fun p ↦
      minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabel
        g h hmin p = z)

/-- Higher-omission owners whose private witness omits one fixed coordinate. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1)) :
    Finset ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin) := by
  classical
  exact Finset.univ.filter (fun b ↦
    z ∈ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val.val))

/-- Every higher-omission incidence has an external coordinate label. -/
theorem minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabel_not_mem
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (p : Σ _b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
        g h hmin), Fin (m + 1))
    (hp : p ∈ minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences
      g h hmin) :
    minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabel
        g h hmin p ∉ B := by
  have hpO :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences_iff
      g h hmin p).mp hp
  have hbSelf :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
      g h hmin p.1.val).mp p.1.property |>.1
  have hsubset := minimalSupportPrivateSelfHeavy_omissions_subset_compl
    g h hmin hbSelf
  exact (Finset.mem_sdiff.mp (hsubset hpO)).2

/-- All omission labels of the higher layer are disjoint from the minimal
transversal. -/
theorem minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabels_disjoint
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Disjoint (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabels
      g h hmin) B := by
  classical
  rw [Finset.disjoint_left]
  intro z hz hzB
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  exact minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabel_not_mem
    g h hmin p hp hzB

/-- At a fixed coordinate, incidence count equals the number of distinct
higher-omission owners in the corresponding fiber. -/
theorem card_minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidenceFiber_eq
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidenceFiber
        g h hmin z).card =
      (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
        g h hmin z).card := by
  classical
  apply Finset.card_bij (fun p _hp ↦ p.1)
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpO :=
      (mem_minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences_iff
        g h hmin p).mp hp'.1
    rw [show p.2 = z by exact hp'.2] at hpO
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpO⟩
  · intro p hp q hq hpq
    have hpz := (Finset.mem_filter.mp hp).2
    have hqz := (Finset.mem_filter.mp hq).2
    apply Sigma.ext hpq
    simp only [minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabel] at hpz hqz
    exact heq_of_eq (hpz.trans hqz.symm)
  · intro b hb
    have hb' := Finset.mem_filter.mp hb
    let p : Σ _b : ↥(minimalSupportPrivateSelfHeavyAtLeastThreeVertices
        g h hmin), Fin (m + 1) := ⟨b, z⟩
    refine ⟨p, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply
        (mem_minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences_iff
          g h hmin p).mpr
      exact hb'.2
    · rfl

/-- Exact label/fiber dichotomy for the higher-omission incidence family. -/
theorem minimalSupportPrivateSelfHeavyAtLeastThreeOmission_labelImage_or_largeFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (L r : ℕ)
    (hcount : L * r <
      (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences
        g h hmin).card) :
    L ≤ (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabels
        g h hmin).card ∨
      ∃ z ∈ minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabels
          g h hmin,
        r < (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
          g h hmin z).card := by
  classical
  let I := minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences
    g h hmin
  let label := minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabel
    g h hmin
  let labels := minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabels
    g h hmin
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
    rw [← card_minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidenceFiber_eq
      g h hmin z]
    simpa [label, I,
      minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidenceFiber] using
        hfiber

/-- A large higher-omission population either consumes many coordinates of
the ambient complement or has a large owner fiber sharing one fixed external
omission. -/
theorem minimalSupportPrivateSelfHeavyAtLeastThreeOmission_capacity_or_largeFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (L r : ℕ)
    (hcount : L * r < 3 *
      (minimalSupportPrivateSelfHeavyAtLeastThreeVertices g h hmin).card) :
    B.card + L ≤ m + 1 ∨
      ∃ z : Fin (m + 1), z ∉ B ∧
        r < (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
          g h hmin z).card := by
  have hinc :=
    three_mul_card_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_le_incidences
      g h hmin
  have hcount' : L * r <
      (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences
        g h hmin).card :=
    lt_of_lt_of_le hcount hinc
  rcases
      minimalSupportPrivateSelfHeavyAtLeastThreeOmission_labelImage_or_largeFiber
        g h hmin L r hcount' with hlabels | hfiber
  · left
    have hdisj :=
      minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabels_disjoint
        g h hmin
    have hcap : B.card +
        (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabels
          g h hmin).card ≤ m + 1 := by
      rw [← Finset.card_union_of_disjoint hdisj.symm]
      simpa using Finset.card_le_univ
        (B ∪ minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabels
          g h hmin)
    omega
  · right
    obtain ⟨z, hzLabel, hzFiber⟩ := hfiber
    have hzB : z ∉ B :=
      Finset.disjoint_left.mp
        (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabels_disjoint
          g h hmin) hzLabel
    exact ⟨z, hzB, hzFiber⟩

/-- Direct quantitative bridge from any upstream lower bound on the full
self-heavy family.  Either the exact-two layer already carries half that
bound, or the higher-omission incidence count forces complement capacity or
a large fixed external-omission owner fiber. -/
theorem minimalSupportPrivateSelfHeavy_exactTwo_or_higherOmission_capacity_or_largeFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (K L r : ℕ)
    (hself : K ≤
      (minimalSupportPrivateSelfHeavyVertices g h hmin).card)
    (hcount : 2 * (L * r) < 3 * K) :
    K ≤ 2 *
        (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ∨
      B.card + L ≤ m + 1 ∨
      ∃ z : Fin (m + 1), z ∉ B ∧
        r < (minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber
          g h hmin z).card := by
  rcases le_two_mul_exactTwo_or_le_two_mul_atLeastThree_of_le_selfHeavy
      g h hmin K hself with htwo | hhigher
  · exact Or.inl htwo
  · right
    have hinner : L * r < 3 *
        (minimalSupportPrivateSelfHeavyAtLeastThreeVertices
          g h hmin).card := by
      omega
    exact minimalSupportPrivateSelfHeavyAtLeastThreeOmission_capacity_or_largeFiber
      g h hmin L r hinner

end MinModulus
