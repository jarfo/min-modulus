/-
# Source-omission versus target-heavy split at a fixed gap

Every edge in a fixed `(gap, omission)` fiber raises the coefficient at the
gap coordinate by at least two.  The witness floor gives an exact local
alternative: either the source coefficient is `-1`, adding the gap to that
witness's omissions, or the source coefficient is nonnegative, making the
target coefficient at least two.

This partitions the edge fiber and turns its multiplicity into two explicit
vertex currencies: sources omitting both fixed external coordinates, and
targets heavy at the gap while still omitting the common omission.
-/
import MinModulus.G1PrivateHeavyGapOmissionVertices

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Edges whose source also omits the fixed gap coordinate. -/
noncomputable def minimalSupportSelectedPrivateGapSourceOmissionPairs
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) :
    Finset (MinimalSupportSelectedDistinctOrderedPair S) := by
  classical
  exact (minimalSupportSelectedPrivateExternalGapOmissionFiber
    g hg hh hmin S z w).filter (fun p ↦
      minimalSupportPrivateWitness g h hmin p.val.1.val z = -1)

/-- Complementary edges whose source does not omit the fixed gap. -/
noncomputable def minimalSupportSelectedPrivateGapNonOmissionSourcePairs
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) :
    Finset (MinimalSupportSelectedDistinctOrderedPair S) := by
  classical
  exact (minimalSupportSelectedPrivateExternalGapOmissionFiber
    g hg hh hmin S z w).filter (fun p ↦
      minimalSupportPrivateWitness g h hmin p.val.1.val z ≠ -1)

/-- The source-omission and non-omission-source edges partition the fixed
`(gap, omission)` pair fiber. -/
theorem card_minimalSupportSelectedPrivateGapSourceOmission_add_nonOmissionSourcePairs
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) :
    (minimalSupportSelectedPrivateGapSourceOmissionPairs
        g hg hh hmin S z w).card +
      (minimalSupportSelectedPrivateGapNonOmissionSourcePairs
        g hg hh hmin S z w).card =
      (minimalSupportSelectedPrivateExternalGapOmissionFiber
        g hg hh hmin S z w).card := by
  classical
  let P := minimalSupportSelectedPrivateExternalGapOmissionFiber
    g hg hh hmin S z w
  let D := minimalSupportSelectedPrivateGapSourceOmissionPairs
    g hg hh hmin S z w
  let H := minimalSupportSelectedPrivateGapNonOmissionSourcePairs
    g hg hh hmin S z w
  have hdisj : Disjoint D H := by
    rw [Finset.disjoint_left]
    intro p hpD hpH
    exact (Finset.mem_filter.mp hpH).2 (Finset.mem_filter.mp hpD).2
  have hunion : D ∪ H = P := by
    ext p
    simp only [Finset.mem_union]
    constructor
    · rintro (hpD | hpH)
      · exact (Finset.mem_filter.mp hpD).1
      · exact (Finset.mem_filter.mp hpH).1
    · intro hp
      by_cases hsource :
          minimalSupportPrivateWitness g h hmin p.val.1.val z = -1
      · exact Or.inl (Finset.mem_filter.mpr ⟨hp, hsource⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hp, hsource⟩)
  change D.card + H.card = P.card
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- Source vertices which omit both the fixed gap and common-omission
coordinates. -/
noncomputable def minimalSupportSelectedPrivateGapSourceOmissionVertices
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) : Finset ↥S := by
  classical
  exact (minimalSupportSelectedPrivateGapSourceOmissionPairs
    g hg hh hmin S z w).image (fun p ↦ p.val.1)

/-- Target vertices made coefficient-heavy at the fixed gap by a
non-omitting source edge. -/
noncomputable def minimalSupportSelectedPrivateGapHeavyTargetVertices
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) : Finset ↥S := by
  classical
  exact (minimalSupportSelectedPrivateGapNonOmissionSourcePairs
    g hg hh hmin S z w).image (fun p ↦ p.val.2)

/-- A source-omission vertex omits both distinct external coordinates. -/
theorem minimalSupportSelectedPrivateGapSourceOmissionVertices_spec
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) {b : ↥S}
    (hb : b ∈ minimalSupportSelectedPrivateGapSourceOmissionVertices
      g hg hh hmin S z w) :
    z ∉ B ∧ w ∉ B ∧ w ≠ z ∧
      minimalSupportPrivateWitness g h hmin b.val z = -1 ∧
      minimalSupportPrivateWitness g h hmin b.val w = -1 := by
  classical
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
  have hpData := Finset.mem_filter.mp hp
  have hpSpec :=
    minimalSupportSelectedPrivateExternalGapOmissionFiber_spec
      g hg hh hmin S hpData.1
  exact ⟨hpSpec.1, hpSpec.2.1, hpSpec.2.2.1,
    hpData.2, hpSpec.2.2.2.2.1⟩

/-- A complementary target vertex is coefficient-heavy at the fixed gap and
still omits the common omission coordinate. -/
theorem minimalSupportSelectedPrivateGapHeavyTargetVertices_spec
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) {b : ↥S}
    (hb : b ∈ minimalSupportSelectedPrivateGapHeavyTargetVertices
      g hg hh hmin S z w) :
    z ∉ B ∧ w ∉ B ∧ w ≠ z ∧
      2 ≤ minimalSupportPrivateWitness g h hmin b.val z ∧
      minimalSupportPrivateWitness g h hmin b.val w = -1 := by
  classical
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
  have hpData := Finset.mem_filter.mp hp
  have hpSpec :=
    minimalSupportSelectedPrivateExternalGapOmissionFiber_spec
      g hg hh hmin S hpData.1
  have hsourceFloor :=
    (minimalSupportPrivateWitness_isWitness g h hmin p.val.1.val).2.1 z
  have hsourceNonneg :
      0 ≤ minimalSupportPrivateWitness g h hmin p.val.1.val z := by
    omega
  have htargetHeavy :
      2 ≤ minimalSupportPrivateWitness g h hmin p.val.2.val z := by
    omega
  exact ⟨hpSpec.1, hpSpec.2.1, hpSpec.2.2.1,
    htargetHeavy, hpSpec.2.2.2.2.2⟩

/-- The double-omission source vertices and gap-heavy target vertices are
disjoint coefficient classes. -/
theorem minimalSupportSelectedPrivateGapSourceOmissionVertices_disjoint_heavyTargets
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) :
    Disjoint
      (minimalSupportSelectedPrivateGapSourceOmissionVertices
        g hg hh hmin S z w)
      (minimalSupportSelectedPrivateGapHeavyTargetVertices
        g hg hh hmin S z w) := by
  rw [Finset.disjoint_left]
  intro b hbD hbH
  have hbDspec :=
    minimalSupportSelectedPrivateGapSourceOmissionVertices_spec
      g hg hh hmin S z w hbD
  have hbHspec :=
    minimalSupportSelectedPrivateGapHeavyTargetVertices_spec
      g hg hh hmin S z w hbH
  omega

/-- The two structural vertex classes are disjoint subfamilies of the full
endpoint family. -/
theorem card_minimalSupportSelectedPrivateGapSourceOmission_add_heavyTargetVertices_le_endpoints
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) :
    (minimalSupportSelectedPrivateGapSourceOmissionVertices
        g hg hh hmin S z w).card +
      (minimalSupportSelectedPrivateGapHeavyTargetVertices
        g hg hh hmin S z w).card ≤
      (minimalSupportSelectedPrivateExternalGapOmissionVertices
        g hg hh hmin S z w).card := by
  classical
  let D := minimalSupportSelectedPrivateGapSourceOmissionVertices
    g hg hh hmin S z w
  let H := minimalSupportSelectedPrivateGapHeavyTargetVertices
    g hg hh hmin S z w
  let V := minimalSupportSelectedPrivateExternalGapOmissionVertices
    g hg hh hmin S z w
  have hDsub : D ⊆ V := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    apply (mem_minimalSupportSelectedPrivateExternalGapOmissionVertices_iff
      g hg hh hmin S z w p.val.1).mpr
    exact Or.inl ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩
  have hHsub : H ⊆ V := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    apply (mem_minimalSupportSelectedPrivateExternalGapOmissionVertices_iff
      g hg hh hmin S z w p.val.2).mpr
    exact Or.inr ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩
  have hdisj :=
    minimalSupportSelectedPrivateGapSourceOmissionVertices_disjoint_heavyTargets
      g hg hh hmin S z w
  change D.card + H.card ≤ V.card
  rw [← Finset.card_union_of_disjoint hdisj]
  exact Finset.card_le_card (Finset.union_subset hDsub hHsub)

/-- Source-omission edges inject into double-omission sources times arbitrary
endpoint vertices. -/
theorem card_minimalSupportSelectedPrivateGapSourceOmissionPairs_le_vertices
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) :
    (minimalSupportSelectedPrivateGapSourceOmissionPairs
        g hg hh hmin S z w).card ≤
      (minimalSupportSelectedPrivateGapSourceOmissionVertices
        g hg hh hmin S z w).card *
      (minimalSupportSelectedPrivateExternalGapOmissionVertices
        g hg hh hmin S z w).card := by
  classical
  let P := minimalSupportSelectedPrivateGapSourceOmissionPairs
    g hg hh hmin S z w
  let D := minimalSupportSelectedPrivateGapSourceOmissionVertices
    g hg hh hmin S z w
  let V := minimalSupportSelectedPrivateExternalGapOmissionVertices
    g hg hh hmin S z w
  let enc : ↥P → ↥D × ↥V := fun p ↦
    (⟨p.val.val.1, Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩⟩,
      ⟨p.val.val.2, by
        apply (mem_minimalSupportSelectedPrivateExternalGapOmissionVertices_iff
          g hg hh hmin S z w p.val.val.2).mpr
        exact Or.inr ⟨p.val, (Finset.mem_filter.mp p.property).1, rfl⟩⟩)
  have henc : Function.Injective enc := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun x ↦ x.1.val) hpq
    · exact congrArg (fun x ↦ x.2.val) hpq
  have hcard := Fintype.card_le_of_injective enc henc
  change P.card ≤ D.card * V.card
  calc
    P.card = Fintype.card ↥P := (Fintype.card_coe P).symm
    _ ≤ Fintype.card (↥D × ↥V) := hcard
    _ = D.card * V.card := by simp

/-- Non-omission-source edges inject into arbitrary endpoint vertices times
gap-heavy targets. -/
theorem card_minimalSupportSelectedPrivateGapNonOmissionSourcePairs_le_vertices
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) :
    (minimalSupportSelectedPrivateGapNonOmissionSourcePairs
        g hg hh hmin S z w).card ≤
      (minimalSupportSelectedPrivateExternalGapOmissionVertices
        g hg hh hmin S z w).card *
      (minimalSupportSelectedPrivateGapHeavyTargetVertices
        g hg hh hmin S z w).card := by
  classical
  let P := minimalSupportSelectedPrivateGapNonOmissionSourcePairs
    g hg hh hmin S z w
  let V := minimalSupportSelectedPrivateExternalGapOmissionVertices
    g hg hh hmin S z w
  let H := minimalSupportSelectedPrivateGapHeavyTargetVertices
    g hg hh hmin S z w
  let enc : ↥P → ↥V × ↥H := fun p ↦
    (⟨p.val.val.1, by
        apply (mem_minimalSupportSelectedPrivateExternalGapOmissionVertices_iff
          g hg hh hmin S z w p.val.val.1).mpr
        exact Or.inl ⟨p.val, (Finset.mem_filter.mp p.property).1, rfl⟩⟩,
      ⟨p.val.val.2, Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩⟩)
  have henc : Function.Injective enc := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun x ↦ x.1.val) hpq
    · exact congrArg (fun x ↦ x.2.val) hpq
  have hcard := Fintype.card_le_of_injective enc henc
  change P.card ≤ V.card * H.card
  calc
    P.card = Fintype.card ↥P := (Fintype.card_coe P).symm
    _ ≤ Fintype.card (↥V × ↥H) := hcard
    _ = V.card * H.card := by simp

/-- Quantitative source/target alternative inside a fixed
`(gap, omission)` fiber. -/
theorem minimalSupportSelectedPrivateGap_manySourceOmissions_or_manyHeavyTargets
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) (A C : ℕ)
    (hcount : (A + C) *
        (minimalSupportSelectedPrivateExternalGapOmissionVertices
          g hg hh hmin S z w).card <
      (minimalSupportSelectedPrivateExternalGapOmissionFiber
        g hg hh hmin S z w).card) :
    A < (minimalSupportSelectedPrivateGapSourceOmissionVertices
      g hg hh hmin S z w).card ∨
      C < (minimalSupportSelectedPrivateGapHeavyTargetVertices
        g hg hh hmin S z w).card := by
  have hpartition :=
    card_minimalSupportSelectedPrivateGapSourceOmission_add_nonOmissionSourcePairs
      g hg hh hmin S z w
  have hDbound :=
    card_minimalSupportSelectedPrivateGapSourceOmissionPairs_le_vertices
      g hg hh hmin S z w
  have hHbound :=
    card_minimalSupportSelectedPrivateGapNonOmissionSourcePairs_le_vertices
      g hg hh hmin S z w
  by_contra hlarge
  push Not at hlarge
  rcases hlarge with ⟨hD, hH⟩
  have hDmul := Nat.mul_le_mul_right
    (minimalSupportSelectedPrivateExternalGapOmissionVertices
      g hg hh hmin S z w).card hD
  have hHmul := Nat.mul_le_mul_left
    (minimalSupportSelectedPrivateExternalGapOmissionVertices
      g hg hh hmin S z w).card hH
  have htotal :
      (minimalSupportSelectedPrivateExternalGapOmissionFiber
          g hg hh hmin S z w).card ≤
        (A + C) *
          (minimalSupportSelectedPrivateExternalGapOmissionVertices
            g hg hh hmin S z w).card := by
    calc
      (minimalSupportSelectedPrivateExternalGapOmissionFiber
          g hg hh hmin S z w).card =
          (minimalSupportSelectedPrivateGapSourceOmissionPairs
              g hg hh hmin S z w).card +
            (minimalSupportSelectedPrivateGapNonOmissionSourcePairs
              g hg hh hmin S z w).card := hpartition.symm
      _ ≤ (minimalSupportSelectedPrivateGapSourceOmissionVertices
              g hg hh hmin S z w).card *
            (minimalSupportSelectedPrivateExternalGapOmissionVertices
              g hg hh hmin S z w).card +
          (minimalSupportSelectedPrivateExternalGapOmissionVertices
              g hg hh hmin S z w).card *
            (minimalSupportSelectedPrivateGapHeavyTargetVertices
              g hg hh hmin S z w).card := Nat.add_le_add hDbound hHbound
      _ ≤ A * (minimalSupportSelectedPrivateExternalGapOmissionVertices
              g hg hh hmin S z w).card +
          (minimalSupportSelectedPrivateExternalGapOmissionVertices
              g hg hh hmin S z w).card * C := Nat.add_le_add hDmul hHmul
      _ = (A + C) *
          (minimalSupportSelectedPrivateExternalGapOmissionVertices
            g hg hh hmin S z w).card := by
        simp [Nat.add_mul, Nat.mul_comm]
  exact (Nat.not_lt_of_ge htotal) hcount

end MinModulus
