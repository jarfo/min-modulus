/-
# Endpoint vertices of a gap/omission pair fiber

A pair fiber with fixed directed gap and common omission is an oriented graph
on selected private owners.  At the gap coordinate every edge raises the
coefficient by at least two.  Hence the reverse of a selected edge cannot
also be selected in the same fiber.

Adjoining all edges and all formal reverses therefore injects into the square
of the endpoint-vertex set.  This improves the naive pair-to-vertex bound by
a factor of two.  Every endpoint still omits the common omission coordinate.
-/
import MinModulus.G1PrivateHeavyGapOmissionFibers

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Selected owners occurring as either endpoint of a fixed external
`(gap, omission)` pair fiber. -/
noncomputable def minimalSupportSelectedPrivateExternalGapOmissionVertices
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) : Finset ↥S := by
  classical
  let P := minimalSupportSelectedPrivateExternalGapOmissionFiber
    g hg hh hmin S z w
  exact P.image (fun p ↦ p.val.1) ∪ P.image (fun p ↦ p.val.2)

@[simp] theorem mem_minimalSupportSelectedPrivateExternalGapOmissionVertices_iff
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) (b : ↥S) :
    b ∈ minimalSupportSelectedPrivateExternalGapOmissionVertices
        g hg hh hmin S z w ↔
      (∃ p ∈ minimalSupportSelectedPrivateExternalGapOmissionFiber
          g hg hh hmin S z w, p.val.1 = b) ∨
      ∃ p ∈ minimalSupportSelectedPrivateExternalGapOmissionFiber
          g hg hh hmin S z w, p.val.2 = b := by
  classical
  simp [minimalSupportSelectedPrivateExternalGapOmissionVertices]

/-- Every endpoint vertex in the fixed pair fiber omits its common omission
coordinate. -/
theorem minimalSupportSelectedPrivateExternalGapOmissionVertices_omit
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) {b : ↥S}
    (hb : b ∈ minimalSupportSelectedPrivateExternalGapOmissionVertices
      g hg hh hmin S z w) :
    minimalSupportPrivateWitness g h hmin b.val w = -1 := by
  rcases
      (mem_minimalSupportSelectedPrivateExternalGapOmissionVertices_iff
        g hg hh hmin S z w b).mp hb with
    ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact
      (minimalSupportSelectedPrivateExternalGapOmissionFiber_spec
        g hg hh hmin S hp).2.2.2.2.1
  · exact
      (minimalSupportSelectedPrivateExternalGapOmissionFiber_spec
        g hg hh hmin S hp).2.2.2.2.2

/-- An oriented fixed-gap fiber and all of its formal reverses inject into
the square of its endpoint-vertex set.  The cross cases are impossible
because the same coefficient cannot rise by two in both directions. -/
theorem two_mul_card_minimalSupportSelectedPrivateExternalGapOmissionFiber_le_sq_vertices
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) :
    2 * (minimalSupportSelectedPrivateExternalGapOmissionFiber
        g hg hh hmin S z w).card ≤
      (minimalSupportSelectedPrivateExternalGapOmissionVertices
        g hg hh hmin S z w).card ^ 2 := by
  classical
  let P := minimalSupportSelectedPrivateExternalGapOmissionFiber
    g hg hh hmin S z w
  let V := minimalSupportSelectedPrivateExternalGapOmissionVertices
    g hg hh hmin S z w
  let src : ↥P → ↥V := fun p ↦
    ⟨p.val.val.1, Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩)⟩
  let dst : ↥P → ↥V := fun p ↦
    ⟨p.val.val.2, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩)⟩
  let enc : Sum ↥P ↥P → ↥V × ↥V
    | Sum.inl p => (src p, dst p)
    | Sum.inr p => (dst p, src p)
  have henc : Function.Injective enc := by
    intro a b hab
    rcases a with p | p <;> rcases b with q | q
    · have hs : p.val.val.1 = q.val.val.1 :=
        congrArg (fun x ↦ x.1.val) hab
      have ht : p.val.val.2 = q.val.val.2 :=
        congrArg (fun x ↦ x.2.val) hab
      have hpq : p = q := by
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext hs ht
      exact congrArg Sum.inl hpq
    · exfalso
      have hs : p.val.val.1 = q.val.val.2 :=
        congrArg (fun x ↦ x.1.val) hab
      have ht : p.val.val.2 = q.val.val.1 :=
        congrArg (fun x ↦ x.2.val) hab
      have hpGap :=
        (minimalSupportSelectedPrivateExternalGapOmissionFiber_spec
          g hg hh hmin S p.property).2.2.2.1
      have hqGap :=
        (minimalSupportSelectedPrivateExternalGapOmissionFiber_spec
          g hg hh hmin S q.property).2.2.2.1
      rw [hs, ht] at hpGap
      omega
    · exfalso
      have hs : p.val.val.2 = q.val.val.1 :=
        congrArg (fun x ↦ x.1.val) hab
      have ht : p.val.val.1 = q.val.val.2 :=
        congrArg (fun x ↦ x.2.val) hab
      have hpGap :=
        (minimalSupportSelectedPrivateExternalGapOmissionFiber_spec
          g hg hh hmin S p.property).2.2.2.1
      have hqGap :=
        (minimalSupportSelectedPrivateExternalGapOmissionFiber_spec
          g hg hh hmin S q.property).2.2.2.1
      rw [hs, ht] at hpGap
      omega
    · have hs : p.val.val.2 = q.val.val.2 :=
        congrArg (fun x ↦ x.1.val) hab
      have ht : p.val.val.1 = q.val.val.1 :=
        congrArg (fun x ↦ x.2.val) hab
      have hpq : p = q := by
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext ht hs
      exact congrArg Sum.inr hpq
  have hcard := Fintype.card_le_of_injective enc henc
  change 2 * P.card ≤ V.card ^ 2
  calc
    2 * P.card = Fintype.card (Sum ↥P ↥P) := by simp [two_mul]
    _ ≤ Fintype.card (↥V × ↥V) := hcard
    _ = V.card ^ 2 := by simp [pow_two]

/-- More than `r` oriented pairs force the endpoint square to contain at
least `2(r+1)` ordered slots. -/
theorem two_mul_succ_le_sq_gapOmissionVertices_of_largeFiber
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) (r : ℕ)
    (hlarge : r < (minimalSupportSelectedPrivateExternalGapOmissionFiber
      g hg hh hmin S z w).card) :
    2 * (r + 1) ≤
      (minimalSupportSelectedPrivateExternalGapOmissionVertices
        g hg hh hmin S z w).card ^ 2 := by
  have hsucc : r + 1 ≤
      (minimalSupportSelectedPrivateExternalGapOmissionFiber
        g hg hh hmin S z w).card := Nat.succ_le_iff.mpr hlarge
  exact (Nat.mul_le_mul_left 2 hsucc).trans
    (two_mul_card_minimalSupportSelectedPrivateExternalGapOmissionFiber_le_sq_vertices
      g hg hh hmin S z w)

/-- The second label split expressed directly as ambient capacity or a large
family of endpoint vertices sharing the fixed common omission. -/
theorem minimalSupportSelectedPrivateExternalGapOmission_capacity_or_largeVertices
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z : Fin m) (L r : ℕ)
    (hcount : L * r < (minimalSupportSelectedPrivateExternalGapFiber
      g hg h hmin S z).card) :
    B.card + 1 + L ≤ m ∨
      ∃ w : Fin m, w ∉ B ∧ w ≠ z ∧
        2 * (r + 1) ≤
          (minimalSupportSelectedPrivateExternalGapOmissionVertices
            g hg hh hmin S z w).card ^ 2 := by
  rcases
      minimalSupportSelectedPrivateExternalGapOmission_capacity_or_largeFiber
        g hg hh hmin S z L r hcount with hcapacity | hfiber
  · exact Or.inl hcapacity
  · right
    obtain ⟨w, hwB, hwz, hwFiber⟩ := hfiber
    exact ⟨w, hwB, hwz,
      two_mul_succ_le_sq_gapOmissionVertices_of_largeFiber
        g hg hh hmin S z w r hwFiber⟩

/-- Full two-stage count with the terminal pair multiplicity converted to a
quantitative family of private endpoint vertices. -/
theorem minimalSupportSelectedPrivate_selfHeavy_or_capacity_or_gapOmissionVertices
    (g : Fin (m + 1) → G) (hg : ValidTuple g) (h : G)
    (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (K L r L' r' : ℕ)
    (hcount : K * S.card + L * r < S.card * (S.card - 1))
    (hinner : L' * r' ≤ r) :
    K ≤ (minimalSupportPrivateSelfHeavyVertices g h hmin).card ∨
      B.card + L ≤ m + 1 ∨
      B.card + 1 + L' ≤ m + 1 ∨
      ∃ z w : Fin (m + 1), z ∉ B ∧ w ∉ B ∧ w ≠ z ∧
        2 * (r' + 1) ≤
          (minimalSupportSelectedPrivateExternalGapOmissionVertices
            g hg hh hmin S z w).card ^ 2 := by
  rcases
      minimalSupportSelectedPrivate_selfHeavy_or_capacity_or_gapOmissionFiber
        g hg h hh hmin S K L r L' r' hcount hinner with
    hself | hcapacity | hsecondCapacity | hfiber
  · exact Or.inl hself
  · exact Or.inr (Or.inl hcapacity)
  · exact Or.inr (Or.inr (Or.inl hsecondCapacity))
  · obtain ⟨z, w, hzB, hwB, hwz, hwFiber⟩ := hfiber
    exact Or.inr (Or.inr (Or.inr
      ⟨z, w, hzB, hwB, hwz,
        two_mul_succ_le_sq_gapOmissionVertices_of_largeFiber
          g hg hh hmin S z w r' hwFiber⟩))

end MinModulus
