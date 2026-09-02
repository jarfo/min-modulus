/-
# Vertex fibers of external private-witness omissions

A large label fiber consists of ordered pairs whose two endpoints both lie
among the private witnesses omitting that label.  It therefore embeds into
the square of a vertex fiber.  Conversely, many distinct external labels
consume ambient coordinates disjoint from the deletion set.  This converts
the pair-label pigeonhole theorem into a dimension-capacity versus large
private-witness-fiber dichotomy.
-/
import MinModulus.G1PrivateHeavyTransversalOmissionFibers

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Vertices whose canonical private witness omits the external coordinate
`z`. -/
noncomputable def minimalSupportPrivateOmissionVertices
    (g : Fin m → G) {h : G}
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin m) : Finset ↥B := by
  classical
  exact Finset.univ.filter (fun b ↦
    minimalSupportPrivateWitness g h hmin b z = -1)

@[simp] theorem mem_minimalSupportPrivateOmissionVertices_iff
    (g : Fin m → G) {h : G}
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin m) (b : ↥B) :
    b ∈ minimalSupportPrivateOmissionVertices g hmin z ↔
      minimalSupportPrivateWitness g h hmin b z = -1 := by
  classical
  simp [minimalSupportPrivateOmissionVertices]

/-- A chosen-label pair fiber injects into the square of the corresponding
private-omission vertex fiber. -/
theorem card_minimalSupportPrivateCommonOmissionFiber_le_square_vertices
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin m) :
    (minimalSupportPrivateCommonOmissionFiber g hg hh hmin z).card ≤
      (minimalSupportPrivateOmissionVertices g hmin z).card *
        (minimalSupportPrivateOmissionVertices g hmin z).card := by
  classical
  let F := minimalSupportPrivateCommonOmissionFiber g hg hh hmin z
  let V := minimalSupportPrivateOmissionVertices g hmin z
  let e : ↥F → ↥V × ↥V := fun p ↦ by
    have hp := minimalSupportPrivateCommonOmissionFiber_spec
      g hg hh hmin p.property
    exact (⟨p.val.val.1, by
      exact (mem_minimalSupportPrivateOmissionVertices_iff
        g hmin z p.val.val.1).2 hp.2.1⟩,
      ⟨p.val.val.2, by
        exact (mem_minimalSupportPrivateOmissionVertices_iff
          g hmin z p.val.val.2).2 hp.2.2⟩)
  have heinj : Function.Injective e := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun x ↦ x.1.val) hpq
    · exact congrArg (fun x ↦ x.2.val) hpq
  have hcard := Fintype.card_le_of_injective e heinj
  change F.card ≤ V.card * V.card
  calc
    F.card = Fintype.card ↥F := (Fintype.card_coe F).symm
    _ ≤ Fintype.card (↥V × ↥V) := hcard
    _ = V.card * V.card := by simp

/-- The deletion vertices and all selected external labels fit disjointly
inside the ambient coordinate set. -/
theorem card_minimalSupport_add_commonOmissionLabels_le
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    B.card +
      (minimalSupportPrivateCommonOmissionLabels g hg hh hmin).card ≤ m := by
  classical
  let Z := minimalSupportPrivateCommonOmissionLabels g hg hh hmin
  have hdisj : Disjoint Z B :=
    minimalSupportPrivateCommonOmissionLabels_disjoint g hg hh hmin
  have hunion : (B ∪ Z).card = B.card + Z.card := by
    rw [Finset.card_union_of_disjoint hdisj.symm]
  have hle : (B ∪ Z).card ≤ m := by
    simpa using Finset.card_le_univ (B ∪ Z)
  change B.card + Z.card ≤ m
  rw [← hunion]
  exact hle

/-- Refined pair-label dichotomy.  Under the same exact pair-count
hypothesis, either `L` distinct external labels fit alongside `B`, or one
external coordinate is omitted by a vertex fiber whose square exceeds `r`. -/
theorem minimalSupportPrivateCommonOmission_capacity_or_largeVertexFiber
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (L r : ℕ) (hcount : L * r < B.card * (B.card - 1)) :
    B.card + L ≤ m ∨
      ∃ z : Fin m, z ∉ B ∧
        r < (minimalSupportPrivateOmissionVertices g hmin z).card *
          (minimalSupportPrivateOmissionVertices g hmin z).card := by
  rcases minimalSupportPrivateCommonOmission_labelImage_or_largeFiber
      g hg hh hmin L r hcount with hlabels | hfiber
  · left
    have hcap := card_minimalSupport_add_commonOmissionLabels_le
      g hg hh hmin
    omega
  · right
    obtain ⟨z, hzLabel, hzFiber⟩ := hfiber
    have hzExternal : z ∉ B := by
      have hdisj := minimalSupportPrivateCommonOmissionLabels_disjoint
        g hg hh hmin
      exact Finset.disjoint_left.mp hdisj hzLabel
    have hpairBound :=
      card_minimalSupportPrivateCommonOmissionFiber_le_square_vertices
        g hg hh hmin z
    exact ⟨z, hzExternal, lt_of_lt_of_le hzFiber hpairBound⟩

end MinModulus
