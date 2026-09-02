/-
# Degree-sensitive rooted common-omission stars

The complete ordered-pair labeling of private transversal witnesses can be
made quantitative from one chosen root.  If the root witness has `q`
omissions, every other selected owner is assigned to one of those same `q`
coordinates.  Consequently a large owner family forces a large common-
omission star through the root.

Unlike the higher-degree recurrence, this count does not sum over all free
coordinates and does not remember an ordered history of fresh labels.  It is
the first bridge between exact omission degree and the cross-owner pair
geometry.
-/
import MinModulus.G1PrivateHeavySelfHeavyHigherDegreeClosure

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- For a fixed root `b`, choose the already constructed common-omission
label on the ordered pair from `b` to another owner in `S`. -/
noncomputable def minimalSupportPrivateCommonOmissionRowLabel
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (b : ↥B) (u : ↥(S.erase b)) : Fin (m + 1) :=
  minimalSupportPrivateCommonOmissionLabel g hg hh hmin
    ⟨(b, u.val), (Finset.mem_erase.mp u.property).1.symm⟩

/-- A row label is external and is omitted by both the root and the labelled
owner. -/
theorem minimalSupportPrivateCommonOmissionRowLabel_spec
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (b : ↥B) (u : ↥(S.erase b)) :
    let z := minimalSupportPrivateCommonOmissionRowLabel
      g hg hh hmin S b u
    z ∉ B ∧
      minimalSupportPrivateWitness g h hmin b z = -1 ∧
      minimalSupportPrivateWitness g h hmin u.val z = -1 := by
  dsimp
  exact minimalSupportPrivateCommonOmissionLabel_spec g hg hh hmin
    ⟨(b, u.val), (Finset.mem_erase.mp u.property).1.symm⟩

/-- External labels realized in the row rooted at `b`. -/
noncomputable def minimalSupportPrivateCommonOmissionRowLabels
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (b : ↥B) : Finset (Fin (m + 1)) := by
  classical
  exact Finset.univ.image
    (minimalSupportPrivateCommonOmissionRowLabel g hg hh hmin S b)

@[simp] theorem mem_minimalSupportPrivateCommonOmissionRowLabels_iff
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (b : ↥B) (z : Fin (m + 1)) :
    z ∈ minimalSupportPrivateCommonOmissionRowLabels
        g hg hh hmin S b ↔
      ∃ u : ↥(S.erase b),
        minimalSupportPrivateCommonOmissionRowLabel
          g hg hh hmin S b u = z := by
  classical
  simp [minimalSupportPrivateCommonOmissionRowLabels]

/-- Every label in a rooted row belongs to the root's complete omission
set. -/
theorem minimalSupportPrivateCommonOmissionRowLabels_subset_rootOmissions
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (b : ↥B) :
    minimalSupportPrivateCommonOmissionRowLabels g hg hh hmin S b ⊆
      witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b) := by
  intro z hz
  obtain ⟨u, rfl⟩ :=
    (mem_minimalSupportPrivateCommonOmissionRowLabels_iff
      g hg hh hmin S b z).mp hz
  exact (witnessOmissionCoordinates_exact _ _).mp
    (minimalSupportPrivateCommonOmissionRowLabel_spec
      g hg hh hmin S b u).2.1

/-- Hence the number of labels used in one row is at most the omission
degree of its root. -/
theorem card_minimalSupportPrivateCommonOmissionRowLabels_le_rootDegree
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (b : ↥B) :
    (minimalSupportPrivateCommonOmissionRowLabels
        g hg hh hmin S b).card ≤
      (witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b)).card :=
  Finset.card_le_card
    (minimalSupportPrivateCommonOmissionRowLabels_subset_rootOmissions
      g hg hh hmin S b)

/-- The fiber of other selected owners receiving one fixed row label. -/
noncomputable def minimalSupportPrivateCommonOmissionRowFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (b : ↥B) (z : Fin (m + 1)) :
    Finset ↥(S.erase b) := by
  classical
  exact Finset.univ.filter (fun u ↦
    minimalSupportPrivateCommonOmissionRowLabel
      g hg hh hmin S b u = z)

@[simp] theorem mem_minimalSupportPrivateCommonOmissionRowFiber_iff
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (b : ↥B) (z : Fin (m + 1))
    (u : ↥(S.erase b)) :
    u ∈ minimalSupportPrivateCommonOmissionRowFiber
        g hg hh hmin S b z ↔
      minimalSupportPrivateCommonOmissionRowLabel
        g hg hh hmin S b u = z := by
  classical
  simp [minimalSupportPrivateCommonOmissionRowFiber]

/-- The row fibers form an exact partition of all selected owners other than
the root. -/
theorem card_erase_eq_sum_minimalSupportPrivateCommonOmissionRowFibers
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (b : ↥B) :
    (S.erase b).card =
      ∑ z ∈ minimalSupportPrivateCommonOmissionRowLabels
          g hg hh hmin S b,
        (minimalSupportPrivateCommonOmissionRowFiber
          g hg hh hmin S b z).card := by
  classical
  let E := S.erase b
  let label := minimalSupportPrivateCommonOmissionRowLabel
    g hg hh hmin S b
  calc
    E.card = (Finset.univ : Finset ↥E).card := by simp
    _ = ∑ z ∈ (Finset.univ : Finset ↥E).image label,
          ((Finset.univ : Finset ↥E).filter (fun u ↦ label u = z)).card :=
      Finset.card_eq_sum_card_image label Finset.univ
    _ = ∑ z ∈ minimalSupportPrivateCommonOmissionRowLabels
            g hg hh hmin S b,
          (minimalSupportPrivateCommonOmissionRowFiber
            g hg hh hmin S b z).card := by
      rfl

/-- Selected owners (including the root when applicable) whose canonical
private witness omits `z`. -/
noncomputable def minimalSupportPrivateCommonOmissionStarOwners
    (g : Fin (m + 1) → G) {h : G}
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z : Fin (m + 1)) : Finset ↥B := by
  classical
  exact S.filter (fun u ↦
    minimalSupportPrivateWitness g h hmin u z = -1)

@[simp] theorem mem_minimalSupportPrivateCommonOmissionStarOwners_iff
    (g : Fin (m + 1) → G) {h : G}
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z : Fin (m + 1)) (u : ↥B) :
    u ∈ minimalSupportPrivateCommonOmissionStarOwners g hmin S z ↔
      u ∈ S ∧ minimalSupportPrivateWitness g h hmin u z = -1 := by
  classical
  simp [minimalSupportPrivateCommonOmissionStarOwners]

/-- A nonempty row-label fiber, together with its root, injects into the
corresponding common-omission star. -/
theorem card_minimalSupportPrivateCommonOmissionRowFiber_add_one_le_star
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (b : ↥B) (hb : b ∈ S)
    {z : Fin (m + 1)}
    (hz : z ∈ minimalSupportPrivateCommonOmissionRowLabels
      g hg hh hmin S b) :
    (minimalSupportPrivateCommonOmissionRowFiber
        g hg hh hmin S b z).card + 1 ≤
      (minimalSupportPrivateCommonOmissionStarOwners
        g hmin S z).card := by
  classical
  let F := minimalSupportPrivateCommonOmissionRowFiber
    g hg hh hmin S b z
  let V := minimalSupportPrivateCommonOmissionStarOwners g hmin S z
  obtain ⟨u₀, hu₀⟩ :=
    (mem_minimalSupportPrivateCommonOmissionRowLabels_iff
      g hg hh hmin S b z).mp hz
  have hbO : minimalSupportPrivateWitness g h hmin b z = -1 := by
    rw [← hu₀]
    exact (minimalSupportPrivateCommonOmissionRowLabel_spec
      g hg hh hmin S b u₀).2.1
  let enc : Option ↥F → ↥V := fun u ↦ by
    cases u with
    | none =>
        exact ⟨b,
          (mem_minimalSupportPrivateCommonOmissionStarOwners_iff
            g hmin S z b).mpr ⟨hb, hbO⟩⟩
    | some u =>
        have hulabel :=
          (mem_minimalSupportPrivateCommonOmissionRowFiber_iff
            g hg hh hmin S b z u.val).mp u.property
        have huspec := minimalSupportPrivateCommonOmissionRowLabel_spec
          g hg hh hmin S b u.val
        have huS : u.val.val ∈ S :=
          (Finset.mem_erase.mp u.val.property).2
        exact ⟨u.val.val,
          (mem_minimalSupportPrivateCommonOmissionStarOwners_iff
            g hmin S z u.val.val).mpr
              ⟨huS, by simpa [hulabel] using huspec.2.2⟩⟩
  have henc : Function.Injective enc := by
    intro u v huv
    cases u with
    | none =>
        cases v with
        | none => rfl
        | some v =>
            exfalso
            have hvne : v.val.val ≠ b :=
              (Finset.mem_erase.mp v.val.property).1
            exact hvne (congrArg Subtype.val huv).symm
    | some u =>
        cases v with
        | none =>
            exfalso
            have hune : u.val.val ≠ b :=
              (Finset.mem_erase.mp u.val.property).1
            exact hune (congrArg Subtype.val huv)
        | some v =>
            congr
            apply Subtype.ext
            apply Subtype.ext
            simpa [enc] using congrArg (fun x : ↥V ↦ x.val) huv
  have hcard := Fintype.card_le_of_injective enc henc
  change F.card + 1 ≤ V.card
  simpa using hcard

/-- Degree-sensitive rooted pigeonhole theorem.  If `q*r` is smaller than
the number of selected owners other than the root, some external omission
is shared by the root and more than `r` of those owners; hence its full star
has more than `r+1` vertices. -/
theorem minimalSupportPrivateCommonOmission_rootDegree_largeStar
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (b : ↥B) (hb : b ∈ S)
    (q r : ℕ)
    (hdegree : (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b)).card ≤ q)
    (hcount : q * r < (S.erase b).card) :
    ∃ z : Fin (m + 1), z ∉ B ∧
      minimalSupportPrivateWitness g h hmin b z = -1 ∧
      r + 1 < (minimalSupportPrivateCommonOmissionStarOwners
        g hmin S z).card := by
  classical
  let E := S.erase b
  let label := minimalSupportPrivateCommonOmissionRowLabel
    g hg hh hmin S b
  let labels := minimalSupportPrivateCommonOmissionRowLabels
    g hg hh hmin S b
  have hlabelsDegree : labels.card ≤ q :=
    (card_minimalSupportPrivateCommonOmissionRowLabels_le_rootDegree
      g hg hh hmin S b).trans hdegree
  have hmul : labels.card * r < (Finset.univ : Finset ↥E).card := by
    simpa [E] using
      lt_of_le_of_lt (Nat.mul_le_mul_right r hlabelsDegree) hcount
  have hmaps : ∀ u ∈ (Finset.univ : Finset ↥E), label u ∈ labels := by
    intro u _hu
    simp [label, labels, minimalSupportPrivateCommonOmissionRowLabels]
  obtain ⟨z, hzLabels, hzFiber⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (f := label) hmaps hmul
  have hzRow : z ∈ minimalSupportPrivateCommonOmissionRowLabels
      g hg hh hmin S b := by
    simpa [labels] using hzLabels
  obtain ⟨u, huLabel⟩ :=
    (mem_minimalSupportPrivateCommonOmissionRowLabels_iff
      g hg hh hmin S b z).mp hzRow
  have hspec := minimalSupportPrivateCommonOmissionRowLabel_spec
    g hg hh hmin S b u
  have hrowCard : r <
      (minimalSupportPrivateCommonOmissionRowFiber
        g hg hh hmin S b z).card := by
    simpa [label, E, minimalSupportPrivateCommonOmissionRowFiber] using hzFiber
  have hstar :=
    card_minimalSupportPrivateCommonOmissionRowFiber_add_one_le_star
      g hg hh hmin S b hb hzRow
  have hzExternal : z ∉ B := by
    rw [← huLabel]
    exact hspec.1
  have hbOmit : minimalSupportPrivateWitness g h hmin b z = -1 := by
    rw [← huLabel]
    exact hspec.2.1
  exact ⟨z, hzExternal, hbOmit, by omega⟩

/-- Cardinality form using the exact size of `S`: two units beyond `q*r`
are enough because the root itself is removed before the row count. -/
theorem minimalSupportPrivateCommonOmission_rootDegree_largeStar_of_card
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (b : ↥B) (hb : b ∈ S)
    (q r : ℕ)
    (hdegree : (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b)).card ≤ q)
    (hcount : q * r + 2 ≤ S.card) :
    ∃ z : Fin (m + 1), z ∉ B ∧
      minimalSupportPrivateWitness g h hmin b z = -1 ∧
      r + 1 < (minimalSupportPrivateCommonOmissionStarOwners
        g hmin S z).card := by
  apply minimalSupportPrivateCommonOmission_rootDegree_largeStar
    g hg hh hmin S b hb q r hdegree
  rw [Finset.card_erase_of_mem hb]
  omega

/-- Exact-degree specialization on the whole transversal.  It lands in the
existing private-omission vertex fiber API, so the large star can immediately
enter the established light/heavy and crossing alternatives. -/
theorem minimalSupportPrivateCommonOmission_exactRoot_largeVertexFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (q r : ℕ)
    (hdegree : (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b)).card = q)
    (hcount : q * r + 2 ≤ B.card) :
    ∃ z : Fin (m + 1), z ∉ B ∧
      minimalSupportPrivateWitness g h hmin b z = -1 ∧
      r + 1 < (minimalSupportPrivateOmissionVertices g hmin z).card := by
  obtain ⟨z, hzB, hbz, hzStar⟩ :=
    minimalSupportPrivateCommonOmission_rootDegree_largeStar_of_card
      g hg hh hmin (Finset.univ : Finset ↥B) b (by simp) q r
        hdegree.le (by simpa using hcount)
  exact ⟨z, hzB, hbz, by
    simpa [minimalSupportPrivateCommonOmissionStarOwners,
      minimalSupportPrivateOmissionVertices] using hzStar⟩

end MinModulus
