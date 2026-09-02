/-
# Coordinate fibers of abundant private-heavy owners

For every tail-heavy private owner, choose one tail coordinate with
coefficient at least two.  Privacy forces that coordinate either to be the
owner itself or to lie outside the minimal transversal.  The heavy owners
therefore split into self-heavy owners and externally labelled owners.

Exact image/fiber counting on the external labels gives three currencies:
many self-heavy owners, ambient coordinate capacity, or many distinct private
witnesses heavy at one common external coordinate.  Combining this with the
all-but-one-heavy theorem inserts the trichotomy directly into the critical
G1 frontier.
-/
import MinModulus.G1PrivateHeavySelectedLightCharge

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Choose a tail coordinate of coefficient at least two for each heavy
private owner.  When the owner is non-anchor and already has coefficient at
least two, prioritize the owner itself. -/
noncomputable def minimalSupportPrivateHeavyTailIndex
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) : Fin m := by
  classical
  if howner : b.val.val ≠ 0 ∧
      2 ≤ minimalSupportPrivateWitness g h hmin b.val b.val then
    exact Classical.choose (Fin.exists_succ_eq_of_ne_zero howner.1)
  else
    exact Classical.choose
      ((mem_minimalSupportPrivateTailHeavyVertices_iff
        g h hmin b.val).mp b.property)

theorem minimalSupportPrivateHeavyTailIndex_spec
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    2 ≤ minimalSupportPrivateWitness g h hmin b.val
      (minimalSupportPrivateHeavyTailIndex g h hmin b).succ := by
  classical
  unfold minimalSupportPrivateHeavyTailIndex
  split
  next howner =>
    rw [Classical.choose_spec (Fin.exists_succ_eq_of_ne_zero howner.1)]
    exact howner.2
  next =>
    exact Classical.choose_spec
      ((mem_minimalSupportPrivateTailHeavyVertices_iff
        g h hmin b.val).mp b.property)

/-- The selected full heavy coordinate. -/
noncomputable def minimalSupportPrivateHeavyCoordinate
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    Fin (m + 1) :=
  (minimalSupportPrivateHeavyTailIndex g h hmin b).succ

theorem minimalSupportPrivateHeavyCoordinate_spec
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    2 ≤ minimalSupportPrivateWitness g h hmin b.val
      (minimalSupportPrivateHeavyCoordinate g h hmin b) :=
  minimalSupportPrivateHeavyTailIndex_spec g h hmin b

/-- A non-anchor owner-heavy private witness is normalized so that its
selected heavy coordinate is exactly its owner. -/
theorem minimalSupportPrivateHeavyCoordinate_eq_owner_of_nonzero_ownerHeavy
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (hb0 : b.val.val ≠ 0)
    (hb : 2 ≤ minimalSupportPrivateWitness g h hmin b.val b.val) :
    minimalSupportPrivateHeavyCoordinate g h hmin b = b.val := by
  classical
  unfold minimalSupportPrivateHeavyCoordinate
  unfold minimalSupportPrivateHeavyTailIndex
  have howner : b.val.val ≠ 0 ∧
      2 ≤ minimalSupportPrivateWitness g h hmin b.val b.val := ⟨hb0, hb⟩
  simp only [dif_pos howner]
  exact Classical.choose_spec (Fin.exists_succ_eq_of_ne_zero hb0)

/-- Privacy localizes the selected heavy coordinate to its owner or outside
the deletion set. -/
theorem minimalSupportPrivateHeavyCoordinate_eq_owner_or_external
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    minimalSupportPrivateHeavyCoordinate g h hmin b = b.val ∨
      minimalSupportPrivateHeavyCoordinate g h hmin b ∉ B := by
  apply privateHeavyCoordinate_eq_owner_or_external b.val
    (minimalSupportPrivateWitness g h hmin b.val)
  · intro a haB hne
    exact minimalSupportPrivateWitness_eq_zero_of_ne
      g h hmin b.val haB hne
  · exact minimalSupportPrivateHeavyCoordinate_spec g h hmin b

/-- Heavy owners whose selected heavy coordinate is the owner itself. -/
noncomputable def minimalSupportPrivateSelfHeavyVertices
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) := by
  classical
  exact Finset.univ.filter (fun b ↦
    minimalSupportPrivateHeavyCoordinate g h hmin b = b.val)

@[simp] theorem mem_minimalSupportPrivateSelfHeavyVertices_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin ↔
      minimalSupportPrivateHeavyCoordinate g h hmin b = b.val := by
  classical
  simp [minimalSupportPrivateSelfHeavyVertices]

/-- Heavy owners whose selected heavy coordinate is external to `B`. -/
noncomputable def minimalSupportPrivateExternalHeavyVertices
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) := by
  classical
  exact Finset.univ.filter (fun b ↦
    minimalSupportPrivateHeavyCoordinate g h hmin b ∉ B)

@[simp] theorem mem_minimalSupportPrivateExternalHeavyVertices_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    b ∈ minimalSupportPrivateExternalHeavyVertices g h hmin ↔
      minimalSupportPrivateHeavyCoordinate g h hmin b ∉ B := by
  classical
  simp [minimalSupportPrivateExternalHeavyVertices]

/-- Self-heavy and externally heavy owners partition the heavy owners. -/
theorem card_minimalSupportPrivateSelfHeavy_add_externalHeavyVertices
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    (minimalSupportPrivateSelfHeavyVertices g h hmin).card +
      (minimalSupportPrivateExternalHeavyVertices g h hmin).card =
        (minimalSupportPrivateTailHeavyVertices g h hmin).card := by
  classical
  let S := minimalSupportPrivateSelfHeavyVertices g h hmin
  let E := minimalSupportPrivateExternalHeavyVertices g h hmin
  have hdisj : Disjoint S E := by
    rw [Finset.disjoint_left]
    intro b hbS hbE
    have hself :=
      (mem_minimalSupportPrivateSelfHeavyVertices_iff g h hmin b).mp hbS
    have hext :=
      (mem_minimalSupportPrivateExternalHeavyVertices_iff g h hmin b).mp hbE
    apply hext
    rw [hself]
    exact b.val.property
  have hunion : S ∪ E = Finset.univ := by
    ext b
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rcases minimalSupportPrivateHeavyCoordinate_eq_owner_or_external
      g h hmin b with hself | hext
    · exact Or.inl
        ((mem_minimalSupportPrivateSelfHeavyVertices_iff
          g h hmin b).mpr hself)
    · exact Or.inr
        ((mem_minimalSupportPrivateExternalHeavyVertices_iff
          g h hmin b).mpr hext)
  change S.card + E.card =
    (minimalSupportPrivateTailHeavyVertices g h hmin).card
  rw [← Finset.card_union_of_disjoint hdisj, hunion]
  simp

/-- External coordinates selected by externally heavy private owners. -/
noncomputable def minimalSupportPrivateExternalHeavyLabels
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) : Finset (Fin (m + 1)) := by
  classical
  exact (minimalSupportPrivateExternalHeavyVertices g h hmin).image
    (minimalSupportPrivateHeavyCoordinate g h hmin)

@[simp] theorem mem_minimalSupportPrivateExternalHeavyLabels_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) (z : Fin (m + 1)) :
    z ∈ minimalSupportPrivateExternalHeavyLabels g h hmin ↔
      ∃ b ∈ minimalSupportPrivateExternalHeavyVertices g h hmin,
        minimalSupportPrivateHeavyCoordinate g h hmin b = z := by
  classical
  simp [minimalSupportPrivateExternalHeavyLabels]

/-- Every selected external heavy label lies outside `B`. -/
theorem minimalSupportPrivateExternalHeavyLabels_disjoint
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Disjoint (minimalSupportPrivateExternalHeavyLabels g h hmin) B := by
  classical
  rw [Finset.disjoint_left]
  intro z hz hzB
  obtain ⟨b, hbE, rfl⟩ :=
    (mem_minimalSupportPrivateExternalHeavyLabels_iff
      g h hmin z).mp hz
  exact ((mem_minimalSupportPrivateExternalHeavyVertices_iff
    g h hmin b).mp hbE) hzB

/-- Externally heavy owners carrying one selected label `z`. -/
noncomputable def minimalSupportPrivateExternalHeavyFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1)) :
    Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) := by
  classical
  exact (minimalSupportPrivateExternalHeavyVertices g h hmin).filter
    (fun b ↦ minimalSupportPrivateHeavyCoordinate g h hmin b = z)

@[simp] theorem mem_minimalSupportPrivateExternalHeavyFiber_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    b ∈ minimalSupportPrivateExternalHeavyFiber g h hmin z ↔
      b ∈ minimalSupportPrivateExternalHeavyVertices g h hmin ∧
        minimalSupportPrivateHeavyCoordinate g h hmin b = z := by
  classical
  simp [minimalSupportPrivateExternalHeavyFiber]

/-- Exact external-label pigeonhole theorem for heavy owners. -/
theorem minimalSupportPrivateExternalHeavy_labelImage_or_largeFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (L r : ℕ)
    (hcount : L * r <
      (minimalSupportPrivateExternalHeavyVertices g h hmin).card) :
    L ≤ (minimalSupportPrivateExternalHeavyLabels g h hmin).card ∨
      ∃ z ∈ minimalSupportPrivateExternalHeavyLabels g h hmin,
        r < (minimalSupportPrivateExternalHeavyFiber
          g h hmin z).card := by
  classical
  let E := minimalSupportPrivateExternalHeavyVertices g h hmin
  let label : ↥(minimalSupportPrivateTailHeavyVertices g h hmin) →
      Fin (m + 1) := minimalSupportPrivateHeavyCoordinate g h hmin
  let labels := minimalSupportPrivateExternalHeavyLabels g h hmin
  by_cases hlarge : L ≤ labels.card
  · exact Or.inl hlarge
  · right
    have hlabelLe : labels.card ≤ L :=
      Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
    have hmul : labels.card * r < E.card :=
      lt_of_le_of_lt (Nat.mul_le_mul_right r hlabelLe) hcount
    have hmaps : ∀ b ∈ E, label b ∈ labels := by
      intro b hb
      exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
    obtain ⟨z, hz, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (f := label) hmaps hmul
    refine ⟨z, hz, ?_⟩
    simpa [label, E, minimalSupportPrivateExternalHeavyFiber] using hfiber

/-- `B` and the external heavy labels fit in the ambient coordinate set. -/
theorem card_minimalSupport_add_externalHeavyLabels_le
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    B.card + (minimalSupportPrivateExternalHeavyLabels g h hmin).card ≤
      m + 1 := by
  classical
  let Z := minimalSupportPrivateExternalHeavyLabels g h hmin
  have hdisj : Disjoint Z B :=
    minimalSupportPrivateExternalHeavyLabels_disjoint g h hmin
  rw [← Finset.card_union_of_disjoint hdisj.symm]
  simpa using Finset.card_le_univ (B ∪ Z)

/-- Exact three-way count for all heavy owners: many are self-heavy, many
external labels consume ambient capacity, or one external coordinate is
heavy in many distinct private witnesses. -/
theorem minimalSupportPrivateHeavy_self_or_capacity_or_largeExternalFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (A L r : ℕ)
    (hcount : A + L * r <
      (minimalSupportPrivateTailHeavyVertices g h hmin).card) :
    A < (minimalSupportPrivateSelfHeavyVertices g h hmin).card ∨
      B.card + L ≤ m + 1 ∨
      ∃ z : Fin (m + 1), z ∉ B ∧
        r < (minimalSupportPrivateExternalHeavyFiber
          g h hmin z).card := by
  have hpartition :=
    card_minimalSupportPrivateSelfHeavy_add_externalHeavyVertices
      g h hmin
  by_cases hself : A <
      (minimalSupportPrivateSelfHeavyVertices g h hmin).card
  · exact Or.inl hself
  · right
    have hselfLe :
        (minimalSupportPrivateSelfHeavyVertices g h hmin).card ≤ A :=
      Nat.le_of_not_gt hself
    have hExternalCount : L * r <
        (minimalSupportPrivateExternalHeavyVertices g h hmin).card := by
      omega
    rcases minimalSupportPrivateExternalHeavy_labelImage_or_largeFiber
        g h hmin L r hExternalCount with hlabels | hfiber
    · left
      have hcap := card_minimalSupport_add_externalHeavyLabels_le g h hmin
      omega
    · right
      obtain ⟨z, hzLabel, hzFiber⟩ := hfiber
      have hzExternal : z ∉ B := by
        have hdisj :=
          minimalSupportPrivateExternalHeavyLabels_disjoint g h hmin
        exact Finset.disjoint_left.mp hdisj hzLabel
      exact ⟨z, hzExternal, hzFiber⟩

/-- Critical composition: crossing, a small transversal, many self-heavy
owners, ambient external-label capacity, or a repeated external heavy
coordinate. -/
theorem critical_largeCross_or_smallSupport_or_manySelfHeavy_or_capacity_or_largeExternalHeavyFiber
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (A L r : ℕ) (hcount : A + L * r + 1 < B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      B.card ≤ min (s + 1) (Nat.log 2 (n + 1)) - 1 + 1 ∨
      A < (minimalSupportPrivateSelfHeavyVertices g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin).card ∨
      B.card + L ≤ n + 1 ∨
      ∃ z : Fin (n + 1), z ∉ B ∧
        r < (minimalSupportPrivateExternalHeavyFiber g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin z).card := by
  rcases
      critical_largeCross_or_minimalSupport_card_le_depth_add_one_or_allButOneHeavy
        hq g hg hmin with hlarge | hsmall | hheavy
  · exact Or.inl hlarge
  · exact Or.inr (Or.inl hsmall)
  · right; right
    have hheavyCount : A + L * r <
        (minimalSupportPrivateTailHeavyVertices g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin).card := by
      omega
    exact minimalSupportPrivateHeavy_self_or_capacity_or_largeExternalFiber
      g _ hmin A L r hheavyCount

end MinModulus
