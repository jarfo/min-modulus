/-
# Common-omission fibers inside an external coefficient-gap fiber

Fix an external directed coefficient-gap coordinate on a selected family of
private witnesses.  Every ordered pair in that gap fiber also has a common
external omission.  The omission cannot equal the gap coordinate, since both
witnesses have coefficient `-1` at an omission while their coefficients differ
by at least two at the directed gap.

Consequently, many distinct omission labels consume coordinates in addition
to both the deletion set and the fixed gap coordinate.  Otherwise a large
subfiber shares both the directed gap and one common omission.
-/
import MinModulus.G1PrivateHeavyOwnerNormalization

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Forget that an ordered pair was selected from `S`, retaining the ordered
pair of its underlying deletion owners. -/
def minimalSupportSelectedPairToPrivatePair
    {B : Finset (Fin m)} (S : Finset ↥B)
    (p : MinimalSupportSelectedDistinctOrderedPair S) :
    MinimalSupportDistinctOrderedPair B :=
  ⟨(p.val.1.val, p.val.2.val), by
    intro howners
    apply p.property
    exact Subtype.ext howners⟩

/-- Select one external common omission for an ordered pair of selected
private owners. -/
noncomputable def minimalSupportSelectedPrivateCommonOmissionLabel
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (p : MinimalSupportSelectedDistinctOrderedPair S) : Fin m :=
  minimalSupportPrivateCommonOmissionLabel g hg hh hmin
    (minimalSupportSelectedPairToPrivatePair S p)

theorem minimalSupportSelectedPrivateCommonOmissionLabel_spec
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (p : MinimalSupportSelectedDistinctOrderedPair S) :
    minimalSupportSelectedPrivateCommonOmissionLabel
        g hg hh hmin S p ∉ B ∧
      minimalSupportPrivateWitness g h hmin p.val.1.val
          (minimalSupportSelectedPrivateCommonOmissionLabel
            g hg hh hmin S p) = -1 ∧
      minimalSupportPrivateWitness g h hmin p.val.2.val
          (minimalSupportSelectedPrivateCommonOmissionLabel
            g hg hh hmin S p) = -1 :=
  minimalSupportPrivateCommonOmissionLabel_spec g hg hh hmin
    (minimalSupportSelectedPairToPrivatePair S p)

/-- A common omission attached to a pair in the fixed external-gap fiber is
distinct from the gap coordinate. -/
theorem minimalSupportSelectedPrivateCommonOmissionLabel_ne_externalGap
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z : Fin m)
    {p : MinimalSupportSelectedDistinctOrderedPair S}
    (hp : p ∈ minimalSupportSelectedPrivateExternalGapFiber
      g hg h hmin S z) :
    minimalSupportSelectedPrivateCommonOmissionLabel
      g hg hh hmin S p ≠ z := by
  have hpGap := (Finset.mem_filter.mp hp).2
  have hgap :=
    (minimalSupportSelectedPrivateCoefficientGapCoordinate_spec
      g hg h hmin S p).1
  rw [hpGap] at hgap
  have homit := minimalSupportSelectedPrivateCommonOmissionLabel_spec
    g hg hh hmin S p
  intro hwz
  rw [← hwz, homit.2.1, homit.2.2] at hgap
  omega

/-- Common-omission labels used inside one fixed external-gap pair fiber. -/
noncomputable def minimalSupportSelectedPrivateExternalGapOmissionLabels
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z : Fin m) : Finset (Fin m) := by
  classical
  exact (minimalSupportSelectedPrivateExternalGapFiber
    g hg h hmin S z).image
      (minimalSupportSelectedPrivateCommonOmissionLabel
        g hg hh hmin S)

/-- Ordered pairs sharing both the fixed external directed gap `z` and the
fixed common omission `w`. -/
noncomputable def minimalSupportSelectedPrivateExternalGapOmissionFiber
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z w : Fin m) :
    Finset (MinimalSupportSelectedDistinctOrderedPair S) := by
  classical
  exact (minimalSupportSelectedPrivateExternalGapFiber
    g hg h hmin S z).filter (fun p ↦
      minimalSupportSelectedPrivateCommonOmissionLabel
        g hg hh hmin S p = w)

/-- Every pair in a joint `(gap, omission)` fiber retains the directed
coefficient gap and the two omission coefficients. -/
theorem minimalSupportSelectedPrivateExternalGapOmissionFiber_spec
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) {z w : Fin m}
    {p : MinimalSupportSelectedDistinctOrderedPair S}
    (hp : p ∈ minimalSupportSelectedPrivateExternalGapOmissionFiber
      g hg hh hmin S z w) :
    z ∉ B ∧ w ∉ B ∧ w ≠ z ∧
      minimalSupportPrivateWitness g h hmin p.val.1.val z + 2 ≤
        minimalSupportPrivateWitness g h hmin p.val.2.val z ∧
      minimalSupportPrivateWitness g h hmin p.val.1.val w = -1 ∧
      minimalSupportPrivateWitness g h hmin p.val.2.val w = -1 := by
  have hp' := Finset.mem_filter.mp hp
  have hpExternalPair := (Finset.mem_filter.mp hp'.1).1
  have hzExternal := (Finset.mem_filter.mp hpExternalPair).2
  have hpGap := (Finset.mem_filter.mp hp'.1).2
  have hgap :=
    (minimalSupportSelectedPrivateCoefficientGapCoordinate_spec
      g hg h hmin S p)
  have homit := minimalSupportSelectedPrivateCommonOmissionLabel_spec
    g hg hh hmin S p
  have hwz := minimalSupportSelectedPrivateCommonOmissionLabel_ne_externalGap
    g hg hh hmin S z hp'.1
  rw [hpGap] at hzExternal
  rw [hpGap] at hgap
  rw [hp'.2] at homit hwz
  exact ⟨hzExternal, homit.1, hwz, hgap.1, homit.2.1, homit.2.2⟩

/-- Omission labels used inside a fixed external-gap fiber lie outside `B`. -/
theorem minimalSupportSelectedPrivateExternalGapOmissionLabels_disjoint
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z : Fin m) :
    Disjoint (minimalSupportSelectedPrivateExternalGapOmissionLabels
      g hg hh hmin S z) B := by
  classical
  rw [Finset.disjoint_left]
  intro w hw hwB
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
  exact (minimalSupportSelectedPrivateCommonOmissionLabel_spec
    g hg hh hmin S p).1 hwB

/-- The fixed external gap itself is not among its common-omission labels. -/
theorem minimalSupportSelectedPrivateExternalGap_not_mem_omissionLabels
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z : Fin m) :
    z ∉ minimalSupportSelectedPrivateExternalGapOmissionLabels
      g hg hh hmin S z := by
  classical
  intro hz
  obtain ⟨p, hp, hpz⟩ := Finset.mem_image.mp hz
  exact (minimalSupportSelectedPrivateCommonOmissionLabel_ne_externalGap
    g hg hh hmin S z hp) hpz

/-- Exact image/fiber dichotomy for common omissions within one fixed
external directed-gap fiber. -/
theorem minimalSupportSelectedPrivateExternalGapOmission_labelImage_or_largeFiber
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z : Fin m) (L r : ℕ)
    (hcount : L * r < (minimalSupportSelectedPrivateExternalGapFiber
      g hg h hmin S z).card) :
    L ≤ (minimalSupportSelectedPrivateExternalGapOmissionLabels
      g hg hh hmin S z).card ∨
      ∃ w ∈ minimalSupportSelectedPrivateExternalGapOmissionLabels
          g hg hh hmin S z,
        r < (minimalSupportSelectedPrivateExternalGapOmissionFiber
          g hg hh hmin S z w).card := by
  classical
  let E := minimalSupportSelectedPrivateExternalGapFiber
    g hg h hmin S z
  let label : MinimalSupportSelectedDistinctOrderedPair S → Fin m :=
    minimalSupportSelectedPrivateCommonOmissionLabel g hg hh hmin S
  let labels := minimalSupportSelectedPrivateExternalGapOmissionLabels
    g hg hh hmin S z
  by_cases hlarge : L ≤ labels.card
  · exact Or.inl hlarge
  · right
    have hlabelLe : labels.card ≤ L :=
      Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
    have hmul : labels.card * r < E.card :=
      lt_of_le_of_lt (Nat.mul_le_mul_right r hlabelLe) hcount
    have hmaps : ∀ p ∈ E, label p ∈ labels := by
      intro p hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    obtain ⟨w, hw, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (f := label) hmaps hmul
    refine ⟨w, hw, ?_⟩
    simpa [label, E,
      minimalSupportSelectedPrivateExternalGapOmissionFiber] using hfiber

/-- A large external-gap fiber either consumes `L` further external
omission coordinates, in addition to its fixed gap coordinate, or contains
a large subfiber sharing one such omission. -/
theorem minimalSupportSelectedPrivateExternalGapOmission_capacity_or_largeFiber
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (z : Fin m) (L r : ℕ)
    (hcount : L * r < (minimalSupportSelectedPrivateExternalGapFiber
      g hg h hmin S z).card) :
    B.card + 1 + L ≤ m ∨
      ∃ w : Fin m, w ∉ B ∧ w ≠ z ∧
        r < (minimalSupportSelectedPrivateExternalGapOmissionFiber
          g hg hh hmin S z w).card := by
  classical
  let E := minimalSupportSelectedPrivateExternalGapFiber
    g hg h hmin S z
  let labels := minimalSupportSelectedPrivateExternalGapOmissionLabels
    g hg hh hmin S z
  rcases
      minimalSupportSelectedPrivateExternalGapOmission_labelImage_or_largeFiber
        g hg hh hmin S z L r hcount with hlabels | hfiber
  · left
    change L ≤ labels.card at hlabels
    change L * r < E.card at hcount
    have hE : E.Nonempty := Finset.card_pos.mp
      (lt_of_le_of_lt (Nat.zero_le _) hcount)
    obtain ⟨p, hp⟩ := hE
    have hpData := Finset.mem_filter.mp hp
    have hzB :
        minimalSupportSelectedPrivateCoefficientGapCoordinate
          g hg h hmin S p ∉ B :=
      (Finset.mem_filter.mp hpData.1).2
    rw [hpData.2] at hzB
    have hzLabels : z ∉ labels :=
      minimalSupportSelectedPrivateExternalGap_not_mem_omissionLabels
        g hg hh hmin S z
    have hdisj : Disjoint (insert z labels) B := by
      rw [Finset.disjoint_left]
      intro x hx hxB
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hzB hxB
      · exact Finset.disjoint_left.mp
          (minimalSupportSelectedPrivateExternalGapOmissionLabels_disjoint
            g hg hh hmin S z) hx hxB
    have hcap : B.card + (insert z labels).card ≤ m := by
      rw [← Finset.card_union_of_disjoint hdisj.symm]
      simpa using Finset.card_le_univ (B ∪ insert z labels)
    rw [Finset.card_insert_of_notMem hzLabels] at hcap
    omega
  · right
    obtain ⟨w, hwLabel, hwFiber⟩ := hfiber
    have hwB : w ∉ B := by
      exact Finset.disjoint_left.mp
        (minimalSupportSelectedPrivateExternalGapOmissionLabels_disjoint
          g hg hh hmin S z) hwLabel
    have hwz : w ≠ z := by
      intro hwz
      subst w
      exact (minimalSupportSelectedPrivateExternalGap_not_mem_omissionLabels
        g hg hh hmin S z) hwLabel
    exact ⟨w, hwB, hwz, hwFiber⟩

/-- Compose the normalized directed-gap count with the common-omission count
inside its external arm.  The remaining large fiber shares two distinct
external coordinates: a directed gap and a common omission. -/
theorem minimalSupportSelectedPrivate_selfHeavy_or_capacity_or_gapOmissionFiber
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
        r' < (minimalSupportSelectedPrivateExternalGapOmissionFiber
          g hg hh hmin S z w).card := by
  rcases
      minimalSupportSelectedPrivate_selfHeavy_or_capacity_or_largeExternalGapFiber
        g hg h hmin S K L r hcount with hself | hcapacity | hgap
  · exact Or.inl hself
  · exact Or.inr (Or.inl hcapacity)
  · obtain ⟨z, hzB, hzFiber⟩ := hgap
    have hinnerCount : L' * r' <
        (minimalSupportSelectedPrivateExternalGapFiber
          g hg h hmin S z).card := lt_of_le_of_lt hinner hzFiber
    rcases
        minimalSupportSelectedPrivateExternalGapOmission_capacity_or_largeFiber
          g hg hh hmin S z L' r' hinnerCount with hcapacity | hfiber
    · exact Or.inr (Or.inr (Or.inl hcapacity))
    · obtain ⟨w, hwB, hwz, hwFiber⟩ := hfiber
      exact Or.inr (Or.inr (Or.inr
        ⟨z, w, hzB, hwB, hwz, hwFiber⟩))

/-- Every owner in the image of a joint heavy/escape fiber has a canonical
lift back to that fiber. -/
theorem exists_minimalSupportPrivateJointOwnerLift
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e : Fin (m + 1))
    (b : ↥(minimalSupportPrivateJointExternalHeavyEscapeOwners
      g hg h t q ht hq hmin hqzero z e)) :
    ∃ b' : ↥(minimalSupportPrivateJointExternalHeavyEscapeFiber
        g hg h t q ht hq hmin hqzero z e),
      b'.val.val = b.val := by
  classical
  obtain ⟨b', hb', hbval⟩ := Finset.mem_image.mp b.property
  exact ⟨⟨b', hb'⟩, hbval⟩

/-- Choose the unique lift of a selected joint-fiber owner back to its heavy
witness. -/
noncomputable def minimalSupportPrivateJointOwnerLift
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e : Fin (m + 1))
    (b : ↥(minimalSupportPrivateJointExternalHeavyEscapeOwners
      g hg h t q ht hq hmin hqzero z e)) :
    ↥(minimalSupportPrivateJointExternalHeavyEscapeFiber
      g hg h t q ht hq hmin hqzero z e) :=
  Classical.choose (exists_minimalSupportPrivateJointOwnerLift
    g hg h t q ht hq hmin hqzero z e b)

@[simp] theorem minimalSupportPrivateJointOwnerLift_val
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e : Fin (m + 1))
    (b : ↥(minimalSupportPrivateJointExternalHeavyEscapeOwners
      g hg h t q ht hq hmin hqzero z e)) :
    (minimalSupportPrivateJointOwnerLift
      g hg h t q ht hq hmin hqzero z e b).val.val = b.val :=
  Classical.choose_spec (exists_minimalSupportPrivateJointOwnerLift
    g hg h t q ht hq hmin hqzero z e b)

/-- A selected `(gap, omission)` pair over joint-fiber owners lifts to two
distinct members of the original joint heavy/escape fiber.  Thus passing to
the owner image has not discarded the fixed heavy and escape signature. -/
theorem minimalSupportPrivateJointExternalGapOmissionFiber_lifts
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1))
    {p : MinimalSupportSelectedDistinctOrderedPair
      (minimalSupportPrivateJointExternalHeavyEscapeOwners
        g hg h t q ht hq hmin hqzero z e)}
    (hp : p ∈ minimalSupportSelectedPrivateExternalGapOmissionFiber
      g hg hh hmin
        (minimalSupportPrivateJointExternalHeavyEscapeOwners
          g hg h t q ht hq hmin hqzero z e) delta w) :
    ∃ b u : ↥(minimalSupportPrivateTailHeavyVertices g h hmin),
      b ∈ minimalSupportPrivateJointExternalHeavyEscapeFiber
          g hg h t q ht hq hmin hqzero z e ∧
      u ∈ minimalSupportPrivateJointExternalHeavyEscapeFiber
          g hg h t q ht hq hmin hqzero z e ∧
      b.val = p.val.1.val ∧ u.val = p.val.2.val ∧ b ≠ u ∧
      delta ∉ B ∧ w ∉ B ∧ w ≠ delta ∧
      minimalSupportPrivateWitness g h hmin b.val delta + 2 ≤
        minimalSupportPrivateWitness g h hmin u.val delta ∧
      minimalSupportPrivateWitness g h hmin b.val w = -1 ∧
      minimalSupportPrivateWitness g h hmin u.val w = -1 := by
  let b' := minimalSupportPrivateJointOwnerLift
    g hg h t q ht hq hmin hqzero z e p.val.1
  let u' := minimalSupportPrivateJointOwnerLift
    g hg h t q ht hq hmin hqzero z e p.val.2
  have hbval : b'.val.val = p.val.1.val := by simp [b']
  have huval : u'.val.val = p.val.2.val := by simp [u']
  have hbu : b'.val ≠ u'.val := by
    intro hsame
    apply p.property
    apply Subtype.ext
    rw [← hbval, ← huval, hsame]
  have hpSpec :=
    minimalSupportSelectedPrivateExternalGapOmissionFiber_spec
      g hg hh hmin
        (minimalSupportPrivateJointExternalHeavyEscapeOwners
          g hg h t q ht hq hmin hqzero z e) hp
  refine ⟨b'.val, u'.val, b'.property, u'.property, hbval, huval, hbu,
    hpSpec.1, hpSpec.2.1, hpSpec.2.2.1, ?_, ?_, ?_⟩
  · simpa [hbval, huval] using hpSpec.2.2.2.1
  · simpa [hbval] using hpSpec.2.2.2.2.1
  · simpa [huval] using hpSpec.2.2.2.2.2

/-- The extra-coordinate capacity/large omission-fiber dichotomy specialized
to one joint heavy/escape fiber and one external directed-gap fiber inside
it. -/
theorem minimalSupportPrivateJointExternalGapOmission_capacity_or_largeFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta : Fin (m + 1)) (L r : ℕ)
    (hcount : let S := (minimalSupportPrivateJointExternalHeavyEscapeOwners
        g hg h t q ht hq hmin hqzero z e)
      L * r < (minimalSupportSelectedPrivateExternalGapFiber
        g hg h hmin S delta).card) :
    B.card + 1 + L ≤ m + 1 ∨
      let S := (minimalSupportPrivateJointExternalHeavyEscapeOwners
        g hg h t q ht hq hmin hqzero z e)
      ∃ w : Fin (m + 1), w ∉ B ∧ w ≠ delta ∧
        r < (minimalSupportSelectedPrivateExternalGapOmissionFiber
          g hg hh hmin S delta w).card := by
  let S := minimalSupportPrivateJointExternalHeavyEscapeOwners
    g hg h t q ht hq hmin hqzero z e
  exact
    minimalSupportSelectedPrivateExternalGapOmission_capacity_or_largeFiber
      g hg hh hmin S delta L r hcount

end MinModulus
