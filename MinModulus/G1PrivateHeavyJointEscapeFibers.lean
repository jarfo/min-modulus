/-
# Joint heavy-coordinate and coefficient-escape fibers

The protected quarter witness supplies a coefficient-floor escape for every
private witness.  On the abundant heavy-owner family, choose that escape with
one normalization: a self-heavy owner escapes at the owner itself.  Otherwise
the escape is still owner-or-external.

Inside a fiber of witnesses heavy at one common external coordinate, this
gives a second exact image/fiber split.  Many witnesses escape at their own
distinct owners, many external escape labels consume ambient capacity, or
many witnesses share the same ordered `(heavy, escape)` signature.
-/
import MinModulus.G1PrivateHeavyCoordinateFibers

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Select a coefficient-floor escape for a heavy private owner.  When its
chosen heavy coordinate is the owner, use that owner as the escape. -/
noncomputable def minimalSupportPrivateHeavyEscapeCoordinate
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    Fin (m + 1) := by
  classical
  by_cases hself : minimalSupportPrivateHeavyCoordinate g h hmin b = b.val
  · exact b.val.val
  · exact Classical.choose
      (exists_minimalSupportPrivateEscape
        g hg ht hq hmin hqzero b.val)

/-- The selected coordinate is always a genuine escape incidence. -/
theorem minimalSupportPrivateHeavyEscapeCoordinate_mem
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    (b.val, minimalSupportPrivateHeavyEscapeCoordinate
      g hg h t q ht hq hmin hqzero b) ∈
        minimalSupportPrivateEscapePairs g h q hmin := by
  classical
  by_cases hself : minimalSupportPrivateHeavyCoordinate g h hmin b = b.val
  · rw [minimalSupportPrivateHeavyEscapeCoordinate, dif_pos hself]
    apply (mem_minimalSupportPrivateEscapePairs_iff
      g h q hmin b.val b.val).mpr
    have hqb := hqzero b.val b.val.property
    have hb := minimalSupportPrivateHeavyCoordinate_spec g h hmin b
    rw [hself] at hb
    omega
  · rw [minimalSupportPrivateHeavyEscapeCoordinate, dif_neg hself]
    exact Classical.choose_spec
      (exists_minimalSupportPrivateEscape
        g hg ht hq hmin hqzero b.val)

/-- Every selected heavy-owner escape is the owner or lies outside `B`. -/
theorem minimalSupportPrivateHeavyEscapeCoordinate_eq_owner_or_external
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    minimalSupportPrivateHeavyEscapeCoordinate
        g hg h t q ht hq hmin hqzero b = b.val ∨
      minimalSupportPrivateHeavyEscapeCoordinate
        g hg h t q ht hq hmin hqzero b ∉ B :=
  minimalSupportPrivateEscape_eq_self_or_external
    g h q hmin hqzero b.val _
      (minimalSupportPrivateHeavyEscapeCoordinate_mem
        g hg h t q ht hq hmin hqzero b)

/-- Self-heavy normalization: the heavy and escape coordinates both equal
the owner. -/
theorem minimalSupportPrivateHeavyEscapeCoordinate_eq_owner_of_selfHeavy
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (hself : minimalSupportPrivateHeavyCoordinate g h hmin b = b.val) :
    minimalSupportPrivateHeavyEscapeCoordinate
      g hg h t q ht hq hmin hqzero b = b.val := by
  simp [minimalSupportPrivateHeavyEscapeCoordinate, hself]

/-- In the external-heavy fiber at `z`, owners whose selected escape is the
owner itself. -/
noncomputable def minimalSupportPrivateExternalHeavyOwnerEscapeVertices
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z : Fin (m + 1)) :
    Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) := by
  classical
  exact (minimalSupportPrivateExternalHeavyFiber g h hmin z).filter
    (fun b ↦ minimalSupportPrivateHeavyEscapeCoordinate
      g hg h t q ht hq hmin hqzero b = b.val)

/-- In the external-heavy fiber at `z`, owners whose selected escape is also
external to `B`. -/
noncomputable def minimalSupportPrivateDoubleExternalHeavyVertices
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z : Fin (m + 1)) :
    Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) := by
  classical
  exact (minimalSupportPrivateExternalHeavyFiber g h hmin z).filter
    (fun b ↦ minimalSupportPrivateHeavyEscapeCoordinate
      g hg h t q ht hq hmin hqzero b ∉ B)

/-- Owner escapes and external escapes partition every fixed external-heavy
fiber. -/
theorem card_minimalSupportPrivateExternalHeavyOwnerEscape_add_doubleExternal
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z : Fin (m + 1)) :
    (minimalSupportPrivateExternalHeavyOwnerEscapeVertices
      g hg h t q ht hq hmin hqzero z).card +
    (minimalSupportPrivateDoubleExternalHeavyVertices
      g hg h t q ht hq hmin hqzero z).card =
    (minimalSupportPrivateExternalHeavyFiber g h hmin z).card := by
  classical
  let F := minimalSupportPrivateExternalHeavyFiber g h hmin z
  let O := minimalSupportPrivateExternalHeavyOwnerEscapeVertices
    g hg h t q ht hq hmin hqzero z
  let E := minimalSupportPrivateDoubleExternalHeavyVertices
    g hg h t q ht hq hmin hqzero z
  have hdisj : Disjoint O E := by
    rw [Finset.disjoint_left]
    intro b hbO hbE
    have hbO' := Finset.mem_filter.mp hbO
    have hbE' := Finset.mem_filter.mp hbE
    apply hbE'.2
    rw [hbO'.2]
    exact b.val.property
  have hunion : O ∪ E = F := by
    ext b
    constructor
    · intro hb
      rcases Finset.mem_union.mp hb with hbO | hbE
      · exact (Finset.mem_filter.mp hbO).1
      · exact (Finset.mem_filter.mp hbE).1
    · intro hbF
      rcases minimalSupportPrivateHeavyEscapeCoordinate_eq_owner_or_external
          g hg h t q ht hq hmin hqzero b with howner | hexternal
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hbF, howner⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hbF, hexternal⟩)
  change O.card + E.card = F.card
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- External escape labels occurring inside one fixed external-heavy fiber. -/
noncomputable def minimalSupportPrivateExternalHeavyEscapeLabels
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z : Fin (m + 1)) : Finset (Fin (m + 1)) := by
  classical
  exact (minimalSupportPrivateDoubleExternalHeavyVertices
    g hg h t q ht hq hmin hqzero z).image
      (minimalSupportPrivateHeavyEscapeCoordinate
        g hg h t q ht hq hmin hqzero)

/-- The joint fiber with fixed external heavy coordinate `z` and fixed
external escape coordinate `e`. -/
noncomputable def minimalSupportPrivateJointExternalHeavyEscapeFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e : Fin (m + 1)) :
    Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) := by
  classical
  exact (minimalSupportPrivateDoubleExternalHeavyVertices
    g hg h t q ht hq hmin hqzero z).filter
      (fun b ↦ minimalSupportPrivateHeavyEscapeCoordinate
        g hg h t q ht hq hmin hqzero b = e)

/-- External escape labels are disjoint from the deletion set. -/
theorem minimalSupportPrivateExternalHeavyEscapeLabels_disjoint
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z : Fin (m + 1)) :
    Disjoint (minimalSupportPrivateExternalHeavyEscapeLabels
      g hg h t q ht hq hmin hqzero z) B := by
  classical
  rw [Finset.disjoint_left]
  intro e he heB
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
  exact (Finset.mem_filter.mp hb).2 heB

/-- Exact image/fiber count for external escapes inside a fixed external-
heavy fiber. -/
theorem minimalSupportPrivateExternalHeavyEscape_labelImage_or_largeJointFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z : Fin (m + 1)) (L r : ℕ)
    (hcount : L * r < (minimalSupportPrivateDoubleExternalHeavyVertices
      g hg h t q ht hq hmin hqzero z).card) :
    L ≤ (minimalSupportPrivateExternalHeavyEscapeLabels
      g hg h t q ht hq hmin hqzero z).card ∨
      ∃ e ∈ minimalSupportPrivateExternalHeavyEscapeLabels
          g hg h t q ht hq hmin hqzero z,
        r < (minimalSupportPrivateJointExternalHeavyEscapeFiber
          g hg h t q ht hq hmin hqzero z e).card := by
  classical
  let E := minimalSupportPrivateDoubleExternalHeavyVertices
    g hg h t q ht hq hmin hqzero z
  let label : ↥(minimalSupportPrivateTailHeavyVertices g h hmin) →
      Fin (m + 1) := minimalSupportPrivateHeavyEscapeCoordinate
        g hg h t q ht hq hmin hqzero
  let labels := minimalSupportPrivateExternalHeavyEscapeLabels
    g hg h t q ht hq hmin hqzero z
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
    obtain ⟨e, he, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (f := label) hmaps hmul
    refine ⟨e, he, ?_⟩
    simpa [label, E, minimalSupportPrivateJointExternalHeavyEscapeFiber]
      using hfiber

/-- The deletion set and external escape labels fit in the ambient
coordinates. -/
theorem card_minimalSupport_add_externalHeavyEscapeLabels_le
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z : Fin (m + 1)) :
    B.card + (minimalSupportPrivateExternalHeavyEscapeLabels
      g hg h t q ht hq hmin hqzero z).card ≤ m + 1 := by
  classical
  let Z := minimalSupportPrivateExternalHeavyEscapeLabels
    g hg h t q ht hq hmin hqzero z
  have hdisj : Disjoint Z B :=
    minimalSupportPrivateExternalHeavyEscapeLabels_disjoint
      g hg h t q ht hq hmin hqzero z
  rw [← Finset.card_union_of_disjoint hdisj.symm]
  simpa using Finset.card_le_univ (B ∪ Z)

/-- Refine one large external-heavy fiber: many owner escapes, ambient escape-
label capacity, or a large joint `(heavy, escape)` fiber. -/
theorem minimalSupportPrivateExternalHeavyFiber_ownerEscape_or_capacity_or_largeJointFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z : Fin (m + 1)) (A L r : ℕ)
    (hcount : A + L * r <
      (minimalSupportPrivateExternalHeavyFiber g h hmin z).card) :
    A < (minimalSupportPrivateExternalHeavyOwnerEscapeVertices
      g hg h t q ht hq hmin hqzero z).card ∨
      B.card + L ≤ m + 1 ∨
      ∃ e : Fin (m + 1), e ∉ B ∧
        r < (minimalSupportPrivateJointExternalHeavyEscapeFiber
          g hg h t q ht hq hmin hqzero z e).card := by
  have hpartition :=
    card_minimalSupportPrivateExternalHeavyOwnerEscape_add_doubleExternal
      g hg h t q ht hq hmin hqzero z
  by_cases howner : A <
      (minimalSupportPrivateExternalHeavyOwnerEscapeVertices
        g hg h t q ht hq hmin hqzero z).card
  · exact Or.inl howner
  · right
    have hownerLe :
        (minimalSupportPrivateExternalHeavyOwnerEscapeVertices
          g hg h t q ht hq hmin hqzero z).card ≤ A :=
      Nat.le_of_not_gt howner
    have hExternalCount : L * r <
        (minimalSupportPrivateDoubleExternalHeavyVertices
          g hg h t q ht hq hmin hqzero z).card := by
      omega
    rcases
        minimalSupportPrivateExternalHeavyEscape_labelImage_or_largeJointFiber
          g hg h t q ht hq hmin hqzero z L r hExternalCount with
      hlabels | hfiber
    · left
      have hcap := card_minimalSupport_add_externalHeavyEscapeLabels_le
        g hg h t q ht hq hmin hqzero z
      omega
    · right
      obtain ⟨e, heLabel, heFiber⟩ := hfiber
      have heExternal : e ∉ B := by
        have hdisj := minimalSupportPrivateExternalHeavyEscapeLabels_disjoint
          g hg h t q ht hq hmin hqzero z
        exact Finset.disjoint_left.mp hdisj heLabel
      exact ⟨e, heExternal, heFiber⟩

/-- Critical two-stage composition.  The abundant-heavy frontier first
selects a repeated external heavy coordinate; the protected quarter witness
then refines that fiber into many owner escapes, external escape-label
capacity, or a repeated joint `(heavy, escape)` signature. -/
theorem critical_largeCross_or_smallSupport_or_manySelfHeavy_or_capacity_or_jointHeavyEscapeFiber
    {n s q₀ : ℕ} (hq₀ : Odd q₀)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q₀)) (hg : ValidTuple g)
    {t : ZMod (2 ^ (s + 1) * q₀)}
    {qv : Fin (n + 1) → ℤ}
    (ht : t + t =
      ((2 ^ s * q₀ : ℕ) : ZMod (2 ^ (s + 1) * q₀)))
    (hqv : Witness g t qv)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q₀ : ℕ) : ZMod (2 ^ (s + 1) * q₀)) B)
    (hqzero : ∀ a ∈ B, qv a = 0)
    (A L R C D r : ℕ)
    (houter : A + L * R + 1 < B.card)
    (hinner : C + D * r ≤ R) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      B.card ≤ min (s + 1) (Nat.log 2 (n + 1)) - 1 + 1 ∨
      A < (minimalSupportPrivateSelfHeavyVertices g
        ((2 ^ s * q₀ : ℕ) : ZMod (2 ^ (s + 1) * q₀)) hmin).card ∨
      B.card + L ≤ n + 1 ∨
      ∃ z : Fin (n + 1), z ∉ B ∧
        (C < (minimalSupportPrivateExternalHeavyOwnerEscapeVertices
            g hg _ t qv ht hqv hmin hqzero z).card ∨
          B.card + D ≤ n + 1 ∨
          ∃ e : Fin (n + 1), e ∉ B ∧
            r < (minimalSupportPrivateJointExternalHeavyEscapeFiber
              g hg _ t qv ht hqv hmin hqzero z e).card) := by
  rcases
      critical_largeCross_or_smallSupport_or_manySelfHeavy_or_capacity_or_largeExternalHeavyFiber
        hq₀ g hg hmin A L R houter with
    hlarge | hsmall | hself | hcap | hfiber
  · exact Or.inl hlarge
  · exact Or.inr (Or.inl hsmall)
  · exact Or.inr (Or.inr (Or.inl hself))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hcap)))
  · obtain ⟨z, hzExternal, hzFiber⟩ := hfiber
    right; right; right; right
    refine ⟨z, hzExternal, ?_⟩
    have hcount : C + D * r <
        (minimalSupportPrivateExternalHeavyFiber g
          ((2 ^ s * q₀ : ℕ) : ZMod (2 ^ (s + 1) * q₀)) hmin z).card :=
      lt_of_le_of_lt hinner hzFiber
    exact
      minimalSupportPrivateExternalHeavyFiber_ownerEscape_or_capacity_or_largeJointFiber
        g hg _ t qv ht hqv hmin hqzero z C D r hcount

end MinModulus
