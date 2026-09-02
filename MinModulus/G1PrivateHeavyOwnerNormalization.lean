/-
# Normalizing owner-heavy private witnesses

The directed coefficient-gap count can return many selected owners whose
private witness is heavy at the owner itself.  Except for the distinguished
anchor coordinate, every such owner is automatically tail-heavy.  The heavy
coordinate selector can therefore be normalized to the owner, and the
protected coefficient-floor escape is then the owner as well.

This gives an injection from non-anchor selected owner-heavy witnesses into
the global self-heavy family.  Quantitatively, the selected owner-heavy family
has cardinality at most `self-heavy + 1`, with the single loss accounting for
the anchor.  Consequently the owner-heavy alternative in the directed-gap
count is upgraded to a normalized self-heavy alternative.
-/
import MinModulus.G1PrivateHeavyCoefficientGapFibers

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- A non-anchor selected owner-heavy witness belongs to the global
tail-heavy private family. -/
theorem minimalSupportSelectedPrivateOwnerHeavy_mem_tailHeavy_of_ne_zero
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    {b : ↥S}
    (hb : b ∈ minimalSupportSelectedPrivateOwnerHeavyVertices
      g h hmin S)
    (hb0 : b.val.val ≠ 0) :
    b.val ∈ minimalSupportPrivateTailHeavyVertices g h hmin := by
  apply (mem_minimalSupportPrivateTailHeavyVertices_iff
    g h hmin b.val).mpr
  obtain ⟨k, hk⟩ := Fin.exists_succ_eq_of_ne_zero hb0
  refine ⟨k, ?_⟩
  rw [hk]
  exact (Finset.mem_filter.mp hb).2

/-- Embed a non-anchor selected owner-heavy witness into the global
self-heavy family. -/
noncomputable def minimalSupportSelectedPrivateOwnerHeavyToSelfHeavy
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (b : ↥(minimalSupportSelectedPrivateOwnerHeavyVertices
      g h hmin S))
    (hb0 : b.val.val.val ≠ 0) :
    ↥(minimalSupportPrivateSelfHeavyVertices g h hmin) := by
  let hbHeavy : ↥(minimalSupportPrivateTailHeavyVertices g h hmin) :=
    ⟨b.val.val,
      minimalSupportSelectedPrivateOwnerHeavy_mem_tailHeavy_of_ne_zero
        g h hmin S b.property hb0⟩
  refine ⟨hbHeavy, ?_⟩
  apply (mem_minimalSupportPrivateSelfHeavyVertices_iff
    g h hmin hbHeavy).mpr
  apply minimalSupportPrivateHeavyCoordinate_eq_owner_of_nonzero_ownerHeavy
    g h hmin hbHeavy hb0
  exact (Finset.mem_filter.mp b.property).2

@[simp] theorem minimalSupportSelectedPrivateOwnerHeavyToSelfHeavy_val
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B)
    (b : ↥(minimalSupportSelectedPrivateOwnerHeavyVertices
      g h hmin S))
    (hb0 : b.val.val.val ≠ 0) :
    (minimalSupportSelectedPrivateOwnerHeavyToSelfHeavy
      g h hmin S b hb0).val.val = b.val.val := by
  rfl

/-- For a non-anchor selected owner-heavy witness, both normalized
coordinates (heavy and protected escape) equal the owner. -/
theorem minimalSupportSelectedPrivateOwnerHeavy_heavy_escape_eq_owner
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (S : Finset ↥B)
    (b : ↥(minimalSupportSelectedPrivateOwnerHeavyVertices
      g h hmin S))
    (hb0 : b.val.val.val ≠ 0) :
    let b' := minimalSupportSelectedPrivateOwnerHeavyToSelfHeavy
      g h hmin S b hb0
    minimalSupportPrivateHeavyCoordinate g h hmin b'.val = b.val.val ∧
      minimalSupportPrivateHeavyEscapeCoordinate
        g hg h t q ht hq hmin hqzero b'.val = b.val.val := by
  let b' := minimalSupportSelectedPrivateOwnerHeavyToSelfHeavy
    g h hmin S b hb0
  have hself : minimalSupportPrivateHeavyCoordinate g h hmin b'.val =
      b'.val.val :=
    (mem_minimalSupportPrivateSelfHeavyVertices_iff
      g h hmin b'.val).mp b'.property
  constructor
  · simpa [b'] using hself
  · simpa [b'] using
      (minimalSupportPrivateHeavyEscapeCoordinate_eq_owner_of_selfHeavy
        g hg h t q ht hq hmin hqzero b'.val hself)

/-- At most the anchor is lost when selected owner-heavy witnesses are
normalized into the global self-heavy family. -/
theorem card_minimalSupportSelectedPrivateOwnerHeavyVertices_le_selfHeavy_add_one
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) :
    (minimalSupportSelectedPrivateOwnerHeavyVertices
        g h hmin S).card ≤
      (minimalSupportPrivateSelfHeavyVertices g h hmin).card + 1 := by
  classical
  let O := minimalSupportSelectedPrivateOwnerHeavyVertices g h hmin S
  let H := minimalSupportPrivateSelfHeavyVertices g h hmin
  let enc : ↥O → Option ↥H := fun b ↦
    if hb0 : b.val.val.val = 0 then none
    else some (minimalSupportSelectedPrivateOwnerHeavyToSelfHeavy
      g h hmin S b hb0)
  have henc : Function.Injective enc := by
    intro b c hbc
    by_cases hb0 : b.val.val.val = 0
    · have hc0 : c.val.val.val = 0 := by
        by_contra hc0
        simp [enc, hb0, hc0] at hbc
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hb0.trans hc0.symm
    · have hc0 : c.val.val.val ≠ 0 := by
        intro hc0
        simp [enc, hb0, hc0] at hbc
      have hself :
          minimalSupportSelectedPrivateOwnerHeavyToSelfHeavy
              g h hmin S b hb0 =
            minimalSupportSelectedPrivateOwnerHeavyToSelfHeavy
              g h hmin S c hc0 := by
        simpa [enc, hb0, hc0] using hbc
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x ↦ x.val.val.val) hself
  have hcard := Fintype.card_le_of_injective enc henc
  change O.card ≤ H.card + 1
  calc
    O.card = Fintype.card ↥O := (Fintype.card_coe O).symm
    _ ≤ Fintype.card (Option ↥H) := hcard
    _ = H.card + 1 := by simp

/-- Directed gaps force many globally normalized self-heavy owners, ambient
external-label capacity, or a large external directed-gap fiber. -/
theorem minimalSupportSelectedPrivate_selfHeavy_or_capacity_or_largeExternalGapFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥B) (K L r : ℕ)
    (hcount : K * S.card + L * r < S.card * (S.card - 1)) :
    K ≤ (minimalSupportPrivateSelfHeavyVertices g h hmin).card ∨
      B.card + L ≤ m + 1 ∨
      ∃ z : Fin (m + 1), z ∉ B ∧
        r < (minimalSupportSelectedPrivateExternalGapFiber
          g hg h hmin S z).card := by
  rcases
      minimalSupportSelectedPrivate_ownerHeavy_or_capacity_or_largeExternalGapFiber
        g hg h hmin S K L r hcount with howner | hcapacity | hfiber
  · left
    have hnormalize :=
      card_minimalSupportSelectedPrivateOwnerHeavyVertices_le_selfHeavy_add_one
        g h hmin S
    omega
  · exact Or.inr (Or.inl hcapacity)
  · exact Or.inr (Or.inr hfiber)

/-- The normalized directed-gap alternative specialized to the owners of one
joint external heavy/escape fiber. -/
theorem minimalSupportPrivateJointFiber_selfHeavy_or_capacity_or_largeExternalGapFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e : Fin (m + 1)) (K L r : ℕ)
    (hcount : let S := (minimalSupportPrivateJointExternalHeavyEscapeOwners
        g hg h t q ht hq hmin hqzero z e)
      K * S.card + L * r < S.card * (S.card - 1)) :
    K ≤ (minimalSupportPrivateSelfHeavyVertices g h hmin).card ∨
      B.card + L ≤ m + 1 ∨
      let S := (minimalSupportPrivateJointExternalHeavyEscapeOwners
        g hg h t q ht hq hmin hqzero z e)
      ∃ w : Fin (m + 1), w ∉ B ∧
        r < (minimalSupportSelectedPrivateExternalGapFiber
          g hg h hmin S w).card := by
  let S := minimalSupportPrivateJointExternalHeavyEscapeOwners
    g hg h t q ht hq hmin hqzero z e
  exact minimalSupportSelectedPrivate_selfHeavy_or_capacity_or_largeExternalGapFiber
    g hg h hmin S K L r hcount

end MinModulus
