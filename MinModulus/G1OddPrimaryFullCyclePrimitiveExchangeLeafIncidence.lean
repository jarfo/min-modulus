/-
# Leaf incidence for the primitive middle exchange family

The simultaneous primitive middle-exchange family contains at least sixteen
literal exact-two transversals.  This module reconnects that family to the
fixed full-cycle leaf geometry without discarding the exchanged set.

If a selected owner lies off the leaf range, erasing it preserves the old
full-or-one-missing leaf incidence; inserting the fixed retained coordinate
can only fill the unique missing leaf.  The existing sixth-stratum leaf
terminal therefore applies to that literal exchanged transversal.  Otherwise
all selected owners lie in the injective leaf range, forcing a cycle of length
at least sixteen while retaining the entire exact-exchange family.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeFamily

namespace MinModulus

open Finset

variable {n : ℕ}

/-- Erasing a point outside an injective cycle's leaf range and inserting an
arbitrary point preserves the alternative that all leaves, or all but one
leaf, belong to the finset.  The inserted point may fill the unique hole. -/
theorem leafIncidence_insert_erase_of_owner_not_mem_range
    {B : Finset (Fin n)} {d : ℕ} (leaf : Fin d → Fin n)
    {b r : Fin n}
    (hboff : b ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (hincidence :
      (∀ i, leaf i ∈ B) ∨
        ∃ p : Fin d, ∀ i, leaf i ∈ B ↔ i ≠ p) :
    (∀ i, leaf i ∈ insert r (B.erase b)) ∨
      ∃ p : Fin d, ∀ i, leaf i ∈ insert r (B.erase b) ↔ i ≠ p := by
  classical
  have hleafNe : ∀ i, leaf i ≠ b := by
    intro i hi
    apply hboff
    rw [← hi]
    exact Finset.mem_image_of_mem leaf (Finset.mem_univ i)
  rcases hincidence with hfull | ⟨p, hpunctured⟩
  · left
    intro i
    exact Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨hleafNe i, hfull i⟩)
  · by_cases hrp : r = leaf p
    · left
      intro i
      by_cases hip : i = p
      · subst i
        exact Finset.mem_insert.mpr (Or.inl hrp.symm)
      · exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr
            ⟨hleafNe i, (hpunctured i).mpr hip⟩)
    · right
      refine ⟨p, ?_⟩
      intro i
      constructor
      · intro hi hip
        subst i
        simp only [Finset.mem_insert, Finset.mem_erase] at hi
        rcases hi with hpr | ⟨_, hpB⟩
        · exact hrp hpr.symm
        · exact (hpunctured p).mp hpB rfl
      · intro hip
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr
            ⟨hleafNe i, (hpunctured i).mpr hip⟩)

/-- A finite selected owner set either contains an owner outside the leaf
range, or is entirely contained in that range. -/
theorem selected_owner_off_leafRange_or_subset
    {B S : Finset (Fin n)} (hSsub : S ⊆ B)
    {d : ℕ} (leaf : Fin d → Fin n) :
    (∃ b : ↥B,
        (b : Fin n) ∈ S ∧
          (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf) ∨
      S ⊆ (Finset.univ : Finset (Fin d)).image leaf := by
  classical
  by_cases hoff :
      ∃ b : ↥B,
        (b : Fin n) ∈ S ∧
          (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf
  · exact Or.inl hoff
  · right
    intro i hiS
    by_contra hiRange
    exact hoff ⟨⟨i, hSsub hiS⟩, hiS, hiRange⟩

/-- The lossless on-leaf survivor: at least sixteen selected owners remain,
all lie in the fixed leaf range, and every literal exchange is still a
primitive exact-two state. -/
def PrimitiveMiddleOnLeafExchangeFamily
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ S : Finset (Fin n), ∃ k₀ : ℤ,
      16 ≤ S.card ∧ S ⊆ B ∧ (k₀ = -1 ∨ k₀ = 0) ∧
      S ⊆ (Finset.univ : Finset (Fin d)).image leaf ∧
      ∀ b : ↥B, (b : Fin n) ∈ S →
        PrimitiveTwoRetainedSixthStratumRows g y
          (middleExchangeSet g y p k₀ b)

/-- Injectivity of the leaf parametrization turns the on-leaf family into the
quantitative large-cycle conclusion needed by the charge arm. -/
theorem PrimitiveMiddleOnLeafExchangeFamily.sixteen_le_cycle
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (hfamily : PrimitiveMiddleOnLeafExchangeFamily g y B leaf) :
    16 ≤ d := by
  rcases hfamily with ⟨_, S, _, hScard, _, _, hSrange, _⟩
  have hcardLe :
      S.card ≤ ((Finset.univ : Finset (Fin d)).image leaf).card :=
    Finset.card_le_card hSrange
  have hcardRange :
      ((Finset.univ : Finset (Fin d)).image leaf).card = d := by
    rw [Finset.card_image_of_injective _ hleaf]
    simp
  omega

/-- Lossless leaf split for the simultaneous exact-exchange family.

Off the leaf range, the existing sixth-stratum terminal is reinstalled on the
literal exchanged transversal.  If no such owner exists, the entire large
primitive family is retained in the on-leaf arm. -/
theorem PrimitiveMiddleAllExactExchangeFamily.offLeafTerminal_or_onLeafFamily
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hfamily : PrimitiveMiddleAllExactExchangeFamily g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    (hd : 2 ≤ d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ 6 * q))
    (hleafIncidence :
      (∀ i, leaf i ∈ B) ∨
        ∃ p : Fin d, ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - base = (2 : ℤ) • (g (leaf i) - base))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y) :
    (∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
      ∃ S : Finset (Fin n), ∃ k₀ : ℤ, ∃ b : ↥B,
        16 ≤ S.card ∧ S ⊆ B ∧ (k₀ = -1 ∨ k₀ = 0) ∧
        (b : Fin n) ∈ S ∧
        (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf ∧
        PrimitiveTwoRetainedSixthStratumRows g y
          (middleExchangeSet g y p k₀ b) ∧
        TwoRetainedSixthStratumLeafTerminal
          (middleExchangeSet g y p k₀ b) leaf) ∨
      PrimitiveMiddleOnLeafExchangeFamily g y B leaf := by
  classical
  rcases hfamily with
    ⟨p, S, k₀, hScard, hSsub, hmiddle, hstates⟩
  rcases selected_owner_off_leafRange_or_subset hSsub leaf with
    ⟨b, hbS, hboff⟩ | hSrange
  · left
    have hstate := hstates b hbS
    have hincidence :
        (∀ i, leaf i ∈ middleExchangeSet g y p k₀ b) ∨
          ∃ missing : Fin d,
            ∀ i, leaf i ∈ middleExchangeSet g y p k₀ b ↔
              i ≠ missing := by
      rcases hmiddle with hk | hk
      · subst k₀
        simpa only [middleExchangeSet, if_true] using
          (leafIncidence_insert_erase_of_owner_not_mem_range
            leaf hboff hleafIncidence (r := p.x))
      · subst k₀
        have hzero : (0 : ℤ) ≠ -1 := by omega
        simpa only [middleExchangeSet, hzero, if_false] using
          (leafIncidence_insert_erase_of_owner_not_mem_range
            leaf hboff hleafIncidence (r := p.z))
    have hterminal :
        TwoRetainedSixthStratumLeafTerminal
          (middleExchangeSet g y p k₀ b) leaf :=
      hstate.2.2.1.sixthStratum_leafTerminal
        g hg hunique hne y hyq (middleExchangeSet g y p k₀ b)
          hminimal hd leaf R hRne base hincidence hdouble hspan
    exact ⟨p, S, k₀, b, hScard, hSsub, hmiddle, hbS, hboff,
      hstate, hterminal⟩
  · right
    exact ⟨p, S, k₀, hScard, hSsub, hmiddle, hSrange, hstates⟩

/-- Numerical front end of the lossless split: either an explicit off-leaf
exchange has reached the leaf terminal, or the fixed cycle has length at
least sixteen. -/
theorem PrimitiveMiddleAllExactExchangeFamily.offLeafTerminal_or_sixteen_le_cycle
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hfamily : PrimitiveMiddleAllExactExchangeFamily g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    (hd : 2 ≤ d) (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ 6 * q))
    (hleafIncidence :
      (∀ i, leaf i ∈ B) ∨
        ∃ p : Fin d, ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - base = (2 : ℤ) • (g (leaf i) - base))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y) :
    (∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
      ∃ S : Finset (Fin n), ∃ k₀ : ℤ, ∃ b : ↥B,
        16 ≤ S.card ∧ S ⊆ B ∧ (k₀ = -1 ∨ k₀ = 0) ∧
        (b : Fin n) ∈ S ∧
        (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf ∧
        PrimitiveTwoRetainedSixthStratumRows g y
          (middleExchangeSet g y p k₀ b) ∧
        TwoRetainedSixthStratumLeafTerminal
          (middleExchangeSet g y p k₀ b) leaf) ∨
      16 ≤ d := by
  rcases hfamily.offLeafTerminal_or_onLeafFamily
      g hg hunique hne y hyq B hminimal hd leaf R hRne base
        hleafIncidence hdouble hspan with hoff | hon
  · exact Or.inl hoff
  · exact Or.inr
      (hon.sixteen_le_cycle g y B leaf hleaf)

end MinModulus
