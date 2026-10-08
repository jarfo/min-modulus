import MinModulus.SILiftConstant
import MinModulus.RLiftTransport

/-!
# Affine transport for the SI lift

`si_extra_eq_top_of_valid_shift` pins the extra entry when the SI block
appears in its exact order, at the first `m` coordinates, and shifted by a
constant.  A deletion-child that is merely AFFINE-SI is weaker in three
ways: the block may be scaled by a unit, permuted, and the extra entry may
sit at any coordinate.

This file removes all three, exactly as `RLiftTransport` does for the
reflected family.  Validity is invariant under reindexing
(`validTuple_reindex`), translation (`validTuple_translate`) and
multiplication by a unit (`validTuple_unit_mul`), so an arbitrary affine
presentation normalizes to the exact one and the conclusion transports
back.

The upshot (`si_affine_extra`): a valid tuple whose deletion-child at ANY
coordinate is an affine image of `SI_m` has its remaining entry equal to
the affine image of the NEXT super-increasing entry `2 ^ m - 1` — that is,
the whole tuple is affine-`SI_(m+1)`.
-/

namespace MinModulus

section Transport

variable {m : ℕ}

/-- The reindexing that sends the last coordinate to `d` and the block
`castSucc i` to `d.succAbove (σ i)`. -/
noncomputable def siReindex (d : Fin (m + 1)) (σ : Fin m ≃ Fin m) : Fin (m + 1) ≃ Fin (m + 1) :=
  Equiv.ofBijective (Fin.lastCases d (fun i => d.succAbove (σ i)))
    (by
      refine (Finite.injective_iff_bijective).mp ?_
      intro p q hpq
      induction p using Fin.lastCases with
      | last =>
        induction q using Fin.lastCases with
        | last => rfl
        | cast j =>
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hpq
          exact absurd hpq.symm (Fin.succAbove_ne d (σ j))
      | cast i =>
        induction q using Fin.lastCases with
        | last =>
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hpq
          exact absurd hpq (Fin.succAbove_ne d (σ i))
        | cast j =>
          simp only [Fin.lastCases_castSucc] at hpq
          have := σ.injective (Fin.succAbove_right_injective hpq)
          rw [this])

@[simp] lemma siReindex_last (d : Fin (m + 1)) (σ : Fin m ≃ Fin m) :
    siReindex d σ (Fin.last m) = d := by
  simp [siReindex, Equiv.ofBijective]

@[simp] lemma siReindex_castSucc (d : Fin (m + 1)) (σ : Fin m ≃ Fin m)
    (i : Fin m) :
    siReindex d σ (Fin.castSucc i) = d.succAbove (σ i) := by
  simp [siReindex, Equiv.ofBijective]

/-- **Affine transport.**  If a valid tuple has, at some coordinate `d`, a
deletion-child which is a unit multiple of the super-increasing block
(reindexed arbitrarily) plus a constant, then the entry at `d` is the same
affine image of the next super-increasing entry. -/
theorem si_affine_extra {s : ℕ} (hm : 4 ≤ m) (hs : 2 ≤ s)
    (hsn : 2 ^ s ≤ m + 1)
    (G : Fin (m + 1) → ZMod (2 ^ (m + 1) - 2 ^ s))
    (d : Fin (m + 1)) (σ : Fin m ≃ Fin m)
    (u : (ZMod (2 ^ (m + 1) - 2 ^ s))ˣ)
    (c : ZMod (2 ^ (m + 1) - 2 ^ s))
    (hchild : ∀ i : Fin m,
      G (d.succAbove (σ i))
        = (u : ZMod (2 ^ (m + 1) - 2 ^ s)) * ((2 ^ i.val - 1 : ℕ) : _) + c)
    (hv : ValidTuple G) :
    G d = (u : ZMod (2 ^ (m + 1) - 2 ^ s)) * ((2 ^ m - 1 : ℕ) : _) + c := by
  -- move `d` to the last coordinate and sort the block
  have hvr : ValidTuple (fun j => G (siReindex d σ j)) :=
    validTuple_reindex G (siReindex d σ) hv
  -- divide out the unit
  have hvu : ValidTuple
      (fun j => ((u⁻¹ : (ZMod (2 ^ (m + 1) - 2 ^ s))ˣ) :
        ZMod (2 ^ (m + 1) - 2 ^ s)) * G (siReindex d σ j)) :=
    validTuple_unit_mul _ u⁻¹ hvr
  -- the normalized tuple IS the exact shifted SI parent
  have hform : (fun j => ((u⁻¹ : (ZMod (2 ^ (m + 1) - 2 ^ s))ˣ) :
        ZMod (2 ^ (m + 1) - 2 ^ s)) * G (siReindex d σ j))
      = siParentShift m (((u⁻¹ : (ZMod (2 ^ (m + 1) - 2 ^ s))ˣ) :
          ZMod (2 ^ (m + 1) - 2 ^ s)) * c)
          (((u⁻¹ : (ZMod (2 ^ (m + 1) - 2 ^ s))ˣ) :
          ZMod (2 ^ (m + 1) - 2 ^ s)) * G d) := by
    funext j
    induction j using Fin.lastCases with
    | last => simp [siParentShift, siReindex_last]
    | cast i =>
      rw [siReindex_castSucc, hchild i]
      simp only [siParentShift, Fin.snoc_castSucc]
      rw [mul_add, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hform] at hvu
  have hkey := si_extra_eq_top_of_valid_shift hm hs hsn _ _ hvu
  -- transport the conclusion back
  have h := congrArg
    (fun z => ((u : ZMod (2 ^ (m + 1) - 2 ^ s))) * z) hkey
  simp only [mul_sub, ← mul_assoc, Units.mul_inv, one_mul] at h
  exact eq_add_of_sub_eq h

end Transport

end MinModulus
