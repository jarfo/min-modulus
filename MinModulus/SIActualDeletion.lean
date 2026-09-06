/-
# Actual half deletion and the shorter-prefix G3 consumer

For a specified deleted coordinate, validity of the actual cyclic half
quotient is equivalent to common touch. The G3 consumer can therefore
construct the required retained quotient from an original half-witness
hypothesis, rather than assuming quotient validity separately.

This connects a proved G1 branch to endpoint extraction. It does not turn
abstract existence of a smaller tuple into actual coordinate deletion, or
prove common touch in the unresolved three-omission cases.
-/
import MinModulus.SIEndpointRigidity
import MinModulus.G1CriticalThreeOmissions

namespace MinModulus
open Finset

/-- The abstract cyclic quotient equivalence computes actual reduction. -/
theorem quotZMultiplesEquivZMod_mk {N M : ℕ} [NeZero N] [NeZero M]
    (hdvd : M ∣ N) (x : ZMod N) :
    quotZMultiplesEquivZMod hdvd
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples ((M : ℕ) : ZMod N)) x) =
      ZMod.castHom hdvd (ZMod M) x := by
  rfl

/-- A specified actual deletion is valid in the half quotient exactly
when every original half-witness touches the deleted coordinate. -/
theorem validTuple_deleted_half_iff_commonTouched
    {n M : ℕ} [NeZero M] (g : Fin (n + 1) → ZMod (2 * M)) (hg : ValidTuple g)
    (j : Fin (n + 1)) :
    ValidTuple (fun i : Fin n ↦
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (j.succAbove i))) ↔
      ∀ c, Witness g (M : ZMod (2 * M)) c → c j ≠ 0 := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  constructor
  · intro hv c hc hj
    apply (validTuple_iff_no_zero_witness _).mp hv (fun i ↦ c (j.succAbove i))
    refine ⟨?_, fun i ↦ hc.2.1 _, ?_, ?_⟩
    · intro hz
      apply hc.1
      funext l
      by_cases hl : l = j
      · subst l; exact hj
      · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hl
        rw [← hi]
        exact congrFun hz i
    · have hs := hc.2.2.1
      rw [Fin.sum_univ_succAbove c j, hj, zero_add] at hs
      exact hs
    · have hs := hc.2.2.2
      rw [Fin.sum_univ_succAbove (fun l ↦ c l • g l) j, hj, zero_smul, zero_add] at hs
      have hp := congrArg π hs
      simpa only [map_sum, map_zsmul, map_natCast, ZMod.natCast_self] using hp
  · intro hj
    have hq := deletion_descent g hg (half_add_half rfl) j hj
    have hv := validTuple_comp hq (quotZMultiplesEquivZMod (dvd_mul_left M 2)).toAddMonoidHom
      (quotZMultiplesEquivZMod (dvd_mul_left M 2)).injective
    change ValidTuple (fun i ↦ quotZMultiplesEquivZMod (dvd_mul_left M 2)
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples ((M : ℕ) : ZMod (2 * M)))
        (g (j.succAbove i)))) at hv
    simpa only [quotZMultiplesEquivZMod_mk] using hv

/-- The shorter-prefix G3 exclusion can use common touch in the original
tuple: actual retained-quotient validity is constructed, not assumed.
The omitted coordinate is outside the prescribed n-2-entry prefix. -/
theorem not_validTuple_exceptional_of_commonTouched_quotient_scaled_short_prefix
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod (globalBound (m + 1)))
    (htouch : ∀ w, Witness g ((globalBound (m + 1) : ℕ) : ZMod (2 * globalBound (m + 1))) w →
      w (e (Fin.last (m + 1))) ≠ 0)
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g (e i.castSucc.castSucc)) = c * (a i.val : ZMod (globalBound (m + 1))) + b) :
    ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (globalBound (m + 1)) := ⟨by omega⟩
  have hg' := validTuple_embedding e.toEmbedding g hg
  have ht : ∀ w, Witness (fun i ↦ g (e i))
      ((globalBound (m + 1) : ℕ) : ZMod (2 * globalBound (m + 1))) w →
      w (Fin.last (m + 1)) ≠ 0 := by
    intro w hw
    have h := htouch _ (witness_reindex_perm g e hw)
    simpa using h
  have hv := (validTuple_deleted_half_iff_commonTouched (fun i ↦ g (e i)) hg'
    (Fin.last (m + 1))).mpr ht
  apply not_validTuple_exceptional_of_valid_quotient_scaled_short_prefix
    hm hnpow g e c b _ hprefix hg
  simpa using hv

end MinModulus
