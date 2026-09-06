/-
# Quotient-collision elimination for the shorter-prefix G3 route

Two distinct entries with the same half-quotient image form an antipodal
pair, so either endpoint is commonly touched. If one is outside an actual
coherent SI prefix of length n-2, delete that endpoint and apply endpoint
extraction to the valid retained quotient. Thus this collision branch is
excluded without assuming common touch or quotient validity separately.

For a unit-scaled quotient prefix, the prefix itself is injective. Hence a
hypothetical valid exceptional tuple with that prefix must have injective
full quotient. This does not settle the injective-quotient residual or any
unrestricted global gate.
-/
import MinModulus.SIActualDeletion

namespace MinModulus
open Finset

/-- A collision of distinct original coordinates under half reduction
constructs common touch at either chosen endpoint. -/
theorem commonTouched_of_distinct_quotient_collision
    {n M : ℕ} [NeZero M] (g : Fin n → ZMod (2 * M)) (hg : ValidTuple g)
    {i j : Fin n} (hne : i ≠ j)
    (hcollision : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g j)) :
    ∀ w, Witness g (M : ZMod (2 * M)) w → w j ≠ 0 := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  rcases eq_or_eq_add_half_of_castHom_eq (g i) (g j) hcollision with heq | hpair
  · exact False.elim (hne (validTuple_injective g hg heq))
  · have hdiff : g i - g j = (M : ZMod (2 * M)) := by rw [hpair]; abel
    exact common_touched_of_pair_difference g hg (half_add_half rfl)
      (half_ne_zero rfl hMpos) hdiff

/-- G3 exclusion when the final coordinate collides in the quotient
with any other coordinate. Common touch is derived from the collision. -/
theorem not_validTuple_exceptional_of_last_collision_scaled_short_prefix
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod (globalBound (m + 1)))
    (k : Fin (m + 2)) (hne : k ≠ e (Fin.last (m + 1)))
    (hcollision :
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1))) (g k) =
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g (e (Fin.last (m + 1)))))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g (e i.castSucc.castSucc)) = c * (a i.val : ZMod (globalBound (m + 1))) + b) :
    ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (globalBound (m + 1)) := ⟨by omega⟩
  exact not_validTuple_exceptional_of_commonTouched_quotient_scaled_short_prefix
    hm hnpow g e c b (commonTouched_of_distinct_quotient_collision g hg hne hcollision)
    hprefix hg

/-- Any quotient collision involving a coordinate outside the shorter SI
prefix excludes the original exceptional tuple. The other coordinate may
lie inside or outside the prefix; the multiplier may be a nonunit. -/
theorem not_validTuple_exceptional_of_tail_collision_scaled_short_prefix
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod (globalBound (m + 1)))
    (j : Fin (m + 2)) (hj : m ≤ j.val) (k : Fin (m + 2)) (hne : k ≠ e j)
    (hcollision :
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1))) (g k) =
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1))) (g (e j)))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g (e i.castSucc.castSucc)) = c * (a i.val : ZMod (globalBound (m + 1))) + b) :
    ¬ ValidTuple g := by
  let p := Equiv.swap j (Fin.last (m + 1))
  let E := p.trans e
  have hlast : E (Fin.last (m + 1)) = e j := by simp [E, p]
  apply not_validTuple_exceptional_of_last_collision_scaled_short_prefix
    hm hnpow g E c b k (by simpa only [hlast] using hne)
      (by simpa only [hlast] using hcollision)
  intro i
  have hip : p i.castSucc.castSucc = i.castSucc.castSucc := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_castSucc] at hv
      omega
    · intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_castSucc, Fin.val_last] at hv
      omega
  change ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
    (g (e (p i.castSucc.castSucc))) = _
  rw [hip]
  exact hprefix i

/-- With a unit-scaled shorter SI prefix, a hypothetical valid G3 tuple
must have injective full half-quotient image. No retained-quotient validity
or common-touch hypothesis is assumed. -/
theorem injective_quotient_of_valid_exceptional_unit_short_prefix
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1))) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod (globalBound (m + 1))) (hc : IsUnit c)
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g (e i.castSucc.castSucc)) = c * (a i.val : ZMod (globalBound (m + 1))) + b) :
    Function.Injective (fun i ↦
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1))) (g i)) := by
  let π := ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
  suffices h : Function.Injective (fun i ↦ π (g (e i))) by
    intro x y hxy
    have := h (show π (g (e (e.symm x))) = π (g (e (e.symm y))) by
      simpa only [Equiv.apply_symm_apply] using hxy)
    exact e.symm.injective this
  intro x y hxy
  by_contra hne
  have hx : x.val < m := by
    by_contra hx
    exact not_validTuple_exceptional_of_tail_collision_scaled_short_prefix hm hnpow
      g e c b x (by omega) (e y) (fun h ↦ hne (e.injective h).symm) hxy.symm hprefix hg
  have hy : y.val < m := by
    by_contra hy
    exact not_validTuple_exceptional_of_tail_collision_scaled_short_prefix hm hnpow
      g e c b y (by omega) (e x) (fun h ↦ hne (e.injective h)) hxy hprefix hg
  let i : Fin m := ⟨x.val, hx⟩
  let j : Fin m := ⟨y.val, hy⟩
  have hi : i.castSucc.castSucc = x := Fin.ext rfl
  have hj : j.castSucc.castSucc = y := Fin.ext rfl
  have hfixed : ValidTuple (fun k : Fin (m + 1) ↦ (a k.val : ZMod (globalBound (m + 1)))) :=
    validTuple_fixed_of_valid (theoremA (by omega))
  have hv : c * (a i.val : ZMod (globalBound (m + 1))) = c * (a j.val : ZMod (globalBound (m + 1))) := by
    apply add_right_cancel (b := b)
    rw [← hprefix i, ← hprefix j, hi, hj]
    exact hxy
  have ha : (a i.val : ZMod (globalBound (m + 1))) = (a j.val : ZMod (globalBound (m + 1))) :=
    hc.mul_left_cancel hv
  have heq : i.castSucc = j.castSucc := validTuple_injective _ hfixed ha
  apply hne
  apply Fin.ext
  have hval := congrArg (fun k : Fin (m + 1) ↦ k.val) heq
  exact hval

end MinModulus
