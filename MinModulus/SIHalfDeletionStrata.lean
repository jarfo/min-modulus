/-
# Global and exact-stratum bounds from actual SI half deletion

An actual valid half-deleted quotient with a coherent SI prefix of length
n-2, under any multiplier, gives the full global bound upstairs. A globally
subcritical doubling of its power-gap modulus must be the exceptional
endpoint, already excluded by actual endpoint extraction and SI lift cover.
In the whole subbinary range the upstairs fixed SI set is therefore valid
at the same modulus, which also supplies every exact-stratum threshold.

Common touch and outside-prefix quotient collisions construct the required
actual quotient. Their consumers permit arbitrary original lift bits and
nonunit multipliers. Quotient validity is not inferred from upstairs
validity alone. No unrestricted G1/G2/G3 input is assumed.
-/
import MinModulus.SIQuotientCollision

namespace MinModulus
open Finset

/-- A valid coherent SI-prefix extension has a modulus at which the full
fixed set is also valid, throughout the subbinary range. This is a modulus
statement; the original tuple need not be the same fixed set. -/
theorem valid_fixed_of_valid_scaled_fixed_prefix_lt_two_pow
    {m N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 1))) (c b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc) = c * (a i.val : ZMod N) + b)
    (hupper : N < 2 ^ (m + 1)) : Valid (m + 1) N := by
  obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_scaled_fixed_prefix_lt_two_pow
    hm g hg e c b hprefix hupper
  have hbound := global_lower_bound_of_valid_scaled_fixed_prefix hm g hg e c b hprefix
  have hp := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) ht.le
  have hlog := Nat.pow_log_le_self 2 (by omega : m + 1 ≠ 0)
  have htle : 2 ^ t ≤ m + 1 := by
    rw [hgap] at hbound
    unfold globalBound at hbound
    omega
  rw [hgap]
  exact valid_gap (by omega) htle

/-- A valid actual half-deleted quotient with an arbitrary-multiplier SI
prefix forces the full global bound upstairs, with independent lift bits
and its remaining extra entry unrestricted. -/
theorem global_lower_bound_of_valid_quotient_scaled_short_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod M)
    (hret : ValidTuple (fun i : Fin (m + 1) ↦
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i.castSucc))))
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc.castSucc)) = c * (a i.val : ZMod M) + b) :
    globalBound (m + 2) ≤ 2 * M := by
  by_contra hnot
  have hcrit : 2 * M < globalBound (m + 2) := Nat.lt_of_not_ge hnot
  have hp : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [pow_succ']
  have hbinary : 2 * M < 2 ^ (m + 2) := hcrit.trans_le (Nat.sub_le _ _)
  have hupper : M < 2 ^ (m + 1) := by rw [hp] at hbinary; omega
  have hfixed := valid_fixed_of_valid_scaled_fixed_prefix_lt_two_pow (by omega)
    _ hret (Equiv.refl _) c b hprefix hupper
  have hcard := Fintype.card_le_of_injective _ (validTuple_injective _ hret)
  simp only [Fintype.card_fin, ZMod.card] at hcard
  obtain ⟨hM, hnpow⟩ := eq_globalBound_of_valid_fixed_double_lt (by omega : 2 ≤ m + 1)
    (by omega) hfixed (by simpa only [Nat.add_assoc] using hcrit)
  subst M
  exact not_validTuple_exceptional_of_valid_quotient_scaled_short_prefix hm hnpow
    g e c b hret hprefix hg

/-- Actual half deletion transports full fixed-set validity to the original
modulus throughout the subbinary range. The conclusion concerns the
modulus, not affine classification of the original tuple. -/
theorem valid_fixed_of_valid_quotient_scaled_short_prefix_lt_two_pow
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod M)
    (hret : ValidTuple (fun i : Fin (m + 1) ↦
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i.castSucc))))
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc.castSucc)) = c * (a i.val : ZMod M) + b)
    (hupper : 2 * M < 2 ^ (m + 2)) : Valid (m + 2) (2 * M) := by
  have hp : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [pow_succ']
  obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_scaled_fixed_prefix_lt_two_pow
    (by omega : 2 ≤ m) _ hret (Equiv.refl _) c b hprefix (by omega)
  have hgap2 : 2 * M = 2 ^ (m + 2) - 2 ^ (t + 1) := by
    simpa only [Nat.mul_sub_left_distrib, ← pow_succ', Nat.add_assoc] using
      congrArg (fun k : ℕ ↦ 2 * k) hgap
  have hbound := global_lower_bound_of_valid_quotient_scaled_short_prefix hm g hg e c b hret hprefix
  have ht2 := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : t + 1 ≤ m + 2)
  have hlog := Nat.pow_log_le_self 2 (by omega : m + 2 ≠ 0)
  have htle : 2 ^ (t + 1) ≤ m + 2 := by
    rw [hgap2] at hbound
    unfold globalBound at hbound
    omega
  rw [hgap2]
  exact valid_gap (by omega) htle

/-- Every actual valuation threshold follows from a valid half-deleted
SI-prefix quotient, with no coherence requirement on the original lifts. -/
theorem stratum_lower_bound_of_valid_quotient_scaled_short_prefix
    {m M s q : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd q) (hN : 2 * M = 2 ^ s * q)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod M)
    (hret : ValidTuple (fun i : Fin (m + 1) ↦
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i.castSucc))))
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc.castSucc)) = c * (a i.val : ZMod M) + b) :
    stratumBound (m + 2) s ≤ 2 * M := by
  by_cases hupper : 2 * M < 2 ^ (m + 2)
  · have hv := valid_fixed_of_valid_quotient_scaled_short_prefix_lt_two_pow
      hm g hg e c b hret hprefix hupper
    rw [hN] at hv ⊢
    exact stratum_lower_bound_of_valid_fixed (by omega) hq hv
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Common touch at the reindexed last coordinate constructs the specific
retained quotient, not merely the existence of some smaller valid tuple. -/
theorem validTuple_last_half_of_commonTouched_reindex
    {n M : ℕ} [NeZero M]
    (g : Fin (n + 1) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (n + 1)))
    (htouch : ∀ w, Witness g (M : ZMod (2 * M)) w → w (e (Fin.last n)) ≠ 0) :
    ValidTuple (fun i : Fin n ↦
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i.castSucc))) := by
  have hg' := validTuple_embedding e.toEmbedding g hg
  have ht : ∀ w, Witness (fun i ↦ g (e i)) (M : ZMod (2 * M)) w →
      w (Fin.last n) ≠ 0 := by
    intro w hw
    have h := htouch _ (witness_reindex_perm g e hw)
    simpa using h
  have hv := (validTuple_deleted_half_iff_commonTouched (fun i ↦ g (e i)) hg'
    (Fin.last n)).mpr ht
  simpa using hv

/-- Common touch outside the shorter SI quotient prefix supplies the global
bound at every positive even modulus, under any quotient multiplier. -/
theorem global_lower_bound_of_valid_commonTouched_quotient_scaled_short_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod M)
    (htouch : ∀ w, Witness g (M : ZMod (2 * M)) w → w (e (Fin.last (m + 1))) ≠ 0)
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc.castSucc)) = c * (a i.val : ZMod M) + b) :
    globalBound (m + 2) ≤ 2 * M :=
  global_lower_bound_of_valid_quotient_scaled_short_prefix hm g hg e c b
    (validTuple_last_half_of_commonTouched_reindex g hg e htouch) hprefix

/-- The same actual common-touch deletion yields the exact stratum bound. -/
theorem stratum_lower_bound_of_valid_commonTouched_quotient_scaled_short_prefix
    {m M s q : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd q) (hN : 2 * M = 2 ^ s * q)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod M)
    (htouch : ∀ w, Witness g (M : ZMod (2 * M)) w → w (e (Fin.last (m + 1))) ≠ 0)
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc.castSucc)) = c * (a i.val : ZMod M) + b) :
    stratumBound (m + 2) s ≤ 2 * M :=
  stratum_lower_bound_of_valid_quotient_scaled_short_prefix hm hq hN g hg e c b
    (validTuple_last_half_of_commonTouched_reindex g hg e htouch) hprefix

/-- An actual quotient collision with an outside-prefix coordinate yields
a reindexing with a valid retained quotient and the same shorter SI data.
The collision partner may be inside or outside the prefix. -/
theorem exists_valid_half_quotient_scaled_short_prefix_of_tail_collision
    {m M : ℕ} [NeZero M]
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod M)
    (j : Fin (m + 2)) (hj : m ≤ j.val) (k : Fin (m + 2)) (hne : k ≠ e j)
    (hcollision : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g k) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e j)))
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc.castSucc)) = c * (a i.val : ZMod M) + b) :
    ∃ E : Equiv.Perm (Fin (m + 2)),
      ValidTuple (fun i : Fin (m + 1) ↦
        ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (E i.castSucc))) ∧
      ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
        (g (E i.castSucc.castSucc)) = c * (a i.val : ZMod M) + b := by
  let p := Equiv.swap j (Fin.last (m + 1))
  let E := p.trans e
  have hlast : E (Fin.last (m + 1)) = e j := by simp [E, p]
  refine ⟨E, validTuple_last_half_of_commonTouched_reindex g hg E ?_, ?_⟩
  · rw [hlast]
    exact commonTouched_of_distinct_quotient_collision g hg hne hcollision
  · intro i
    have hip : p i.castSucc.castSucc = i.castSucc.castSucc := by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_castSucc] at hv
        omega
      · exact Fin.castSucc_ne_last i.castSucc
    change ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (p i.castSucc.castSucc))) = _
    rw [hip]
    exact hprefix i

/-- A tail quotient collision gives the full global numerical bound for
the independently lifted shorter SI prefix, under any multiplier. -/
theorem global_lower_bound_of_valid_tail_collision_quotient_scaled_short_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod M)
    (j : Fin (m + 2)) (hj : m ≤ j.val) (k : Fin (m + 2)) (hne : k ≠ e j)
    (hcollision : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g k) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e j)))
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc.castSucc)) = c * (a i.val : ZMod M) + b) :
    globalBound (m + 2) ≤ 2 * M := by
  obtain ⟨E, hret, hpref⟩ := exists_valid_half_quotient_scaled_short_prefix_of_tail_collision
    g hg e c b j hj k hne hcollision hprefix
  exact global_lower_bound_of_valid_quotient_scaled_short_prefix hm g hg E c b hret hpref

/-- Tail quotient collisions satisfy all exact even-stratum thresholds,
not only the exceptional G3 endpoint. -/
theorem stratum_lower_bound_of_valid_tail_collision_quotient_scaled_short_prefix
    {m M s q : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd q) (hN : 2 * M = 2 ^ s * q)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod M)
    (j : Fin (m + 2)) (hj : m ≤ j.val) (k : Fin (m + 2)) (hne : k ≠ e j)
    (hcollision : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g k) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e j)))
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc.castSucc)) = c * (a i.val : ZMod M) + b) :
    stratumBound (m + 2) s ≤ 2 * M := by
  obtain ⟨E, hret, hpref⟩ := exists_valid_half_quotient_scaled_short_prefix_of_tail_collision
    g hg e c b j hj k hne hcollision hprefix
  exact stratum_lower_bound_of_valid_quotient_scaled_short_prefix hm hq hN g hg E c b hret hpref

/-- Direct critical-G1 exclusion from actual quotient collision data,
without assuming a half-witness or a valid smaller quotient. -/
theorem not_validTuple_of_critical_tail_collision_quotient_scaled_short_prefix
    {m M s q : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd q) (hN : 2 * M = 2 ^ s * q)
    (hcritical : 2 * M < stratumBound (m + 2) s)
    (g : Fin (m + 2) → ZMod (2 * M))
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod M)
    (j : Fin (m + 2)) (hj : m ≤ j.val) (k : Fin (m + 2)) (hne : k ≠ e j)
    (hcollision : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g k) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e j)))
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc.castSucc)) = c * (a i.val : ZMod M) + b) : ¬ ValidTuple g := by
  intro hg
  exact (not_lt_of_ge
    (stratum_lower_bound_of_valid_tail_collision_quotient_scaled_short_prefix hm hq hN
      g hg e c b j hj k hne hcollision hprefix)) hcritical

/-- In every critical even stratum, an independently lifted unit-scaled
shorter SI prefix forces the ENTIRE half quotient to be injective.
The previous G3-only injectivity restriction now holds throughout G1. -/
theorem injective_quotient_of_valid_critical_unit_short_prefix
    {m M s q : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd q) (hN : 2 * M = 2 ^ s * q)
    (hcritical : 2 * M < stratumBound (m + 2) s)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod M) (hc : IsUnit c)
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc.castSucc)) = c * (a i.val : ZMod M) + b) :
    Function.Injective (fun i ↦ ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)) := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  have hbinary := two_pow_pred_le_card_of_validTuple g hg
  simp only [ZMod.card, show m + 2 - 1 = m + 1 by omega, pow_succ'] at hbinary
  have hMbound : 2 ^ m ≤ M := by omega
  suffices hinj : Function.Injective (fun i ↦ π (g (e i))) by
    intro x y hxy
    apply e.symm.injective
    exact hinj (by simpa only [Equiv.apply_symm_apply] using hxy)
  intro x y hxy
  by_contra hne
  have hx : x.val < m := by
    by_contra hx
    exact not_validTuple_of_critical_tail_collision_quotient_scaled_short_prefix hm hq hN hcritical
      g e c b x (by omega) (e y) (fun h ↦ hne (e.injective h).symm) hxy.symm hprefix hg
  have hy : y.val < m := by
    by_contra hy
    exact not_validTuple_of_critical_tail_collision_quotient_scaled_short_prefix hm hq hN hcritical
      g e c b y (by omega) (e x) (fun h ↦ hne (e.injective h)) hxy hprefix hg
  let i : Fin m := ⟨x.val, hx⟩
  let j : Fin m := ⟨y.val, hy⟩
  have hi : i.castSucc.castSucc = x := Fin.ext rfl
  have hj : j.castSucc.castSucc = y := Fin.ext rfl
  have hscaled : c * (a i.val : ZMod M) = c * (a j.val : ZMod M) := by
    apply add_right_cancel (b := b)
    rw [← hprefix i, ← hprefix j, hi, hj]
    exact hxy
  have ha := hc.mul_left_cancel hscaled
  have hsmall (k : Fin m) : a k.val < M := by
    have hp := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) k.isLt.le
    have hpos : 0 < 2 ^ k.val := by positivity
    unfold a
    omega
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp ha
  change a i.val % M = a j.val % M at hmod
  rw [Nat.mod_eq_of_lt (hsmall i), Nat.mod_eq_of_lt (hsmall j)] at hmod
  have hp : 2 ^ i.val = 2 ^ j.val := by
    have hpi : 0 < 2 ^ i.val := by positivity
    have hpj : 0 < 2 ^ j.val := by positivity
    unfold a at hmod
    omega
  have heq := Nat.pow_right_injective (by omega : 2 ≤ (2 : ℕ)) hp
  exact hne (Fin.ext heq)

end MinModulus
