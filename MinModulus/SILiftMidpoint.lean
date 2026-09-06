/-
# Binary threshold for quotient-midpoint extensions of SI lift prefixes

An independently lifted SI quotient prefix of length n-1 cannot have a
valid subbinary extension whose last entry is a quotient midpoint of two
distinct prefix entries. The downstairs midpoint relation must switch
sheets upstairs. A one-hole quotient cover then gives either an omitted
last coordinate or a repeated last coordinate. At the remaining hole,
the last quotient value is -1; actual coherence extraction and the global
bound contradict the midpoint's dyadic divisibility constraint.

All positive half moduli and all independent lift bits are allowed.
The binary conclusion excludes this class from every critical even
stratum. It does not assert extraction of such a midpoint from arbitrary
tuples or close any unrestricted global gate.
-/
import MinModulus.SILiftMinusOne

namespace MinModulus
open Finset

/-- The lifted-prefix one-hole cover includes the last subbinary quotient
boundary. Its final residue is twice the largest available coin. -/
theorem exists_lift_multiset_sum_mod_except_hole_of_lt_two_pow
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M < 2 ^ m)
    (u : Fin m → ZMod (2 * M))
    (hu : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (u i) = (a i.val : ZMod M))
    (x : ZMod M) (hne : x.val ≠ 2 ^ m - m) :
    ∃ s : Multiset (Fin m), s.card = m - 1 ∧
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) ((s.map u).sum) = x := by
  classical
  by_cases hsmall : M ≤ 2 ^ m - 2
  · exact exists_lift_multiset_sum_mod_except_hole (by omega) hsmall u hu x hne
  have hx := x.val_lt
  have hp := Nat.lt_two_pow_self (n := m - 1)
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hcoins : ∃ s : Multiset ℕ, s.card ≤ m - 1 ∧
      (∀ i ∈ s, i < m) ∧ (s.map a).sum = x.val := by
    by_cases hend : x.val = 2 * (2 ^ (m - 1) - 1)
    · refine ⟨Multiset.replicate 2 (m - 1), by simp; omega, ?_, ?_⟩
      · intro i hi
        have := (Multiset.mem_replicate.mp hi).2
        omega
      · simp [a, hend]; omega
    · obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt_two_mul
        (by omega : 1 ≤ m - 1) x.val (by omega) (by omega)
      exact ⟨s, hs, fun i hi ↦ by have := hmem i hi; omega, hsum⟩
  obtain ⟨s, hs, hmem, hsum⟩ := hcoins
  obtain ⟨v, hv, hvsum⟩ := exists_fixed_multiset_sum_of_nat_coin_representation_card
    (m := m) (N := M) (K := m - 1) (by omega) s hs hmem hsum
  refine ⟨v, hv, ?_⟩
  rw [map_multiset_sum, Multiset.map_map]
  change (v.map (fun i ↦ ZMod.castHom (dvd_mul_left M 2) (ZMod M) (u i))).sum = x
  simpa only [hu, ZMod.natCast_zmod_val] using hvsum

/-- A subbinary valid midpoint extension can survive the one-hole cover
only at normalized quotient value -1. No lift normalization is assumed. -/
theorem eq_neg_one_of_valid_si_lift_prefix_midpoint
    {m M : ℕ} [NeZero M] (hm : 2 ≤ m) (hM : M < 2 ^ (m + 1))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (i j : Fin (m + 1)) (hij : i ≠ j)
    (hmid : 2 • ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) =
      (a i.val : ZMod M) + (a j.val : ZMod M)) :
    ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) = -1 := by
  classical
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let x := Fin.last (m + 1)
  let u := fun k : Fin (m + 1) ↦ g k.castSucc
  have hpair : 2 • g x = g i.castSucc + g j.castSucc + M := by
    have hproj : π (2 • g x) = π (g i.castSucc + g j.castSucc) := by
      rw [map_nsmul, map_add, hprefix, hprefix]
      exact hmid
    rcases eq_or_eq_add_half_of_castHom_eq _ _ hproj with heq | heq
    · exact False.elim (not_validTuple_of_double_eq_distinct_pair g i.castSucc j.castSucc x
        (fun h ↦ hij (Fin.castSucc_injective _ h)) heq hg)
    · exact heq
  let z := π ((∑ k, g k) - 2 • g x)
  have hhole : z.val = 2 ^ (m + 1) - (m + 1) := by
    by_contra hne
    obtain ⟨v, hv, hvsum⟩ := exists_lift_multiset_sum_mod_except_hole_of_lt_two_pow
      (by omega : 3 ≤ m + 1) hM u hprefix z hne
    let s := v.map Fin.castSucc
    have hscard : s.card + 2 = m + 2 := by simp only [s, Multiset.card_map, hv]; omega
    have hxnot : x ∉ s := by
      intro hmem
      obtain ⟨k, _, hk⟩ := Multiset.mem_map.mp hmem
      exact Fin.castSucc_ne_last k hk
    have hsum : π ((s.map g).sum + 2 • g x) = π (∑ k, g k) := by
      rw [map_add]
      have hs : π ((s.map g).sum) = z := by
        simpa only [s, Multiset.map_map, Function.comp_def] using hvsum
      rw [hs]
      dsimp only [z]
      rw [map_sub]
      abel
    rcases eq_or_eq_add_half_of_castHom_eq _ _ hsum with heq | heq
    · have hc := multiset_count_eq_one_of_validTuple g hg (s + Multiset.replicate 2 x)
        (by simpa using hscard)
        (by simpa only [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
          Multiset.sum_replicate] using heq) x
      simp only [Multiset.count_add, Multiset.count_replicate_self] at hc
      omega
    · let w : Multiset (Fin (m + 2)) := s + {i.castSucc} + {j.castSucc}
      have hwcard : w.card = m + 2 := by
        simp only [w, Multiset.card_add, Multiset.card_singleton]
        omega
      have hwsum : (w.map g).sum = ∑ k, g k := by
        simp only [w, Multiset.map_add, Multiset.sum_add, Multiset.map_singleton,
          Multiset.sum_singleton]
        rw [hpair] at heq
        have : (s.map g).sum + g i.castSucc + g j.castSucc + M =
            (∑ k, g k) + M := by simpa only [add_assoc] using heq
        exact add_right_cancel this
      have hxw : x ∉ w := by
        simp only [w, Multiset.mem_add, Multiset.mem_singleton]
        exact fun h ↦ h.elim
          (fun h ↦ h.elim hxnot (fun h ↦ Fin.castSucc_ne_last i h.symm))
          (fun h ↦ Fin.castSucc_ne_last j h.symm)
      exact not_validTuple_of_multiset_omission g w hwcard hwsum x hxw hg
  have hz : z = ((2 ^ (m + 1) - (m + 1) : ℕ) : ZMod M) := by
    rw [← hhole, ZMod.natCast_zmod_val]
  have hpsum : (∑ k : Fin (m + 1), π (g k.castSucc)) =
      ((2 ^ (m + 1) - (m + 1) - 1 : ℕ) : ZMod M) := by
    dsimp only [π]
    simp only [hprefix]
    rw [← Nat.cast_sum, sum_fixed_eq_cover_hole]
  have hzsum : z = ((2 ^ (m + 1) - (m + 1) - 1 : ℕ) : ZMod M) - π (g x) := by
    dsimp only [z]
    rw [map_sub, Fin.sum_univ_castSucc, map_add, map_sum, hpsum, map_nsmul]
    change _ + π (g x) - 2 • π (g x) = _
    module
  have hnat : 2 ^ (m + 1) - (m + 1) = (2 ^ (m + 1) - (m + 1) - 1) + 1 := by
    have := Nat.lt_two_pow_self (n := m + 1)
    omega
  have hc := congrArg (fun k : ℕ ↦ (k : ZMod M)) hnat
  simp only [Nat.cast_add, Nat.cast_one] at hc
  change π (g x) = -1
  linear_combination hzsum - hz - hc

/-- The midpoint hole forces divisibility by a sum of two distinct powers
of two, placing the half modulus at most three quarters of the prefix's
binary range. -/
theorem two_mul_modulus_le_of_fixed_midpoint_neg_one
    {m M : ℕ} (hm : 1 ≤ m) (i j : Fin (m + 1)) (hij : i ≠ j)
    (hmid : (2 : ℕ) • (-1 : ZMod M) = (a i.val : ZMod M) + (a j.val : ZMod M)) :
    2 * M ≤ 3 * 2 ^ m := by
  have hp (k : Fin (m + 1)) : (a k.val : ZMod M) + 1 = ((2 ^ k.val : ℕ) : ZMod M) := by
    have hnat : a k.val + 1 = 2 ^ k.val := by
      have : 0 < 2 ^ k.val := by positivity
      unfold a
      omega
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun r : ℕ ↦ (r : ZMod M)) hnat
  have hz : ((2 ^ i.val + 2 ^ j.val : ℕ) : ZMod M) = 0 := by
    rw [Nat.cast_add, ← hp, ← hp]
    rw [two_nsmul] at hmid
    linear_combination -hmid
  have hd : M ∣ 2 ^ i.val + 2 ^ j.val := by
    rwa [ZMod.natCast_eq_zero_iff] at hz
  have hM := Nat.le_of_dvd (by positivity : 0 < 2 ^ i.val + 2 ^ j.val) hd
  have hpM : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hil : 2 ^ i.val ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
  have hjl : 2 ^ j.val ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
  have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
  have hsmall : i.val ≤ m - 1 ∨ j.val ≤ m - 1 := by omega
  rcases hsmall with hi | hj
  · have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hi
    omega
  · have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hj
    omega

/-- Every independent SI quotient-prefix midpoint extension satisfies the
binary lower bound, uniformly in all dimensions n>=5 and positive half
moduli. This is stronger than each exact stratum threshold. -/
theorem two_pow_le_of_valid_si_lift_prefix_midpoint
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (i j : Fin (m + 1)) (hij : i ≠ j)
    (hmid : 2 • ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) =
      (a i.val : ZMod M) + (a j.val : ZMod M)) :
    2 ^ (m + 2) ≤ 2 * M := by
  by_contra hnot
  have hp2 : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; norm_num; ring
  have hp1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
  have hM : M < 2 ^ (m + 1) := by omega
  have hx := eq_neg_one_of_valid_si_lift_prefix_midpoint (by omega) hM g hg hprefix i j hij hmid
  have hglobal := global_lower_bound_of_valid_si_lifts_neg_one hm g hg
    (fun k ↦ hprefix k.castSucc) hx
  have hlog := Nat.pow_log_le_self 2 (by omega : m + 2 ≠ 0)
  have harith := two_mul_modulus_le_of_fixed_midpoint_neg_one (by omega : 1 ≤ m) i j hij
    (by simpa only [hx] using hmid)
  have hlarge : m + 2 < 2 ^ m := by
    have hsmall := succ_le_two_pow_pred m hm
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  unfold globalBound at hglobal
  omega

/-- Reindexing and quotient affine transport preserve the midpoint binary
bound; neither an upstairs affine prefix nor coherent lift bits are needed. -/
theorem two_pow_le_of_valid_quotient_affine_si_prefix_midpoint
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ k : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e k.castSucc)) = φ (a k.val) + b)
    (i j : Fin (m + 1)) (hij : i ≠ j)
    (hmid : 2 • ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (Fin.last (m + 1)))) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i.castSucc)) +
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e j.castSucc))) :
    2 ^ (m + 2) ≤ 2 * M := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_lift_castHom (dvd_mul_left M 2) φ
  let B : ZMod (2 * M) := b.val
  let w := fun k ↦ Φ.symm (g (e k) - B)
  have hv := validTuple_sub_const (fun k ↦ g (e k)) (validTuple_embedding e.toEmbedding g hg) B
  have hw : ValidTuple w := validTuple_comp hv Φ.symm.toAddMonoidHom Φ.symm.injective
  have hpref : ∀ k : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (w k.castSucc) = (a k.val : ZMod M) := by
    intro k
    apply φ.injective
    rw [← hΦ, Φ.apply_symm_apply, map_sub, hprefix]
    simp [B]
  apply two_pow_le_of_valid_si_lift_prefix_midpoint hm w hw hpref i j hij
  apply φ.injective
  rw [map_nsmul, ← hΦ, Φ.apply_symm_apply, map_sub, map_add]
  have hB : ZMod.castHom (dvd_mul_left M 2) (ZMod M) B = b := by simp [B]
  rw [hB, smul_sub, hmid, hprefix, hprefix]
  module

/-- Every exact stratum bound follows for this independently lifted class.
The parameter t need not even be the actual valuation. -/
theorem stratum_lower_bound_of_valid_quotient_affine_si_prefix_midpoint
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ k : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e k.castSucc)) = φ (a k.val) + b)
    (i j : Fin (m + 1)) (hij : i ≠ j)
    (hmid : 2 • ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (Fin.last (m + 1)))) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i.castSucc)) +
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e j.castSucc)))
    (t : ℕ) : stratumBound (m + 2) t ≤ 2 * M :=
  (Nat.sub_le _ _).trans
    (two_pow_le_of_valid_quotient_affine_si_prefix_midpoint hm g hg e φ b hprefix i j hij hmid)

/-- Direct exclusion at any critical even stratum, without a half-witness,
common-touch, overlap, or unrestricted G1 hypothesis. -/
theorem not_validTuple_of_critical_quotient_affine_si_prefix_midpoint
    {m M t : ℕ} [NeZero M] (hm : 3 ≤ m)
    (hcritical : 2 * M < stratumBound (m + 2) t)
    (g : Fin (m + 2) → ZMod (2 * M))
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ k : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e k.castSucc)) = φ (a k.val) + b)
    (i j : Fin (m + 1)) (hij : i ≠ j)
    (hmid : 2 • ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (Fin.last (m + 1)))) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e i.castSucc)) +
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e j.castSucc))) : ¬ ValidTuple g := by
  intro hg
  exact (not_lt_of_ge
    (stratum_lower_bound_of_valid_quotient_affine_si_prefix_midpoint hm g hg e φ b
      hprefix i j hij hmid t)) hcritical

end MinModulus
