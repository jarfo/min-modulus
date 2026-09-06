/-
# A quarter-offset extra excludes independent shorter SI lifts

The m-fold quotient sumset of the first m SI entries together with H+1
in ZMod (2*H) misses at most H+1+(2^m-m), provided H <= 2^m-2.
Upstairs, two copies of the extra and two copies of the lifted one form
an antipodal pair, independently of every lift bit. Adding that pair
gives a full-length rival unless the other extra reduces to 3. At the
exceptional modulus this last case is an actual quotient collision and
is already excluded. No finite census or unrestricted global gate is used.
-/
import MinModulus.SITwoMultiplierStrata
import MinModulus.SIQuotientCollision

namespace MinModulus
open Finset

/-- One quarter-offset coin leaves at most one hole in the m-term
quotient sumset. This is a uniform cover, not a validity assumption. -/
theorem exists_multiset_sum_of_fixed_prefix_quarter_extra_except_hole
    {m M H : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M = 2 * H)
    (hH : H ≤ 2 ^ m - 2) (u : Fin (m + 1) → ZMod M)
    (hu : ∀ i : Fin m, u i.castSucc = (a i.val : ZMod M))
    (hq : u (Fin.last m) = (H + 1 : ℕ))
    (z : ZMod M) (hne : z ≠ ((H + 1 : ℕ) : ZMod M) + ((2 ^ m - m : ℕ) : ZMod M)) :
    ∃ s : Multiset (Fin (m + 1)), s.card = m ∧ (s.map u).sum = z := by
  classical
  have hp := Nat.lt_two_pow_self (n := m - 1)
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hlarge := succ_le_two_pow_pred m hm
  have hz := z.val_lt
  have mapped (K r : ℕ) (s : Multiset (Fin m)) (hs : s.card = K)
      (hval : (s.map (fun i ↦ (a i.val : ZMod M))).sum = (r : ZMod M)) :
      (s.map Fin.castSucc).card = K ∧ ((s.map Fin.castSucc).map u).sum = (r : ZMod M) := by
    constructor
    · simpa using hs
    · simpa only [Multiset.map_map, Function.comp_def, hu] using hval
  by_cases hlow : z.val < H + 1
  · obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt
      (by omega : 1 ≤ m - 1) 1 z.val (by omega)
    obtain ⟨v, hv, hvsum⟩ := exists_fixed_multiset_sum_of_nat_coin_representation_card
      (m := m) (N := M) (K := m) (by omega) s (by omega)
      (fun i hi ↦ by have := hmem i hi; omega) hsum
    obtain ⟨hcard, hval⟩ := mapped m z.val v hv hvsum
    exact ⟨v.map Fin.castSucc, hcard, by simpa using hval⟩
  · let r := z.val - (H + 1)
    have hr : r < 2 * (2 ^ (m - 1) - 1) := by dsimp [r]; omega
    have hsumNat : H + 1 + r = z.val := by dsimp [r]; omega
    have hrne : r ≠ 2 * (2 ^ (m - 1) - 1) - ((m - 1) - 1) := by
      intro heq
      apply hne
      have hrF : r = 2 ^ m - m := by omega
      have hc := congrArg (fun k : ℕ ↦ (k : ZMod M)) hsumNat
      rw [hrF] at hc
      simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hc.symm
    obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt_two_mul
      (by omega : 1 ≤ m - 1) r hr hrne
    obtain ⟨v, hv, hvsum⟩ := exists_fixed_multiset_sum_of_nat_coin_representation_card
      (m := m) (N := M) (K := m - 1) (by omega) s hs
      (fun i hi ↦ by have := hmem i hi; omega) hsum
    obtain ⟨hcard, hval⟩ := mapped (m - 1) r v hv hvsum
    refine ⟨Fin.last m ::ₘ v.map Fin.castSucc, ?_, ?_⟩
    · simp only [Multiset.card_cons, hcard]; omega
    · rw [Multiset.map_cons, Multiset.sum_cons, hq, hval, ← Nat.cast_add, hsumNat]
      exact ZMod.natCast_zmod_val z

/-- A quotient displacement H from the lifted one gives a two-term
antipodal pair in ZMod (2*M), where M=2*H. -/
theorem two_nsmul_quarter_extra_eq_two_nsmul_one_add_half
    {M H : ℕ} [NeZero M] (hM : M = 2 * H)
    (x one : ZMod (2 * M))
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) x = (H + 1 : ℕ))
    (hone : ZMod.castHom (dvd_mul_left M 2) (ZMod M) one = 1) :
    2 • x = 2 • one + M := by
  have hx' : 2 • x = 2 • ((H + 1 : ℕ) : ZMod (2 * M)) :=
    nsmul_eq_of_even_of_castHom_eq (by decide : Even 2) _ _
      (by simpa only [map_natCast] using hx)
  have ho' : 2 • one = 2 • (1 : ZMod (2 * M)) :=
    nsmul_eq_of_even_of_castHom_eq (by decide : Even 2) _ _
      (by simpa only [map_one] using hone)
  rw [hx', ho', hM]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, nsmul_eq_mul]
  ring

/-- Arbitrary shorter-prefix lift bits and a quarter-offset extra force
a rival unless the other extra actually collides with the lifted 3. -/
theorem not_validTuple_of_si_lifts_quarter_extra_of_last_ne_three
    {m M H : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M = 2 * H)
    (hH : H ≤ 2 ^ m - 2) (g : Fin (m + 2) → ZMod (2 * M))
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc.castSucc) = (a i.val : ZMod M))
    (hq : ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (Fin.last m).castSucc) = (H + 1 : ℕ))
    (hy : ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (Fin.last (m + 1))) ≠ 3) : ¬ ValidTuple g := by
  classical
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let u : Fin (m + 1) → ZMod (2 * M) := fun i ↦ g i.castSucc
  let one : Fin (m + 1) := (⟨1, by omega⟩ : Fin m).castSucc
  let X := ∑ i, g i
  have hone : π (u one) = 1 := by
    exact (hprefix ⟨1, by omega⟩).trans (by norm_num [a])
  have hpair : 2 • u (Fin.last m) = 2 • u one + M :=
    two_nsmul_quarter_extra_eq_two_nsmul_one_add_half hM _ _ hq hone
  have hsum : π X = ((2 ^ m - m - 1 : ℕ) : ZMod M) +
      ((H + 1 : ℕ) : ZMod M) + π (g (Fin.last (m + 1))) := by
    dsimp only [X]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, map_add, map_add]
    rw [map_sum, hq]
    congr 2
    simp only [π, hprefix]
    rw [← Nat.cast_sum, sum_fixed_eq_cover_hole]
  have hF : ((2 ^ m - m - 1 : ℕ) : ZMod M) + 1 = ((2 ^ m - m : ℕ) : ZMod M) := by
    have hn : (2 ^ m - m - 1) + 1 = 2 ^ m - m := by
      have := Nat.lt_two_pow_self (n := m); omega
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ ↦ (k : ZMod M)) hn
  have hne : π (X - 2 • u one) ≠
      ((H + 1 : ℕ) : ZMod M) + ((2 ^ m - m : ℕ) : ZMod M) := by
    intro heq
    apply hy
    change π (g (Fin.last (m + 1))) = 3
    rw [map_sub, map_nsmul, hone, hsum, ← hF] at heq
    simp only [nsmul_eq_mul] at heq
    linear_combination heq
  obtain ⟨s, hs, hproj⟩ := exists_multiset_sum_of_fixed_prefix_quarter_extra_except_hole
    hm hM hH (fun i ↦ π (u i)) hprefix hq (π (X - 2 • u one)) hne
  have hproj' : π ((s.map u).sum + 2 • u one) = π X := by
    rw [map_add, map_multiset_sum, Multiset.map_map]
    change (s.map (fun i ↦ π (u i))).sum + π (2 • u one) = π X
    rw [hproj, map_sub]
    abel
  obtain ⟨v, hv, hvsum⟩ := exists_multiset_sum_of_antipodal_coin_pair u one (Fin.last m)
    hpair s (by omega : s.card + 2 = m + 2) X hproj'
  apply not_validTuple_of_multiset_omission g (v.map Fin.castSucc)
    (by simpa using hv) (by simpa only [u, Multiset.map_map, Function.comp_def] using hvsum)
    (Fin.last (m + 1))
  intro hmem
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
  exact Fin.castSucc_ne_last i hi

/-- At G3, the lone uncovered target is excluded by an actual quotient
collision. Every independent lift bit and the other extra are arbitrary. -/
theorem not_validTuple_exceptional_of_si_lifts_quarter_extra
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g i.castSucc.castSucc) = (a i.val : ZMod (globalBound (m + 1))))
    (hq : ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
      (g (Fin.last m).castSucc) = ((globalBound (m + 1) / 2 + 1 : ℕ) : ZMod (globalBound (m + 1)))) :
    ¬ ValidTuple g := by
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (globalBound (m + 1)) := ⟨by omega⟩
  let π := ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
  by_cases hy : π (g (Fin.last (m + 1))) = 3
  · let k : Fin (m + 2) := (⟨2, by omega⟩ : Fin m).castSucc.castSucc
    apply not_validTuple_exceptional_of_last_collision_scaled_short_prefix hm hnpow g
      (Equiv.refl _) 1 0 k
      (Fin.castSucc_ne_last ((⟨2, by omega⟩ : Fin m).castSucc))
    · change π (g k) = π (g (Fin.last (m + 1)))
      rw [hy]
      exact (hprefix ⟨2, by omega⟩).trans (by norm_num [a])
    · intro i
      simpa only [Equiv.refl_apply, one_mul, add_zero] using hprefix i
  · have ht : 2 ≤ Nat.log 2 (m + 1) :=
      (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by norm_num; omega)
    have hD := Nat.pow_log_le_self 2 (show m + 1 ≠ 0 by omega)
    have hp := Nat.lt_two_pow_self (n := m)
    have hmPow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
    have htPow : 2 ^ Nat.log 2 (m + 1) = 2 * 2 ^ (Nat.log 2 (m + 1) - 1) := by
      rw [← pow_succ']; congr 1; omega
    have htLower : 2 ≤ 2 ^ (Nat.log 2 (m + 1) - 1) := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ Nat.log 2 (m + 1) - 1)
    have hM : globalBound (m + 1) = 2 * (globalBound (m + 1) / 2) := by
      unfold globalBound
      omega
    have hH : globalBound (m + 1) / 2 ≤ 2 ^ m - 2 := by
      unfold globalBound
      omega
    exact not_validTuple_of_si_lifts_quarter_extra_of_last_ne_three hm hM hH g hprefix hq hy

/-- Quotient affine transport and arbitrary reindexing preserve the
quarter-offset obstruction; no upstairs coherence is required. -/
theorem not_validTuple_exceptional_of_quotient_affine_short_prefix_quarter_extra
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (e : Equiv.Perm (Fin (m + 2)))
    (φ : ZMod (globalBound (m + 1)) ≃+ ZMod (globalBound (m + 1)))
    (b : ZMod (globalBound (m + 1)))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g (e i.castSucc.castSucc)) = φ (a i.val) + b)
    (hq : ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
      (g (e (Fin.last m).castSucc)) = φ ((globalBound (m + 1) / 2 + 1 : ℕ) : ZMod (globalBound (m + 1))) + b) :
    ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (globalBound (m + 1)) := ⟨by omega⟩
  letI : NeZero (2 * globalBound (m + 1)) := ⟨by omega⟩
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_lift_castHom (dvd_mul_left (globalBound (m + 1)) 2) φ
  let B : ZMod (2 * globalBound (m + 1)) := b.val
  have hv := validTuple_sub_const (fun i ↦ g (e i)) (validTuple_embedding e.toEmbedding g hg) B
  have hw := validTuple_comp hv Φ.symm.toAddMonoidHom Φ.symm.injective
  apply not_validTuple_exceptional_of_si_lifts_quarter_extra hm hnpow
    (fun i ↦ Φ.symm (g (e i) - B)) _ _ hw
  · intro i
    apply φ.injective
    rw [← hΦ, Φ.apply_symm_apply, map_sub, hprefix]
    simp [B]
  · apply φ.injective
    rw [← hΦ, Φ.apply_symm_apply, map_sub, hq]
    simp [B]

end MinModulus
