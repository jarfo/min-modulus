/-
# Exact stratum bounds for coherent SI-prefix extensions

The single-hole prefix cover extends through modulus 2^n-3. At these
moduli, a valid n-tuple containing the first n-1 SI entries must be the
complete fixed set. Separately, validity of the fixed set below 2^n forces
a power-gap modulus 2^n-2^t. Minimality and valuation bound t by both
floor(log₂ n) and the ambient two-adic valuation.

This proves the full stratum bound for coherent affine SI-prefix
extensions, with direct critical-G1 and odd-G2 consumers. The existing
G3 consumer remains available. The prefix is in the full modulus, with
unit scaling, translation and reindexing allowed; independent half-modulus
shifts are not included. No unrestricted G1/G2/G3 input is assumed or proved.
-/
import MinModulus.SIExtensionBound

namespace MinModulus
open Finset

/-- Below the full binary range, a valid fixed set can occur only at a
power-gap modulus. This is a necessary condition, not just minimality. -/
theorem exists_power_gap_of_valid_fixed_lt_two_pow
    {n N : ℕ} (hn : 3 ≤ n) (hN : 2 ≤ N) (hupper : N < 2 ^ n)
    (hv : Valid n N) : ∃ t < n, N = 2 ^ n - 2 ^ t := by
  have hbound := (nmin_eq (by omega : 2 ≤ n)).2 ⟨hN, hv⟩
  have hlog := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hnsmall := succ_le_two_pow_pred n hn
  have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hhalf : 2 ^ (n - 1) ≤ N := by omega
  by_cases heq : N = 2 ^ (n - 1)
  · exact ⟨n - 1, by omega, by omega⟩
  have hgap : 2 ^ n - N < 2 ^ (n - 1) := by omega
  have hex : ∃ t, 2 ^ n - N = 2 ^ t := by
    by_contra hnot
    obtain ⟨k, hs, hkval, hkdsum⟩ :=
      exists_rep_compl (n - 1) (2 ^ n - N) hgap (by omega) hnot
    obtain ⟨_, hval, hdsum⟩ := update_top (n - 1) 3 k hs
    rw [show n - 1 + 1 = n by omega, hkval] at hval
    rw [show n - 1 + 1 = n by omega] at hdsum
    have hbase : ∃ k, val n k = 2 ^ n - 1 + N ∧ dsum n k ≤ n :=
      ⟨Function.update k (n - 1) 3, by omega, by omega⟩
    have hnlt := Nat.lt_two_pow_self (n := n)
    apply not_valid_of_witness (by omega) (by omega) _
      (exists_dsum_eq hbase (by omega)) hv
    have hmod : N * 1 + (2 ^ n - 1) ≡ 2 ^ n - 1 [MOD N] :=
      Nat.ModEq.modulus_mul_add
    simpa only [mul_one, Nat.add_comm] using hmod
  obtain ⟨t, ht⟩ := hex
  have htn : t < n := by
    by_contra hnot
    have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : n ≤ t)
    omega
  exact ⟨t, htn, by omega⟩

/-- The fixed set satisfies the exact lower bound in every valuation. -/
theorem stratum_lower_bound_of_valid_fixed
    {n s q : ℕ} (hn : 3 ≤ n) (hq : Odd q) (hv : Valid n (2 ^ s * q)) :
    stratumBound n s ≤ 2 ^ s * q := by
  have hpos := hq.pos
  have hNpos : 0 < 2 ^ s * q := by positivity
  have hgapPos : 0 < 2 ^ min s (Nat.log 2 n) := by positivity
  letI : NeZero (2 ^ s * q) := ⟨ne_of_gt hNpos⟩
  have htup := validTuple_fixed_of_valid hv
  have hcard := Fintype.card_le_of_injective _ (validTuple_injective _ htup)
  simp only [Fintype.card_fin, ZMod.card] at hcard
  by_contra hnot
  have hupper : 2 ^ s * q < 2 ^ n := by
    unfold stratumBound at hnot
    omega
  obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_fixed_lt_two_pow hn (by omega) hupper hv
  have hbound := (nmin_eq (by omega : 2 ≤ n)).2 ⟨by omega, hv⟩
  have htlog : t ≤ Nat.log 2 n := by
    apply (pow_le_pow_iff_right₀ (by omega : 1 < (2 : ℕ))).mp
    have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) ht.le
    rw [hgap] at hbound
    omega
  have htwodvd : 2 ^ t ∣ 2 ^ s * q := by
    rw [hgap]
    exact Nat.dvd_sub (pow_dvd_pow 2 ht.le) (dvd_refl _)
  have hts : t ≤ s := by
    by_contra hnot
    have hstep : 2 ^ s * 2 ∣ 2 ^ s * q := by
      rw [← pow_succ]
      exact (pow_dvd_pow 2 (by omega : s + 1 ≤ t)).trans htwodvd
    exact hq.not_two_dvd_nat (Nat.dvd_of_mul_dvd_mul_left (by positivity) hstep)
  have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (le_min hts htlog)
  unfold stratumBound at hnot
  omega

/-- The prefix cover extends to every modulus at most `2^n-3`, not just
those below the global envelope. Its sole possible hole is the fixed sum. -/
theorem exists_fixed_multiset_sum_except_hole_of_modulus_le
    {m N : ℕ} [NeZero N] (hm : 2 ≤ m) (hN : N ≤ 2 ^ (m + 1) - 3)
    (x : ZMod N) (hne : x.val ≠ 2 ^ (m + 1) - m - 2) :
    ∃ s : Multiset (Fin m), s.card = m + 1 ∧
      (s.map (fun i ↦ (a i.val : ZMod N))).sum = x := by
  have hx := x.val_lt
  have hcoins : ∃ s : Multiset ℕ, s.card ≤ m + 1 ∧
      (∀ i ∈ s, i < m) ∧ (s.map a).sum = x.val := by
    by_cases hm2 : m = 2
    · subst m
      norm_num at hN hne
      obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt
        (by omega : 1 ≤ 1) 2 x.val (by norm_num; omega)
      exact ⟨s, hs, fun i hi ↦ by have := hmem i hi; omega, hsum⟩
    · have hm3 : 3 ≤ m := by omega
      have hpow : 2 ^ (m + 1) = 4 * 2 ^ (m - 1) := by
        rw [show m + 1 = (m - 1) + 2 by omega, pow_add]
        ring
      have hp := Nat.lt_two_pow_self (n := m - 1)
      have hxle : x.val ≤ 4 * (2 ^ (m - 1) - 1) := by omega
      rcases hxle.eq_or_lt with heq | hlt
      · refine ⟨Multiset.replicate 4 (m - 1), by simp; omega, ?_, ?_⟩
        · intro i hi
          have := (Multiset.mem_replicate.mp hi).2
          omega
        · simp [a]
          omega
      · have hne' : x.val ≠ 4 * (2 ^ (m - 1) - 1) - (m - 1 - 1) := by omega
        obtain ⟨s, hs, hmem, hsum⟩ :=
          exists_mersenne_coin_multiset_of_lt_four_mul (by omega : 1 ≤ m - 1) x.val hlt hne'
        exact ⟨s, by omega, fun i hi ↦ by have := hmem i hi; omega, hsum⟩
  obtain ⟨s, hs, hmem, hsum⟩ := hcoins
  exact exists_fixed_multiset_sum_of_nat_coin_representation (by omega) x s hs hmem hsum

/-- At these moduli, validity forces the arbitrary last entry to be the
missing SI entry. This is an extraction conclusion, not a hypothesis. -/
theorem eq_fixed_of_valid_fixed_prefix_of_modulus_le
    {m N : ℕ} [NeZero N] (hm : 2 ≤ m) (hN : N ≤ 2 ^ (m + 1) - 3)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc = (a i.val : ZMod N)) :
    g = fun i ↦ (a i.val : ZMod N) := by
  classical
  let x := ∑ i, g i
  have hx : x.val = 2 ^ (m + 1) - m - 2 := by
    by_contra hne
    obtain ⟨s, hcard, hsum⟩ := exists_fixed_multiset_sum_except_hole_of_modulus_le hm hN x hne
    let t := s.map Fin.castSucc
    have htcard : t.card = m + 1 := by simpa only [t, Multiset.card_map] using hcard
    have htsum : (t.map g).sum = ∑ i, g i := by
      simpa only [t, Multiset.map_map, Function.comp_def, hprefix] using hsum
    have hnot : Fin.last m ∉ t := by
      intro hmem
      obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
      have heq := congrArg Fin.val hi
      simp only [Fin.val_castSucc, Fin.val_last] at heq
      omega
    have hz := Multiset.count_eq_zero.mpr hnot
    have ho := multiset_count_eq_one_of_validTuple g hg t htcard htsum (Fin.last m)
    omega
  have hsum : (∑ i, g i) = ∑ i : Fin (m + 1), (a i.val : ZMod N) := by
    rw [← Nat.cast_sum, sum_fixed_eq_cover_hole]
    have hxcast : x = (x.val : ZMod N) := (ZMod.natCast_zmod_val x).symm
    change x = ((2 ^ (m + 1) - (m + 1) - 1 : ℕ) : ZMod N)
    rw [hxcast, hx]
    congr 1
  have hlast : g (Fin.last m) = (a m : ZMod N) := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hsum
    simpa only [hprefix, Fin.val_castSucc, Fin.val_last, add_right_inj] using hsum
  funext i
  exact Fin.lastCases hlast (fun j ↦ hprefix j) i

/-- The exact stratum bound for an SI prefix with an arbitrary extra entry. -/
theorem stratum_lower_bound_of_valid_fixed_prefix
    {m s q : ℕ} (hm : 2 ≤ m) (hq : Odd q)
    (g : Fin (m + 1) → ZMod (2 ^ s * q)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc = (a i.val : ZMod (2 ^ s * q))) :
    stratumBound (m + 1) s ≤ 2 ^ s * q := by
  have hqpos := hq.pos
  have hNpos : 0 < 2 ^ s * q := by positivity
  letI : NeZero (2 ^ s * q) := ⟨ne_of_gt hNpos⟩
  by_contra hnot
  have hN : 2 ^ s * q ≤ 2 ^ (m + 1) - 3 := by
    by_cases hs : s = 0
    · subst s
      simp only [stratumBound, Nat.zero_min, pow_zero, one_mul] at hnot ⊢
      obtain ⟨r, hr⟩ := hq
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
      omega
    · have hlog : 1 ≤ Nat.log 2 (m + 1) := by
        apply (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr
        norm_num
        omega
      have hdelta : 2 ≤ 2 ^ min s (Nat.log 2 (m + 1)) := by
        simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ))
          (le_min (by omega : 1 ≤ s) hlog)
      unfold stratumBound at hnot
      omega
  have hfull := eq_fixed_of_valid_fixed_prefix_of_modulus_le hm hN g hg hprefix
  have hv : Valid (m + 1) (2 ^ s * q) := valid_fixed_of_validTuple (hfull ▸ hg)
  exact hnot (stratum_lower_bound_of_valid_fixed (by omega) hq hv)

/-- Affine normalization preserves the exact SI-extension stratum bound. -/
theorem stratum_lower_bound_of_valid_affine_fixed_prefix
    {m s q : ℕ} (hm : 2 ≤ m) (hq : Odd q)
    (g : Fin (m + 1) → ZMod (2 ^ s * q)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 1)))
    (φ : ZMod (2 ^ s * q) ≃+ ZMod (2 ^ s * q)) (b : ZMod (2 ^ s * q))
    (hprefix : ∀ i : Fin m, g (e i.castSucc) = φ (a i.val) + b) :
    stratumBound (m + 1) s ≤ 2 ^ s * q := by
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) b
  have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
  exact stratum_lower_bound_of_valid_fixed_prefix hm hq (fun i ↦ φ.symm (g (e i) - b)) hw
    (by intro i; simp [hprefix])

/-- This class cannot supply a critical G1 tuple, regardless of its
half-witness family or its overlap profile. -/
theorem not_validTuple_of_critical_affine_fixed_prefix
    {m s q : ℕ} (hm : 2 ≤ m) (hq : Odd q)
    (hcritical : 2 ^ s * q < stratumBound (m + 1) s)
    (g : Fin (m + 1) → ZMod (2 ^ s * q)) (e : Equiv.Perm (Fin (m + 1)))
    (φ : ZMod (2 ^ s * q) ≃+ ZMod (2 ^ s * q)) (b : ZMod (2 ^ s * q))
    (hprefix : ∀ i : Fin m, g (e i.castSucc) = φ (a i.val) + b) : ¬ ValidTuple g := by
  intro hg
  exact (not_lt_of_ge
    (stratum_lower_bound_of_valid_affine_fixed_prefix hm hq g hg e φ b hprefix)) hcritical

/-- The full odd G2 threshold for a coherent SI prefix and arbitrary extra
entry in every dimension at least three. The unrestricted G2 stays open. -/
theorem odd_lower_bound_of_valid_affine_fixed_prefix
    {m N : ℕ} (hm : 2 ≤ m) (hN : Odd N)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 1))) (φ : ZMod N ≃+ ZMod N) (b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc) = φ (a i.val) + b) :
    2 ^ (m + 1) - 1 ≤ N := by
  have h := stratum_lower_bound_of_valid_affine_fixed_prefix (s := 0) hm hN
  rw [show (2 : ℕ) ^ 0 * N = N by simp] at h
  simpa [stratumBound] using h g hg e φ b hprefix

end MinModulus
