/-
# Exact strata and full SI extraction for two-extra coherent prefixes

The two-extra global bound strengthens to the actual G1/G2 stratum
thresholds for a coherent unit-affine SI prefix of length n-2, n>=5.
Below 2^n, validity forces N=2^n-2^t; the preceding global bound and
the actual two-adic valuation separately bound t by log2(n) and v2(N).

For n>=7 and N<=2^n-3, the proof extracts the full SI tuple with the same
affine map after reindexing. The one-extra cover localizes both extras
unless one is the missing SI entry. Close extras give a doubled-extra
rival; wrapped far extras give a prefix-only rival. The new near-wrap
case gives a rival with three copies of the smaller extra. Thus one
extra must complete the longer prefix, which forces full completion.

The two top binary residues are already power gaps. Dimensions five
and six use the existing kernel-checked odd base theorems alongside
the preceding two-extra global bound; no new census is performed.

No unrestricted G1/G2/G3 assumption is used. Full-modulus coherence
and unit scaling remain essential hypotheses, not extraction claims
about arbitrary tuples or arbitrary independent half-modulus lifts.
-/
import MinModulus.SITwoExtensionBound
import MinModulus.SIMultiplierStrata
import MinModulus.SHCFiveBaseCases

namespace MinModulus
open Finset

/-- The largest retained coin absorbs the slightly larger loss needed
for exact strata, not merely the numerical global envelope. -/
theorem three_mul_sub_one_le_mersenne_pred {m : ℕ} (hm : 5 ≤ m) :
    3 * m - 1 ≤ 2 ^ (m - 1) - 1 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hp := Nat.lt_two_pow_self (n := m - 1)
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    simp only [Nat.add_sub_cancel]
    omega

/-- The localized two-extra obstruction extends through `2^n-3`.
The additional near-wrap case is repaired by tripling the smaller extra. -/
theorem not_validTuple_of_localized_fixed_short_prefix_near_binary
    {m N : ℕ} [NeZero N] (hm : 5 ≤ m)
    (hN : N ≤ 8 * (2 ^ (m - 1) - 1) + 5)
    (g : Fin (m + 2) → ZMod N) (f : Fin m ↪ Fin (m + 2))
    (hprefix : ∀ i, g (f i) = (a i.val : ZMod N))
    (x y : Fin (m + 2)) (hx : ∀ i, f i ≠ x) (hy : ∀ i, f i ≠ y)
    (hsum : (∑ i, g i) = ((2 ^ m - m - 1 : ℕ) : ZMod N) + g x + g y)
    (hxlo : 4 * (2 ^ (m - 1) - 1) + 1 ≤ (2 ^ m - m - 1) + (g x).val)
    (hylo : 4 * (2 ^ (m - 1) - 1) + 1 ≤ (2 ^ m - m - 1) + (g y).val)
    (_hxhi : (2 ^ m - m - 1) + (g x).val < N)
    (hyhi : (2 ^ m - m - 1) + (g y).val < N)
    (hxy : (g x).val ≤ (g y).val) : ¬ ValidTuple g := by
  have hp := Nat.lt_two_pow_self (n := m - 1)
  have hlarge := three_mul_sub_one_le_mersenne_pred hm
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  let S := 2 ^ m - m - 1
  let X := (g x).val
  let Y := (g y).val
  by_cases hclose : Y ≤ S + X
  · let r := S + X - Y
    have hr : r + Y = S + X := by dsimp [r]; omega
    have hrbound : r < (1 + 2) * (2 ^ (m - 1) - 1) - (m - 2) := by
      dsimp [r, S, X, Y] at *; omega
    apply not_validTuple_of_fixed_block_rival g f hprefix y hy
      (by omega : 2 ≠ 1) (by omega : (m - 1 + 1) + 2 = m + 2)
      (exists_fixed_multiset_sum_of_lt_initial_interval (by omega) hrbound)
    have hz := congrArg (fun k : ℕ ↦ (k : ZMod N)) hr
    simp only [Nat.cast_add, X, Y, ZMod.natCast_zmod_val] at hz
    rw [hsum, ← hz]
    simp only [two_nsmul]
    abel
  · by_cases hwrap : N ≤ S + X + Y
    · let r := S + X + Y - N
      have hr : r + N = S + X + Y := by dsimp [r]; omega
      have hrbound : r < (3 + 2) * (2 ^ (m - 1) - 1) - (m - 2) := by
        dsimp [r, S, X, Y] at *; omega
      apply not_validTuple_of_fixed_block_rival g f hprefix y hy
        (by omega : 0 ≠ 1) (by omega : (m - 1 + 3) + 0 = m + 2)
        (exists_fixed_multiset_sum_of_lt_initial_interval (by omega) hrbound)
      have hz := congrArg (fun k : ℕ ↦ (k : ZMod N)) hr
      simpa only [Nat.cast_add, ZMod.natCast_self, add_zero,
        X, Y, ZMod.natCast_zmod_val, zero_nsmul, hsum, S] using hz
    · let r := S + Y - 2 * X
      have hr : r + 2 * X = S + Y := by dsimp [r, S, X, Y] at *; omega
      have hrbound : r < (0 + 2) * (2 ^ (m - 1) - 1) - (m - 2) := by
        dsimp [r, S, X, Y] at *; omega
      apply not_validTuple_of_fixed_block_rival g f hprefix x hx
        (by omega : 3 ≠ 1) (by omega : (m - 1 + 0) + 3 = m + 2)
        (exists_fixed_multiset_sum_of_lt_initial_interval (by omega) hrbound)
      have hz := congrArg (fun k : ℕ ↦ (k : ZMod N)) hr
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, X, Y,
        ZMod.natCast_zmod_val] at hz
      rw [hsum]
      change (r : ZMod N) + 3 • g x = (S : ZMod N) + g x + g y
      simp only [nsmul_eq_mul]
      linear_combination hz

/-- Below the last two binary residues, validity extracts the next SI
entry from the two arbitrary extras. No global conjecture is assumed. -/
theorem exists_tail_eq_next_of_valid_fixed_short_prefix
    {m N : ℕ} [NeZero N] (hm : 5 ≤ m)
    (hN : N ≤ 2 ^ (m + 2) - 3)
    (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = (a i.val : ZMod N)) :
    g (Fin.last m).castSucc = (a m : ZMod N) ∨
      g (Fin.last (m + 1)) = (a m : ZMod N) := by
  by_contra hc
  have hbinary := two_pow_pred_le_card_of_validTuple g hg
  simp only [ZMod.card, show m + 2 - 1 = m + 1 by omega] at hbinary
  have hp := Nat.lt_two_pow_self (n := m - 1)
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpow1 : 2 ^ (m + 1) = 4 * 2 ^ (m - 1) := by rw [pow_succ', hpow]; ring
  have hpow2 : 2 ^ (m + 2) = 8 * 2 ^ (m - 1) := by
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ', hpow1]; ring
  have hNlo : 4 * (2 ^ (m - 1) - 1) + 4 ≤ N := by omega
  have hNhi : N ≤ 8 * (2 ^ (m - 1) - 1) + 5 := by omega
  let x : Fin (m + 2) := (Fin.last m).castSucc
  let y : Fin (m + 2) := Fin.last (m + 1)
  let f : Fin m ↪ Fin (m + 2) :=
    ⟨fun i ↦ i.castSucc.castSucc,
      (Fin.castSucc_injective (m + 1)).comp (Fin.castSucc_injective m)⟩
  have hvx := validTuple_fixed_prefix_with_tail_coordinate g hg hprefix x (by simp [x])
  have hvy := validTuple_fixed_prefix_with_tail_coordinate g hg hprefix y (by simp [y])
  have hx := fixed_prefix_extra_localization (by omega) hNlo
    (Fin.lastCases (g x) (fun i : Fin m ↦ (a i.val : ZMod N))) hvx
    (by intro i; simp) (by simpa only [Fin.lastCases_last] using not_or.mp hc |>.1)
  have hy := fixed_prefix_extra_localization (by omega) hNlo
    (Fin.lastCases (g y) (fun i : Fin m ↦ (a i.val : ZMod N))) hvy
    (by intro i; simp) (by simpa only [Fin.lastCases_last] using not_or.mp hc |>.2)
  simp only [Fin.lastCases_last] at hx hy
  have hfx : ∀ i, f i ≠ x := by
    intro i heq
    have hv := congrArg Fin.val heq
    simp only [f, x, Fin.val_castSucc, Fin.val_last, Function.Embedding.coeFn_mk] at hv
    omega
  have hfy : ∀ i, f i ≠ y := by
    intro i heq
    have hv := congrArg Fin.val heq
    simp only [f, y, Fin.val_castSucc, Fin.val_last, Function.Embedding.coeFn_mk] at hv
    omega
  have hsum : (∑ i, g i) = ((2 ^ m - m - 1 : ℕ) : ZMod N) + g x + g y := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [hprefix, ← Nat.cast_sum, sum_fixed_eq_cover_hole, x, y]
  rcases le_total (g x).val (g y).val with hxy | hyx
  · exact not_validTuple_of_localized_fixed_short_prefix_near_binary hm hNhi
      g f hprefix x y hfx hfy hsum hx.1 hy.1 hx.2 hy.2 hxy hg
  · exact not_validTuple_of_localized_fixed_short_prefix_near_binary hm hNhi
      g f hprefix y x hfy hfx (by rw [hsum]; abel) hy.1 hx.1 hy.2 hx.2 hyx hg

/-- The extracted next entry completes the whole fixed set after at most
swapping the two extras. This is full tuple extraction, not a new input. -/
theorem exists_perm_fixed_of_valid_fixed_short_prefix_of_modulus_le
    {m N : ℕ} [NeZero N] (hm : 5 ≤ m)
    (hN : N ≤ 2 ^ (m + 2) - 3)
    (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = (a i.val : ZMod N)) :
    ∃ p : Equiv.Perm (Fin (m + 2)), ∀ i, g (p i) = (a i.val : ZMod N) := by
  obtain hnext | hnext := exists_tail_eq_next_of_valid_fixed_short_prefix hm hN g hg hprefix
  · have hlong : ∀ i : Fin (m + 1), g i.castSucc = (a i.val : ZMod N) := by
      intro i
      exact Fin.lastCases hnext (fun k ↦ hprefix k) i
    have hfull := eq_fixed_of_valid_fixed_prefix_of_modulus_le (by omega) hN g hg hlong
    exact ⟨Equiv.refl _, fun i ↦ congrFun hfull i⟩
  · let x : Fin (m + 2) := (Fin.last m).castSucc
    let y : Fin (m + 2) := Fin.last (m + 1)
    let p := Equiv.swap x y
    have hfix (i : Fin m) : p i.castSucc.castSucc = i.castSucc.castSucc := by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro heq
        have hv := congrArg Fin.val heq
        simp only [x, Fin.val_castSucc, Fin.val_last] at hv
        omega
      · intro heq
        have hv := congrArg Fin.val heq
        simp only [y, Fin.val_castSucc, Fin.val_last] at hv
        omega
    have hlong : ∀ i : Fin (m + 1), g (p i.castSucc) = (a i.val : ZMod N) := by
      intro i
      refine Fin.lastCases ?_ (fun k ↦ ?_) i
      · simpa only [p, x, y, Equiv.swap_apply_left, Fin.val_last] using hnext
      · rw [hfix, hprefix]
        rfl
    have hpvalid := validTuple_embedding p.toEmbedding g hg
    have hfull := eq_fixed_of_valid_fixed_prefix_of_modulus_le (by omega) hN
      (fun i ↦ g (p i)) hpvalid hlong
    exact ⟨p, fun i ↦ congrFun hfull i⟩

/-- Affine two-extra prefixes below the last two binary residues extend
to the whole tuple with the same affine map, after a permutation. -/
theorem exists_perm_affine_fixed_of_valid_affine_fixed_short_prefix_of_modulus_le
    {m N : ℕ} [NeZero N] (hm : 5 ≤ m) (hN : N ≤ 2 ^ (m + 2) - 3)
    (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod N ≃+ ZMod N) (b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc) = φ (a i.val) + b) :
    ∃ p : Equiv.Perm (Fin (m + 2)), ∀ i, g (p i) = φ (a i.val) + b := by
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) b
  have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
  obtain ⟨p, hfull⟩ := exists_perm_fixed_of_valid_fixed_short_prefix_of_modulus_le hm hN
    (fun i ↦ φ.symm (g (e i) - b)) hw (by intro i; simp [hprefix])
  refine ⟨p.trans e, ?_⟩
  intro i
  have h := congrArg φ (hfull i)
  rw [φ.apply_symm_apply] at h
  change g (e (p i)) = _
  exact (sub_eq_iff_eq_add).mp h

/-- At the global endpoint, a coherent unit-affine `n-2`-entry prefix
extracts the whole SI tuple for every `n>=7`. -/
theorem exists_perm_affine_fixed_of_valid_affine_fixed_short_prefix_at_endpoint
    {m N : ℕ} [NeZero N] (hm : 5 ≤ m) (hendpoint : N = globalBound (m + 2))
    (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod N ≃+ ZMod N) (b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc) = φ (a i.val) + b) :
    ∃ p : Equiv.Perm (Fin (m + 2)), ∀ i, g (p i) = φ (a i.val) + b := by
  have hlog : 2 ≤ Nat.log 2 (m + 2) :=
    (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by norm_num; omega)
  have hdelta : 4 ≤ 2 ^ Nat.log 2 (m + 2) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hlog
  have hN : N ≤ 2 ^ (m + 2) - 3 := by rw [hendpoint]; unfold globalBound; omega
  exact exists_perm_affine_fixed_of_valid_affine_fixed_short_prefix_of_modulus_le
    hm hN g hg e φ b hprefix

/-- Below `2^n`, the two-extra coherent-prefix class has a power-gap
modulus. Dimensions five and six use the already proved odd base bounds;
all larger dimensions use the uniform extraction theorem. -/
theorem exists_power_gap_of_valid_fixed_short_prefix_lt_two_pow
    {m N : ℕ} [NeZero N] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = (a i.val : ZMod N))
    (hupper : N < 2 ^ (m + 2)) : ∃ t < m + 2, N = 2 ^ (m + 2) - 2 ^ t := by
  by_cases hm5 : 5 ≤ m
  · by_cases hnear : N ≤ 2 ^ (m + 2) - 3
    · obtain ⟨p, hfull⟩ := exists_perm_fixed_of_valid_fixed_short_prefix_of_modulus_le
        hm5 hnear g hg hprefix
      have hv := validTuple_embedding p.toEmbedding g hg
      have heq : (fun i ↦ g (p i)) = fun i ↦ (a i.val : ZMod N) := funext hfull
      change ValidTuple (fun i ↦ g (p i)) at hv
      rw [heq] at hv
      have hcard := Fintype.card_le_of_injective _ (validTuple_injective _ hg)
      simp only [Fintype.card_fin, ZMod.card] at hcard
      exact exists_power_gap_of_valid_fixed_lt_two_pow (by omega) (by omega) hupper
        (valid_fixed_of_validTuple hv)
    · have hp : 8 ≤ 2 ^ (m + 2) := by
        simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : 3 ≤ m + 2)
      by_cases htop : N = 2 ^ (m + 2) - 1
      · exact ⟨0, by omega, by simpa using htop⟩
      · exact ⟨1, by omega, by norm_num; omega⟩
  · have hbound := global_lower_bound_of_valid_fixed_short_prefix hm g hg hprefix
    have hcases : m = 3 ∨ m = 4 := by omega
    rcases hcases with rfl | rfl
    · norm_num [globalBound] at hbound hupper ⊢
      have hne29 : N ≠ 29 := by
        intro heq
        have hodd : Odd N := by rw [heq]; norm_num
        have := odd_min_five hodd g hg
        omega
      by_cases h28 : N = 28
      · exact ⟨2, by norm_num, by norm_num; omega⟩
      by_cases h30 : N = 30
      · exact ⟨1, by norm_num, by norm_num; omega⟩
      · exact ⟨0, by norm_num, by norm_num; omega⟩
    · norm_num [globalBound] at hbound hupper ⊢
      have hne61 : N ≠ 61 := by
        intro heq
        have hodd : Odd N := by rw [heq]; norm_num
        have := odd_min_six hodd g hg
        omega
      by_cases h60 : N = 60
      · exact ⟨2, by norm_num, by norm_num; omega⟩
      by_cases h62 : N = 62
      · exact ⟨1, by norm_num, by norm_num; omega⟩
      · exact ⟨0, by norm_num, by norm_num; omega⟩

/-- Affine normalization preserves power-gap rigidity for two extras. -/
theorem exists_power_gap_of_valid_affine_fixed_short_prefix_lt_two_pow
    {m N : ℕ} [NeZero N] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod N ≃+ ZMod N) (b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc) = φ (a i.val) + b)
    (hupper : N < 2 ^ (m + 2)) : ∃ t < m + 2, N = 2 ^ (m + 2) - 2 ^ t := by
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) b
  have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
  exact exists_power_gap_of_valid_fixed_short_prefix_lt_two_pow hm
    (fun i ↦ φ.symm (g (e i) - b)) hw (by intro i; simp [hprefix]) hupper

/-- The exact stratum bound, not just its global envelope, holds for a
coherent unit-affine SI prefix of length `n-2` with two arbitrary extras. -/
theorem stratum_lower_bound_of_valid_affine_fixed_short_prefix
    {m s q : ℕ} (hm : 3 ≤ m) (hq : Odd q)
    (g : Fin (m + 2) → ZMod (2 ^ s * q)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2)))
    (φ : ZMod (2 ^ s * q) ≃+ ZMod (2 ^ s * q)) (b : ZMod (2 ^ s * q))
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc) = φ (a i.val) + b) :
    stratumBound (m + 2) s ≤ 2 ^ s * q := by
  have hqpos := hq.pos
  have hNpos : 0 < 2 ^ s * q := by positivity
  letI : NeZero (2 ^ s * q) := ⟨ne_of_gt hNpos⟩
  by_contra hnot
  have hgapPos : 0 < 2 ^ min s (Nat.log 2 (m + 2)) := by positivity
  have hupper : 2 ^ s * q < 2 ^ (m + 2) := by unfold stratumBound at hnot; omega
  obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_affine_fixed_short_prefix_lt_two_pow
    hm g hg e φ b hprefix hupper
  have hbound := global_lower_bound_of_valid_affine_fixed_short_prefix hm g hg e φ b hprefix
  have htlog : t ≤ Nat.log 2 (m + 2) := by
    apply (pow_le_pow_iff_right₀ (by omega : 1 < (2 : ℕ))).mp
    have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) ht.le
    rw [hgap] at hbound
    unfold globalBound at hbound
    omega
  have htwodvd : 2 ^ t ∣ 2 ^ s * q := by
    rw [hgap]
    exact Nat.dvd_sub (pow_dvd_pow 2 ht.le) (dvd_refl _)
  have hts : t ≤ s := by
    by_contra hc
    have hstep : 2 ^ s * 2 ∣ 2 ^ s * q := by
      rw [← pow_succ]
      exact (pow_dvd_pow 2 (by omega : s + 1 ≤ t)).trans htwodvd
    exact hq.not_two_dvd_nat (Nat.dvd_of_mul_dvd_mul_left (by positivity) hstep)
  have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (le_min hts htlog)
  unfold stratumBound at hnot
  omega

/-- Direct critical-G1 exclusion for the two-extra coherent unit class. -/
theorem not_validTuple_of_critical_affine_fixed_short_prefix
    {m s q : ℕ} (hm : 3 ≤ m) (hq : Odd q)
    (hcritical : 2 ^ s * q < stratumBound (m + 2) s)
    (g : Fin (m + 2) → ZMod (2 ^ s * q)) (e : Equiv.Perm (Fin (m + 2)))
    (φ : ZMod (2 ^ s * q) ≃+ ZMod (2 ^ s * q)) (b : ZMod (2 ^ s * q))
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc) = φ (a i.val) + b) :
    ¬ ValidTuple g := by
  intro hg
  exact (not_lt_of_ge
    (stratum_lower_bound_of_valid_affine_fixed_short_prefix hm hq g hg e φ b hprefix)) hcritical

/-- The full odd G2 threshold for a coherent unit-affine shorter prefix,
with both extras arbitrary, in every dimension at least five. -/
theorem odd_lower_bound_of_valid_affine_fixed_short_prefix
    {m N : ℕ} (hm : 3 ≤ m) (hN : Odd N)
    (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod N ≃+ ZMod N) (b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc) = φ (a i.val) + b) :
    2 ^ (m + 2) - 1 ≤ N := by
  have h := stratum_lower_bound_of_valid_affine_fixed_short_prefix (s := 0) hm hN
  rw [show (2 : ℕ) ^ 0 * N = N by simp] at h
  simpa [stratumBound] using h g hg e φ b hprefix

end MinModulus
