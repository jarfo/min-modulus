/-
# Full global bound for an SI prefix and two arbitrary extra entries

For every n >= 5, a valid cyclic n-tuple containing a coherent unit-affine
copy of the first n-2 SI entries satisfies globalBound n. This broadens
the preceding one-extra theorem without assuming full doubling closure,
common touch, a valid deleted quotient, or any global G1/G2/G3 input.

Write m=n-2, L=2^(m-1)-1 and S=2^m-m-1. Below the claimed bound, heredity
and the one-extra cover force each extra X into 4L+1 <= S+X < N, unless
it completes the longer SI prefix already excluded by the older theorem.
For ordered extras X<=Y, Y-X<=S yields a rival with two copies of Y.
Otherwise S+X+Y wraps once, and an (m+2)-term prefix cover supplies a
prefix-only rival. Its initial interval suffices uniformly for m>=5.
The m=3,4 endpoints have explicit coin and triple-extra repairs.

The affine theorem gives a direct G3 consumer in every relevant n>=5.
These results require a coherent prefix in the FULL modulus and unit
scaling. Arbitrary independent half-modulus shifts, nonunit scaling of
this shorter prefix, and the three unrestricted global inputs stay open.
No finite census, proof placeholder, or additional axiom is used.
-/
import MinModulus.SIMultiplierBound

namespace MinModulus
open Finset

/-- Pad a bounded natural Mersenne representation to any prescribed length. -/
theorem exists_fixed_multiset_sum_of_nat_coin_representation_card
    {m N K x : ℕ} (hm : 0 < m) (s : Multiset ℕ) (hs : s.card ≤ K)
    (hmem : ∀ i ∈ s, i < m) (hsum : (s.map a).sum = x) :
    ∃ t : Multiset (Fin m), t.card = K ∧
      (t.map (fun i ↦ (a i.val : ZMod N))).sum = (x : ZMod N) := by
  classical
  let f : ℕ → Fin m := fun i ↦ ⟨i % m, Nat.mod_lt i hm⟩
  let t := s.map f
  have htcard : t.card ≤ K := by simpa only [t, Multiset.card_map] using hs
  have htval : (t.map (fun i ↦ (a i.val : ZMod N))).sum = (x : ZMod N) := by
    have heq : t.map (fun i ↦ (a i.val : ZMod N)) = s.map (fun i ↦ (a i : ZMod N)) := by
      dsimp only [t]
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro i hi
      simp [f, Nat.mod_eq_of_lt (hmem i hi)]
    rw [heq]
    have hc : (s.map (fun i ↦ (a i : ZMod N))).sum = ((s.map a).sum : ℕ) := by simp
    rw [hc, hsum]
  let z : Fin m := ⟨0, hm⟩
  refine ⟨t + Multiset.replicate (K - t.card) z, ?_, ?_⟩
  · simp only [Multiset.card_add, Multiset.card_replicate]
    omega
  · simpa [z, a] using htval

/-- A full-length rival omitting a coordinate contradicts validity. -/
theorem not_validTuple_of_multiset_omission
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (s : Multiset (Fin n)) (hcard : s.card = n)
    (hsum : (s.map g).sum = ∑ i, g i) (j : Fin n) (hj : j ∉ s) :
    ¬ ValidTuple g := by
  intro hg
  have hzero := Multiset.count_eq_zero.mpr hj
  have hone := multiset_count_eq_one_of_validTuple g hg s hcard hsum j
  omega

/-- The one-extra cover includes its right endpoint, with only the usual
fixed-set hole left over. -/
theorem exists_fixed_multiset_sum_of_le_four_mul_except_hole
    {m N x : ℕ} (hm : 3 ≤ m)
    (hx : x ≤ 4 * (2 ^ (m - 1) - 1))
    (hne : x ≠ 4 * (2 ^ (m - 1) - 1) - (m - 2)) :
    ∃ s : Multiset (Fin m), s.card = m + 1 ∧
      (s.map (fun i ↦ (a i.val : ZMod N))).sum = (x : ZMod N) := by
  by_cases heq : x = 4 * (2 ^ (m - 1) - 1)
  · apply exists_fixed_multiset_sum_of_nat_coin_representation_card (by omega)
      (Multiset.replicate 4 (m - 1))
    · simp; omega
    · intro i hi
      have := (Multiset.mem_replicate.mp hi).2
      omega
    · simp [a, heq]; omega
  · obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt_four_mul
      (by omega : 1 ≤ m - 1) x (by omega) (by convert hne using 2; omega)
    exact exists_fixed_multiset_sum_of_nat_coin_representation_card (by omega) s
      (by omega) (fun i hi ↦ by have := hmem i hi; omega) hsum

/-- An individually valid extra entry, unless it completes the fixed set,
lies in a short ordinary interval; its sum with the prefix does not wrap. -/
theorem fixed_prefix_extra_localization
    {m N : ℕ} [NeZero N] (hm : 3 ≤ m)
    (hN : 4 * (2 ^ (m - 1) - 1) + 4 ≤ N)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc = (a i.val : ZMod N))
    (hextra : g (Fin.last m) ≠ (a m : ZMod N)) :
    4 * (2 ^ (m - 1) - 1) + 1 ≤ (2 ^ m - m - 1) + (g (Fin.last m)).val ∧
      (2 ^ m - m - 1) + (g (Fin.last m)).val < N := by
  have hp := Nat.lt_two_pow_self (n := m - 1)
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  let S := 2 ^ m - m - 1
  let z := (S : ZMod N) + g (Fin.last m)
  have hsum : (∑ i, g i) = z := by
    rw [Fin.sum_univ_castSucc]
    simp only [hprefix, ← Nat.cast_sum, sum_fixed_eq_cover_hole, z, S]
  have hhole : z.val ≠ 4 * (2 ^ (m - 1) - 1) - (m - 2) := by
    intro heq
    have hz : z = ((4 * (2 ^ (m - 1) - 1) - (m - 2) : ℕ) : ZMod N) := by
      rw [← heq, ZMod.natCast_zmod_val]
    have hnat : 4 * (2 ^ (m - 1) - 1) - (m - 2) = S + a m := by
      dsimp [S, a]; omega
    rw [hnat, Nat.cast_add] at hz
    exact hextra (add_left_cancel hz)
  have hlarge : 4 * (2 ^ (m - 1) - 1) < z.val := by
    by_contra hc
    obtain ⟨s, hcard, hs⟩ := exists_fixed_multiset_sum_of_le_four_mul_except_hole
      (N := N) hm (by omega : z.val ≤ _) hhole
    apply not_validTuple_of_multiset_omission g (s.map Fin.castSucc)
      (by simpa using hcard) ?_ (Fin.last m) ?_ hg
    · simpa only [Multiset.map_map, Function.comp_def, hprefix,
        ZMod.natCast_zmod_val, hsum] using hs
    · intro hmem
      obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
      have hv := congrArg Fin.val hi
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      omega
  have hzval : z.val = (S + (g (Fin.last m)).val) % N := by
    dsimp only [z]
    rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_add_mod]
  have hx := (g (Fin.last m)).val_lt
  have hS : S < N := by dsimp [S]; omega
  have htotal : S + (g (Fin.last m)).val < 2 * N := by omega
  have hnowrap : S + (g (Fin.last m)).val < N := by
    by_contra hc
    have hrem : (S + (g (Fin.last m)).val) % N =
        S + (g (Fin.last m)).val - N := Nat.mod_eq_sub_mod (by omega) |>.trans
          (Nat.mod_eq_of_lt (by omega))
    rw [hzval, hrem] at hlarge
    dsimp [S] at hlarge
    omega
  rw [hzval, Nat.mod_eq_of_lt hnowrap] at hlarge
  exact ⟨by dsimp [S] at hlarge; omega, hnowrap⟩

/-- Prefix-only terms plus a nonstandard number of copies of an outside
coordinate cannot attain the distinguished full-tuple sum. -/
theorem not_validTuple_of_fixed_block_rival
    {m n N K r q : ℕ} (g : Fin n → ZMod N) (f : Fin m ↪ Fin n)
    (hprefix : ∀ i, g (f i) = (a i.val : ZMod N))
    (j : Fin n) (hj : ∀ i, f i ≠ j) (hq : q ≠ 1) (hcard : K + q = n)
    (hcover : ∃ s : Multiset (Fin m), s.card = K ∧
      (s.map (fun i ↦ (a i.val : ZMod N))).sum = (r : ZMod N))
    (hsum : (r : ZMod N) + q • g j = ∑ i, g i) : ¬ ValidTuple g := by
  classical
  intro hg
  obtain ⟨s, hscard, hssum⟩ := hcover
  let t := s.map f + Multiset.replicate q j
  have htcard : t.card = n := by simp [t, hscard, hcard]
  have htsum : (t.map g).sum = ∑ i, g i := by
    simpa only [t, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
      Function.comp_def, hprefix, Multiset.map_replicate, Multiset.sum_replicate,
      hssum] using hsum
  have hjnot : j ∉ s.map f := by
    intro hmem
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
    exact hj i hi
  have hcount := multiset_count_eq_one_of_validTuple g hg t htcard htsum j
  simp only [t, Multiset.count_add, Multiset.count_eq_zero.mpr hjnot,
    Multiset.count_replicate_self, zero_add] at hcount
  exact hq hcount

/-- A bounded initial interval admits a fixed-cardinality prefix cover. -/
theorem exists_fixed_multiset_sum_of_lt_initial_interval
    {m N d r : ℕ} (hm : 2 ≤ m)
    (hr : r < (d + 2) * (2 ^ (m - 1) - 1) - (m - 2)) :
    ∃ s : Multiset (Fin m), s.card = m - 1 + d ∧
      (s.map (fun i ↦ (a i.val : ZMod N))).sum = (r : ZMod N) := by
  obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt
    (by omega : 1 ≤ m - 1) d r (by convert hr using 2; omega)
  exact exists_fixed_multiset_sum_of_nat_coin_representation_card (by omega) s hs
    (fun i hi ↦ by have := hmem i hi; omega) hsum

/-- Once two extras are localized, close extras have a double-extra rival;
far extras have a prefix-only rival. This is an integer interval argument,
uniform in the prefix length and the modulus. -/
theorem not_validTuple_of_localized_fixed_short_prefix
    {m N : ℕ} [NeZero N] (hm : 3 ≤ m)
    (hN : N ≤ 8 * (2 ^ (m - 1) - 1) + 3)
    (hcoverN : N ≤ 3 * (2 ^ m - m - 1) + 3 * (2 ^ (m - 1) - 1) + 3)
    (g : Fin (m + 2) → ZMod N) (f : Fin m ↪ Fin (m + 2))
    (hprefix : ∀ i, g (f i) = (a i.val : ZMod N))
    (x y : Fin (m + 2)) (hy : ∀ i, f i ≠ y)
    (hsum : (∑ i, g i) = ((2 ^ m - m - 1 : ℕ) : ZMod N) + g x + g y)
    (hxlo : 4 * (2 ^ (m - 1) - 1) + 1 ≤ (2 ^ m - m - 1) + (g x).val)
    (hylo : 4 * (2 ^ (m - 1) - 1) + 1 ≤ (2 ^ m - m - 1) + (g y).val)
    (hxhi : (2 ^ m - m - 1) + (g x).val < N)
    (hyhi : (2 ^ m - m - 1) + (g y).val < N)
    (hxy : (g x).val ≤ (g y).val) : ¬ ValidTuple g := by
  have hp := Nat.lt_two_pow_self (n := m - 1)
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  let S := 2 ^ m - m - 1
  let X := (g x).val
  let Y := (g y).val
  change 4 * (2 ^ (m - 1) - 1) + 1 ≤ S + X at hxlo
  change 4 * (2 ^ (m - 1) - 1) + 1 ≤ S + Y at hylo
  change S + X < N at hxhi
  change S + Y < N at hyhi
  change X ≤ Y at hxy
  by_cases hclose : Y ≤ S + X
  · let r := S + X - Y
    have hr : r + Y = S + X := by dsimp [r]; omega
    have hrbound : r < (1 + 2) * (2 ^ (m - 1) - 1) - (m - 2) := by
      dsimp [r, S] at *; omega
    apply not_validTuple_of_fixed_block_rival g f hprefix y hy
      (by omega : 2 ≠ 1) (by omega : (m - 1 + 1) + 2 = m + 2)
      (exists_fixed_multiset_sum_of_lt_initial_interval (by omega) hrbound)
    have hz := congrArg (fun k : ℕ ↦ (k : ZMod N)) hr
    simp only [Nat.cast_add, ZMod.natCast_zmod_val, X, Y] at hz
    rw [hsum, ← hz]
    simp only [two_nsmul]
    abel
  · let r := S + X + Y - N
    have hr : r + N = S + X + Y := by dsimp [r, S] at *; omega
    have hrbound : r < (3 + 2) * (2 ^ (m - 1) - 1) - (m - 2) := by
      dsimp [r, S] at *; omega
    apply not_validTuple_of_fixed_block_rival g f hprefix y hy
      (by omega : 0 ≠ 1) (by omega : (m - 1 + 3) + 0 = m + 2)
      (exists_fixed_multiset_sum_of_lt_initial_interval (by omega) hrbound)
    have hz := congrArg (fun k : ℕ ↦ (k : ZMod N)) hr
    simpa only [Nat.cast_add, ZMod.natCast_self, add_zero,
      ZMod.natCast_zmod_val, X, Y, zero_nsmul, hsum, S] using hz

/-- In a putative counterexample with a two-extra SI prefix, either extra
is localized. If it completes the longer prefix, the preceding extension
theorem already excludes the tuple. -/
theorem fixed_short_prefix_extra_localization
    {m N : ℕ} [NeZero N] (hm : 3 ≤ m)
    (hN : 4 * (2 ^ (m - 1) - 1) + 4 ≤ N) (hcrit : N < globalBound (m + 2))
    (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = (a i.val : ZMod N))
    (j : Fin (m + 2)) (hj : m ≤ j.val) :
    4 * (2 ^ (m - 1) - 1) + 1 ≤ (2 ^ m - m - 1) + (g j).val ∧
      (2 ^ m - m - 1) + (g j).val < N := by
  let x : Fin (m + 2) := (Fin.last m).castSucc
  let p := Equiv.swap j x
  have hpx : p x = j := Equiv.swap_apply_right j x
  have hfix (i : Fin m) : p i.castSucc.castSucc = i.castSucc.castSucc := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_castSucc] at hv
      omega
    · intro heq
      have hv := congrArg Fin.val heq
      simp only [x, Fin.val_castSucc, Fin.val_last] at hv
      omega
  have hpvalid := validTuple_embedding p.toEmbedding g hg
  have hv := validTuple_embedding ⟨Fin.castSucc, Fin.castSucc_injective (m + 1)⟩
    (fun i ↦ g (p i)) hpvalid
  have hpre : ∀ i : Fin m, g (p i.castSucc.castSucc) = (a i.val : ZMod N) := by
    intro i
    rw [hfix, hprefix]
  have hne : g (p x) ≠ (a m : ZMod N) := by
    intro heq
    have hfull : ∀ i : Fin (m + 1), g (p i.castSucc) = (a i.val : ZMod N) := by
      intro i
      exact Fin.lastCases heq (fun k ↦ hpre k) i
    exact (not_le_of_gt hcrit)
      (global_lower_bound_of_valid_fixed_prefix (by omega) (fun i ↦ g (p i)) hpvalid hfull)
  have hpx' : p (Fin.last m).castSucc = j := hpx
  simpa only [hpx'] using fixed_prefix_extra_localization hm hN
    (fun i ↦ g (p i.castSucc)) hv hpre hne

/-- The largest retained SI coin dominates the linear interval loss once
the retained prefix has length at least five. -/
theorem three_mul_sub_three_le_mersenne_pred {m : ℕ} (hm : 5 ≤ m) :
    3 * m - 3 ≤ 2 ^ (m - 1) - 1 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hp := Nat.lt_two_pow_self (n := m - 1)
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    simp only [Nat.add_sub_cancel]
    omega

/-- The full global lower bound for a coherent SI prefix and two arbitrary
extra residues, in every dimension at least seven. -/
theorem global_lower_bound_of_valid_fixed_short_prefix_of_five_le
    {m N : ℕ} [NeZero N] (hm : 5 ≤ m)
    (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = (a i.val : ZMod N)) :
    globalBound (m + 2) ≤ N := by
  by_contra hc
  have hcrit : N < globalBound (m + 2) := by omega
  have hbinary := two_pow_pred_le_card_of_validTuple g hg
  simp only [ZMod.card, show m + 2 - 1 = m + 1 by omega] at hbinary
  have hp := Nat.lt_two_pow_self (n := m - 1)
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpow1 : 2 ^ (m + 1) = 4 * 2 ^ (m - 1) := by rw [pow_succ', hpow]; ring
  have hpow2 : 2 ^ (m + 2) = 8 * 2 ^ (m - 1) := by
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ', hpow1]; ring
  have hlog : 2 ≤ Nat.log 2 (m + 2) :=
    (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by norm_num; omega)
  have hdelta : 4 ≤ 2 ^ Nat.log 2 (m + 2) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hlog
  have hNlo : 4 * (2 ^ (m - 1) - 1) + 4 ≤ N := by omega
  have hNhi : N ≤ 8 * (2 ^ (m - 1) - 1) + 3 := by unfold globalBound at hcrit; omega
  have hcoverN : N ≤ 3 * (2 ^ m - m - 1) + 3 * (2 ^ (m - 1) - 1) + 3 := by
    have := three_mul_sub_three_le_mersenne_pred hm
    omega
  let x : Fin (m + 2) := (Fin.last m).castSucc
  let y : Fin (m + 2) := Fin.last (m + 1)
  let f : Fin m ↪ Fin (m + 2) :=
    ⟨fun i ↦ i.castSucc.castSucc,
      (Fin.castSucc_injective (m + 1)).comp (Fin.castSucc_injective m)⟩
  have hx := fixed_short_prefix_extra_localization (by omega) hNlo hcrit g hg hprefix x (by simp [x])
  have hy := fixed_short_prefix_extra_localization (by omega) hNlo hcrit g hg hprefix y (by simp [y])
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
  · exact not_validTuple_of_localized_fixed_short_prefix (by omega) hNhi hcoverN
      g f hprefix x y hfy hsum hx.1 hy.1 hx.2 hy.2 hxy hg
  · exact not_validTuple_of_localized_fixed_short_prefix (by omega) hNhi hcoverN
      g f hprefix y x hfx (by rw [hsum]; abel) hy.1 hx.1 hy.2 hx.2 hyx hg

/-- Any tail coordinate can be retained alongside the shorter fixed prefix. -/
theorem validTuple_fixed_prefix_with_tail_coordinate
    {m N : ℕ} (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = (a i.val : ZMod N))
    (j : Fin (m + 2)) (hj : m ≤ j.val) :
    ValidTuple (Fin.lastCases (g j) (fun i : Fin m ↦ (a i.val : ZMod N))) := by
  let x : Fin (m + 2) := (Fin.last m).castSucc
  let p := Equiv.swap j x
  have hfix (i : Fin m) : p i.castSucc.castSucc = i.castSucc.castSucc := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_castSucc] at hv
      omega
    · intro heq
      have hv := congrArg Fin.val heq
      simp only [x, Fin.val_castSucc, Fin.val_last] at hv
      omega
  have hv := validTuple_embedding ⟨Fin.castSucc, Fin.castSucc_injective (m + 1)⟩
    (fun i ↦ g (p i)) (validTuple_embedding p.toEmbedding g hg)
  have heq : (fun i : Fin (m + 1) ↦ g (p i.castSucc)) =
      Fin.lastCases (g j) (fun i : Fin m ↦ (a i.val : ZMod N)) := by
    funext i
    refine Fin.lastCases ?_ (fun k ↦ ?_) i
    · simp [p, x]
    · simp [hfix, hprefix]
  change ValidTuple (fun i : Fin (m + 1) ↦ g (p i.castSucc)) at hv
  rwa [heq] at hv

/-- Explicit right-end repair of the five-term cover with coins 0,1,3. -/
theorem exists_three_prefix_five_sum_except_two_holes
    {N r : ℕ} (hr : r ≤ 16) (h14 : r ≠ 14) (h16 : r ≠ 16) :
    ∃ s : Multiset (Fin 3), s.card = 5 ∧
      (s.map (fun i ↦ (a i.val : ZMod N))).sum = (r : ZMod N) := by
  by_cases hsmall : r < 14
  · exact exists_fixed_multiset_sum_of_lt_initial_interval (d := 3) (by norm_num)
      (by norm_num; omega)
  · have heq : r = 15 := by omega
    apply exists_fixed_multiset_sum_of_nat_coin_representation_card (by norm_num)
      (Multiset.replicate 5 2) (by simp)
    · intro i hi
      have := (Multiset.mem_replicate.mp hi).2
      omega
    · norm_num [a, heq]

/-- Explicit right-end repair of the six-term cover with coins 0,1,3,7. -/
theorem exists_four_prefix_six_sum_except_hole
    {N r : ℕ} (hr : r ≤ 34) (h33 : r ≠ 33) :
    ∃ s : Multiset (Fin 4), s.card = 6 ∧
      (s.map (fun i ↦ (a i.val : ZMod N))).sum = (r : ZMod N) := by
  by_cases hsmall : r < 33
  · exact exists_fixed_multiset_sum_of_lt_initial_interval (d := 3) (by norm_num)
      (by norm_num; omega)
  · have heq : r = 34 := by omega
    apply exists_fixed_multiset_sum_of_nat_coin_representation_card (by norm_num)
      (Multiset.replicate 4 3 + Multiset.replicate 2 2) (by simp)
    · intro i hi
      rcases Multiset.mem_add.mp hi with hi | hi
      · have := (Multiset.mem_replicate.mp hi).2; omega
      · have := (Multiset.mem_replicate.mp hi).2; omega
    · norm_num [a, heq]

/-- Tripling a single extra removes the exceptional low-dimensional tail
values left over by the interval covers. -/
theorem not_validTuple_fixed_prefix_extra_of_triple_cover
    {m N r : ℕ} (x : ZMod N)
    (hcover : ∃ s : Multiset (Fin m), s.card = m - 2 ∧
      (s.map (fun i ↦ (a i.val : ZMod N))).sum = (r : ZMod N))
    (hm : 2 ≤ m) (hsum : (r : ZMod N) + 2 * x = ((2 ^ m - m - 1 : ℕ) : ZMod N)) :
    ¬ ValidTuple (Fin.lastCases x (fun i : Fin m ↦ (a i.val : ZMod N))) := by
  apply not_validTuple_of_fixed_block_rival
    (Fin.lastCases x (fun i : Fin m ↦ (a i.val : ZMod N)))
    ⟨Fin.castSucc, Fin.castSucc_injective m⟩ (by intro i; simp)
    (Fin.last m) (by intro i; exact Fin.castSucc_ne_last i)
    (by omega : 3 ≠ 1) (by omega : m - 2 + 3 = m + 1) hcover
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, ← Nat.cast_sum, sum_fixed_eq_cover_hole]
  rw [← hsum]
  simp only [nsmul_eq_mul]
  ring

/-- The same localized two-extra obstruction in the two small prefix
lengths. The only missing interval values are repaired explicitly. -/
theorem not_validTuple_of_localized_fixed_short_prefix_small
    {m N : ℕ} [NeZero N] (hm : 3 ≤ m) (hmsmall : m ≤ 4)
    (hN : N ≤ 8 * (2 ^ (m - 1) - 1) + 3)
    (g : Fin (m + 2) → ZMod N) (f : Fin m ↪ Fin (m + 2))
    (hprefix : ∀ i, g (f i) = (a i.val : ZMod N))
    (x y : Fin (m + 2)) (hx : ∀ i, f i ≠ x) (hy : ∀ i, f i ≠ y)
    (hsum : (∑ i, g i) = ((2 ^ m - m - 1 : ℕ) : ZMod N) + g x + g y)
    (hxlo : 4 * (2 ^ (m - 1) - 1) + 1 ≤ (2 ^ m - m - 1) + (g x).val)
    (hylo : 4 * (2 ^ (m - 1) - 1) + 1 ≤ (2 ^ m - m - 1) + (g y).val)
    (hxhi : (2 ^ m - m - 1) + (g x).val < N)
    (hyhi : (2 ^ m - m - 1) + (g y).val < N)
    (hxy : (g x).val ≤ (g y).val)
    (hvx : ValidTuple (Fin.lastCases (g x) (fun i : Fin m ↦ (a i.val : ZMod N)))) :
    ¬ ValidTuple g := by
  have hp := Nat.lt_two_pow_self (n := m - 1)
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
  · let r := S + X + Y - N
    have hr : r + N = S + X + Y := by dsimp [r, S, X, Y] at *; omega
    have hz : (r : ZMod N) = (S : ZMod N) + g x + g y := by
      have ht := congrArg (fun k : ℕ ↦ (k : ZMod N)) hr
      simpa only [Nat.cast_add, ZMod.natCast_self, add_zero, X, Y,
        ZMod.natCast_zmod_val] using ht
    have hcases : m = 3 ∨ m = 4 := by omega
    rcases hcases with rfl | rfl
    · norm_num at hxlo hylo hxhi hyhi hN
      have hrle : r ≤ 16 := by dsimp [r, S, X, Y] at *; omega
      by_cases hholes : r ≠ 14 ∧ r ≠ 16
      · exact not_validTuple_of_fixed_block_rival g f hprefix y hy
          (by omega : 0 ≠ 1) (by omega : 5 + 0 = 3 + 2)
          (exists_three_prefix_five_sum_except_two_holes hrle hholes.1 hholes.2)
          (by simpa only [zero_nsmul, add_zero, hsum, S] using hz)
      · by_cases hdiff : Y = X + 5
        · have hcoins : ∃ s : Multiset (Fin 3), s.card = 3 ∧
              (s.map (fun i ↦ (a i.val : ZMod N))).sum = (9 : ZMod N) := by
            apply exists_fixed_multiset_sum_of_nat_coin_representation_card (by norm_num)
              (Multiset.replicate 3 2) (by simp)
            · intro i hi; have := (Multiset.mem_replicate.mp hi).2; omega
            · norm_num [a]
          apply not_validTuple_of_fixed_block_rival g f hprefix x hx
            (by omega : 2 ≠ 1) (by omega : 3 + 2 = 3 + 2) hcoins
          have ht := congrArg (fun k : ℕ ↦ (k : ZMod N)) hdiff
          simp only [Nat.cast_add, X, Y, ZMod.natCast_zmod_val] at ht
          rw [hsum, ht]
          norm_num
          ring
        · have hX : X = 15 := by dsimp [r, S, X, Y] at *; omega
          have hNN : N = 26 ∨ N = 27 := by dsimp [r, S, X, Y] at *; omega
          have hcoins : ∃ s : Multiset (Fin 3), s.card = 3 - 2 ∧
              (s.map (fun i ↦ (a i.val : ZMod N))).sum = ((N - 26 : ℕ) : ZMod N) := by
            apply exists_fixed_multiset_sum_of_nat_coin_representation_card (by norm_num)
              (Multiset.replicate (N - 26) 1)
            · simp; omega
            · intro i hi; have := (Multiset.mem_replicate.mp hi).2; omega
            · simp [a]
          exact False.elim (not_validTuple_fixed_prefix_extra_of_triple_cover (g x) hcoins
            (by omega) (by
              have ht := congrArg (fun k : ℕ ↦ (k : ZMod N))
                (show (N - 26) + 2 * X = N + 4 by omega)
              norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, X,
                ZMod.natCast_zmod_val, ZMod.natCast_self, zero_add] at ht ⊢
              exact ht) hvx)
    · norm_num at hxlo hylo hxhi hyhi hN
      have hrle : r ≤ 34 := by dsimp [r, S, X, Y] at *; omega
      by_cases hhole : r ≠ 33
      · exact not_validTuple_of_fixed_block_rival g f hprefix y hy
          (by omega : 0 ≠ 1) (by omega : 6 + 0 = 4 + 2)
          (exists_four_prefix_six_sum_except_hole hrle hhole)
          (by simpa only [zero_nsmul, add_zero, hsum, S] using hz)
      · have hX : X = 34 := by dsimp [r, S, X, Y] at *; omega
        have hNN : N = 58 ∨ N = 59 := by dsimp [r, S, X, Y] at *; omega
        have hcoins : ∃ s : Multiset (Fin 4), s.card = 4 - 2 ∧
            (s.map (fun i ↦ (a i.val : ZMod N))).sum = ((N - 57 : ℕ) : ZMod N) := by
          apply exists_fixed_multiset_sum_of_nat_coin_representation_card (by norm_num)
            (Multiset.replicate (N - 57) 1)
          · simp; omega
          · intro i hi; have := (Multiset.mem_replicate.mp hi).2; omega
          · simp [a]
        exact False.elim (not_validTuple_fixed_prefix_extra_of_triple_cover (g x) hcoins
          (by omega) (by
            have ht := congrArg (fun k : ℕ ↦ (k : ZMod N))
              (show (N - 57) + 2 * X = N + 11 by omega)
            norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, X,
              ZMod.natCast_zmod_val, ZMod.natCast_self, zero_add] at ht ⊢
            exact ht) hvx)

/-- Adding any two residues to the first `m` SI entries cannot beat the
full fixed-set global bound. This holds in every dimension `m+2 >= 5`. -/
theorem global_lower_bound_of_valid_fixed_short_prefix
    {m N : ℕ} [NeZero N] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = (a i.val : ZMod N)) :
    globalBound (m + 2) ≤ N := by
  by_cases hm5 : 5 ≤ m
  · exact global_lower_bound_of_valid_fixed_short_prefix_of_five_le hm5 g hg hprefix
  by_contra hc
  have hcrit : N < globalBound (m + 2) := by omega
  have hbinary := two_pow_pred_le_card_of_validTuple g hg
  simp only [ZMod.card] at hbinary
  have hlimits : 4 * (2 ^ (m - 1) - 1) + 4 ≤ N ∧
      N ≤ 8 * (2 ^ (m - 1) - 1) + 3 := by
    have hcases : m = 3 ∨ m = 4 := by omega
    rcases hcases with rfl | rfl <;> norm_num [globalBound] at hcrit hbinary ⊢ <;> omega
  let x : Fin (m + 2) := (Fin.last m).castSucc
  let y : Fin (m + 2) := Fin.last (m + 1)
  let f : Fin m ↪ Fin (m + 2) :=
    ⟨fun i ↦ i.castSucc.castSucc,
      (Fin.castSucc_injective (m + 1)).comp (Fin.castSucc_injective m)⟩
  have hx := fixed_short_prefix_extra_localization hm hlimits.1 hcrit g hg hprefix x (by simp [x])
  have hy := fixed_short_prefix_extra_localization hm hlimits.1 hcrit g hg hprefix y (by simp [y])
  have hvx := validTuple_fixed_prefix_with_tail_coordinate g hg hprefix x (by simp [x])
  have hvy := validTuple_fixed_prefix_with_tail_coordinate g hg hprefix y (by simp [y])
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
  · exact not_validTuple_of_localized_fixed_short_prefix_small hm (by omega) hlimits.2
      g f hprefix x y hfx hfy hsum hx.1 hy.1 hx.2 hy.2 hxy hvx hg
  · exact not_validTuple_of_localized_fixed_short_prefix_small hm (by omega) hlimits.2
      g f hprefix y x hfy hfx (by rw [hsum]; abel) hy.1 hx.1 hy.2 hx.2 hyx hvy hg

/-- Reindexing, translating, and unit scaling preserve the full lower
bound for a coherent SI prefix with two arbitrary extra entries. -/
theorem global_lower_bound_of_valid_affine_fixed_short_prefix
    {m N : ℕ} [NeZero N] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod N ≃+ ZMod N) (b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc) = φ (a i.val) + b) :
    globalBound (m + 2) ≤ N := by
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) b
  have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
  exact global_lower_bound_of_valid_fixed_short_prefix hm (fun i ↦ φ.symm (g (e i) - b)) hw
    (by intro i; simp [hprefix])

/-- Uniform G3 exclusion for coherent full-modulus SI prefixes of length
`n-2`, with two arbitrary extra entries and no quotient-validity assumption. -/
theorem not_validTuple_exceptional_of_affine_fixed_short_prefix
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (e : Equiv.Perm (Fin (m + 2)))
    (φ : ZMod (2 * globalBound (m + 1)) ≃+ ZMod (2 * globalBound (m + 1)))
    (b : ZMod (2 * globalBound (m + 1)))
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc) = φ (a i.val) + b) :
    ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (2 * globalBound (m + 1)) := ⟨by omega⟩
  exact (not_lt_of_ge
    (global_lower_bound_of_valid_affine_fixed_short_prefix hm g hg e φ b hprefix))
    (two_mul_globalBound_lt_succ_of_not_power (by omega) hnpow)

end MinModulus
