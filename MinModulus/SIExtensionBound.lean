/-
# Full global bound for a super-increasing block plus an arbitrary residue

A valid n-tuple containing a coherent affine copy of the first n-1 fixed
super-increasing entries satisfies the full globalBound n. The last entry
is arbitrary: no doubling-closure assumption is imposed on the full tuple.

The proof constructs multiset sums with Mersenne coins 2^i-1. Below the
claimed global bound, n coins from the retained n-1 entries cover every
residue except possibly 2^n-n-1. If the full tuple's sum is covered, a rival
multiset omits the extra coordinate. Otherwise that sum forces the extra
entry to be the missing fixed-set entry, and nmin_eq finishes the proof.

The initial interval cover also gives a direct uniform G3 consumer. These
theorems concern a coherent affine block in the full modulus; independent
half-modulus shifts of its entries are not assumed to preserve that form.
No G1/G2/G3 input or new conjectural interface is introduced.
-/
import MinModulus.DoublingClosure

namespace MinModulus
open Finset

/-- With coins through `2^k-1`, `k+d` coins cover the entire initial interval
below `(d+2)*(2^k-1)-(k-1)`. The proof constructs a bounded multiset. -/
theorem exists_mersenne_coin_multiset_of_lt
    {k : ℕ} (hk : 1 ≤ k) (d x : ℕ)
    (hx : x < (d + 2) * (2 ^ k - 1) - (k - 1)) :
    ∃ s : Multiset ℕ, s.card ≤ k + d ∧
      (∀ i ∈ s, i ≤ k) ∧ (s.map a).sum = x := by
  induction k, hk using Nat.le_induction generalizing d x with
  | base =>
    refine ⟨Multiset.replicate x 1, ?_, ?_, ?_⟩
    · simp only [Multiset.card_replicate]
      norm_num at hx
      omega
    · intro i hi
      exact (Multiset.mem_replicate.mp hi).2.le
    · simp [a]
  | succ k hk ih =>
    have htwo : k < 2 ^ k := Nat.lt_two_pow_self
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
    induction d generalizing x with
    | zero =>
      by_cases hsmall : x < 2 ^ (k + 1) - 1
      · have hx' : x < (1 + 2) * (2 ^ k - 1) - (k - 1) := by omega
        obtain ⟨s, hs, hmem, hsum⟩ := ih 1 x hx'
        exact ⟨s, by omega, fun i hi ↦ (hmem i hi).trans (by omega), hsum⟩
      · have hx' : x - (2 ^ (k + 1) - 1) <
            (0 + 2) * (2 ^ k - 1) - (k - 1) := by omega
        obtain ⟨s, hs, hmem, hsum⟩ := ih 0 _ hx'
        refine ⟨(k + 1) ::ₘ s, by simp only [Multiset.card_cons]; omega, ?_, ?_⟩
        · intro i hi
          rcases Multiset.mem_cons.mp hi with rfl | hi
          · rfl
          · exact (hmem i hi).trans (by omega)
        · rw [Multiset.map_cons, Multiset.sum_cons, hsum]
          simp only [a]
          omega
    | succ d ihd =>
      let C := 2 ^ (k + 1) - 1
      have hC : k ≤ C := by dsimp [C]; omega
      have hmul : 2 * C ≤ (d + 2) * C := Nat.mul_le_mul_right C (by omega)
      have hincr : (d + 1 + 2) * C = (d + 2) * C + C := by ring
      change x < (d + 1 + 2) * C - k at hx
      rw [hincr] at hx
      by_cases hsmall : x < (d + 2) * C - k
      · obtain ⟨s, hs, hmem, hsum⟩ := ihd x (by simpa [C] using hsmall)
        exact ⟨s, by omega, hmem, hsum⟩
      · have hx' : x - C < (d + 2) * C - k := by omega
        obtain ⟨s, hs, hmem, hsum⟩ := ihd _ (by simpa [C] using hx')
        refine ⟨(k + 1) ::ₘ s, by simp only [Multiset.card_cons]; omega, ?_, ?_⟩
        · intro i hi
          rcases Multiset.mem_cons.mp hi with rfl | hi
          · rfl
          · exact hmem i hi
        · rw [Multiset.map_cons, Multiset.sum_cons, hsum]
          simp only [a]
          change C + (x - C) = x
          omega

/-- The short interval above the first greedy gap is filled by a descending
geometric tail, ending with a repeated smallest coin. -/
theorem exists_mersenne_coin_tail_multiset
    {c : ℕ} (hc : 1 ≤ c) (k : ℕ) (hck : c ≤ k) :
    ∃ s : Multiset ℕ, s.card = c + 1 ∧
      (∀ i ∈ s, i ≤ k - 1) ∧ (s.map a).sum = 2 ^ k - c - 1 := by
  induction c, hc using Nat.le_induction generalizing k with
  | base =>
    refine ⟨Multiset.replicate 2 (k - 1), by simp, ?_, ?_⟩
    · intro i hi
      exact (Multiset.mem_replicate.mp hi).2.le
    · have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hp : 0 < 2 ^ (k - 1) := by positivity
      simp only [Multiset.map_replicate, Multiset.sum_replicate, a, nsmul_eq_mul]
      omega
  | succ c hc ih =>
    obtain ⟨s, hs, hmem, hsum⟩ := ih (k - 1) (by omega)
    refine ⟨(k - 1) ::ₘ s, by simp [hs], ?_, ?_⟩
    · intro i hi
      rcases Multiset.mem_cons.mp hi with rfl | hi
      · rfl
      · exact (hmem i hi).trans (by omega)
    · rw [Multiset.map_cons, Multiset.sum_cons, hsum]
      have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hp := Nat.lt_two_pow_self (n := k - 1)
      simp only [a]
      omega

/-- Up to four times the largest coin, `k+2` coins cover every value except
possibly the first gap. A short geometric tail fills the upper interval. -/
theorem exists_mersenne_coin_multiset_of_lt_four_mul
    {k : ℕ} (hk : 1 ≤ k) (x : ℕ)
    (hx : x < 4 * (2 ^ k - 1))
    (hne : x ≠ 4 * (2 ^ k - 1) - (k - 1)) :
    ∃ s : Multiset ℕ, s.card ≤ k + 2 ∧
      (∀ i ∈ s, i ≤ k) ∧ (s.map a).sum = x := by
  by_cases hsmall : x < 4 * (2 ^ k - 1) - (k - 1)
  · exact exists_mersenne_coin_multiset_of_lt hk 2 x hsmall
  let c := 4 * (2 ^ k - 1) - x
  have hp := Nat.lt_two_pow_self (n := k)
  have hc : 1 ≤ c := by dsimp [c]; omega
  have hck : c ≤ k - 2 := by dsimp [c]; omega
  obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_tail_multiset hc k (by omega)
  refine ⟨Multiset.replicate 3 k + s, by simp [hs]; omega, ?_, ?_⟩
  · intro i hi
    rcases Multiset.mem_add.mp hi with hi | hi
    · exact (Multiset.mem_replicate.mp hi).2.le
    · exact (hmem i hi).trans (by omega)
  · rw [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, hsum]
    simp only [a, nsmul_eq_mul]
    dsimp [c]
    omega

/-- Convert bounded natural coin indices to the finite prefix and pad with
zero coins to obtain exactly one more term than the prefix length. -/
theorem exists_fixed_multiset_sum_of_nat_coin_representation
    {m N : ℕ} [NeZero N] (hm : 0 < m) (x : ZMod N)
    (s : Multiset ℕ) (hs : s.card ≤ m + 1)
    (hmem : ∀ i ∈ s, i < m) (hsum : (s.map a).sum = x.val) :
    ∃ s : Multiset (Fin m), s.card = m + 1 ∧
      (s.map (fun i ↦ (a i.val : ZMod N))).sum = x := by
  classical
  let f : ℕ → Fin m := fun i ↦ ⟨i % m, Nat.mod_lt i hm⟩
  let t := s.map f
  have htcard : t.card ≤ m + 1 := by simpa only [t, Multiset.card_map] using hs
  have htval : (t.map (fun i ↦ (a i.val : ZMod N))).sum = x := by
    have heq : t.map (fun i ↦ (a i.val : ZMod N)) = s.map (fun i ↦ (a i : ZMod N)) := by
      dsimp only [t]
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro i hi
      simp [f, Nat.mod_eq_of_lt (hmem i hi)]
    rw [heq]
    have hc : (s.map (fun i ↦ (a i : ZMod N))).sum = ((s.map a).sum : ℕ) := by simp
    rw [hc, hsum, ZMod.natCast_zmod_val]
  let z : Fin m := ⟨0, hm⟩
  refine ⟨t + Multiset.replicate (m + 1 - t.card) z, ?_, ?_⟩
  · simp only [Multiset.card_add, Multiset.card_replicate]
    omega
  · simpa [z, a] using htval

/-- The retained `m`-entry fixed block covers every residue using exactly
`m+1` terms when the modulus lies below the initial-interval endpoint. -/
theorem exists_fixed_multiset_sum_of_modulus_le_cover_bound
    {m N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (hN : N ≤ 2 ^ (m + 1) - m - 2) (x : ZMod N) :
    ∃ s : Multiset (Fin m), s.card = m + 1 ∧
      (s.map (fun i ↦ (a i.val : ZMod N))).sum = x := by
  classical
  have hpow : 2 ^ (m + 1) = 4 * 2 ^ (m - 1) := by
    rw [show m + 1 = (m - 1) + 2 by omega, pow_add]
    ring
  have hp := Nat.lt_two_pow_self (n := m - 1)
  have hx := x.val_lt
  have hbound : x.val < (2 + 2) * (2 ^ (m - 1) - 1) - (m - 1 - 1) := by omega
  obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt (by omega : 1 ≤ m - 1) 2 x.val hbound
  exact exists_fixed_multiset_sum_of_nat_coin_representation (by omega) x s
    (by omega) (fun i hi ↦ by have := hmem i hi; omega) hsum

/-- Multiset form of validity: a full-length multiset at the distinguished
sum contains each coordinate exactly once. -/
theorem multiset_count_eq_one_of_validTuple
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (s : Multiset (Fin n)) (hcard : s.card = n)
    (hsum : (s.map g).sum = ∑ i, g i) : ∀ i, s.count i = 1 := by
  classical
  have hcount : ∑ i : Fin n, s.count i = n := by
    rw [Multiset.sum_count_eq_card (fun i _ ↦ Finset.mem_univ i), hcard]
  apply hg _ hcount
  rw [← hsum, Finset.sum_multiset_map_count]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hz : s.count i = 0 := Multiset.count_eq_zero.mpr (by simpa using hi)
  simp [hz]

/-- Covering by the retained prefix leaves no room for any extra residue:
the competing full-length multiset omits that coordinate. -/
theorem not_validTuple_of_fixed_prefix_and_modulus_le_cover_bound
    {m N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (hN : N ≤ 2 ^ (m + 1) - m - 2)
    (g : Fin (m + 1) → ZMod N)
    (hprefix : ∀ i : Fin m, g i.castSucc = (a i.val : ZMod N)) :
    ¬ ValidTuple g := by
  intro hg
  classical
  obtain ⟨s, hcard, hsum⟩ := exists_fixed_multiset_sum_of_modulus_le_cover_bound hm hN (∑ i, g i)
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

/-- The no-extension interval is invariant under reindexing, translation,
and a cyclic additive automorphism (unit scaling). -/
theorem not_validTuple_of_affine_fixed_prefix_and_modulus_le_cover_bound
    {m N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (hN : N ≤ 2 ^ (m + 1) - m - 2)
    (g : Fin (m + 1) → ZMod N) (e : Equiv.Perm (Fin (m + 1)))
    (φ : ZMod N ≃+ ZMod N) (b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc) = φ (a i.val) + b) :
    ¬ ValidTuple g := by
  intro hg
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) b
  have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
  apply not_validTuple_of_fixed_prefix_and_modulus_le_cover_bound hm hN
    (fun i ↦ φ.symm (g (e i) - b)) (by intro i; simp [hprefix]) hw

/-- Uniform G3 exclusion for a coherent affine SI prefix and an arbitrary
extra residue. The complete tuple need not be affine-doubling-closed. -/
theorem not_validTuple_exceptional_of_affine_fixed_prefix
    {m : ℕ} (hm : 2 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 1) ≠ m + 1)
    (g : Fin (m + 1) → ZMod (2 * globalBound m))
    (e : Equiv.Perm (Fin (m + 1)))
    (φ : ZMod (2 * globalBound m) ≃+ ZMod (2 * globalBound m))
    (b : ZMod (2 * globalBound m))
    (hprefix : ∀ i : Fin m, g (e i.castSucc) = φ (a i.val) + b) :
    ¬ ValidTuple g := by
  have hB : 2 ≤ globalBound m := (nmin_eq hm).1.1
  letI : NeZero (2 * globalBound m) := ⟨by omega⟩
  have hlog : Nat.log 2 m = Nat.log 2 (m + 1) :=
    (Nat.log_eq_log_succ_iff (b := 2) (n := m) (by omega) (by omega)).mpr hnpow
  have hupper := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (m + 1)
  rw [← hlog, pow_succ'] at hupper
  have hlogle := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
  have hmpow := Nat.lt_two_pow_self (n := m)
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
  have hN : 2 * globalBound m ≤ 2 ^ (m + 1) - m - 2 := by
    unfold globalBound
    omega
  exact not_validTuple_of_affine_fixed_prefix_and_modulus_le_cover_bound hm hN g e φ b hprefix

/-- Below globalBound, every residue except the fixed full-tuple sum is
covered by full-length multisets drawn only from the retained prefix. -/
theorem exists_fixed_multiset_sum_except_cover_hole
    {m N : ℕ} [NeZero N] (hm : 2 ≤ m) (hN : N < globalBound (m + 1))
    (x : ZMod N) (hne : x.val ≠ 2 ^ (m + 1) - m - 2) :
    ∃ s : Multiset (Fin m), s.card = m + 1 ∧
      (s.map (fun i ↦ (a i.val : ZMod N))).sum = x := by
  have hx := x.val_lt
  have hcoins : ∃ s : Multiset ℕ, s.card ≤ m + 1 ∧
      (∀ i ∈ s, i < m) ∧ (s.map a).sum = x.val := by
    by_cases hm2 : m = 2
    · subst m
      norm_num [globalBound] at hN hne
      obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt
        (by omega : 1 ≤ 1) 2 x.val (by norm_num; omega)
      exact ⟨s, hs, fun i hi ↦ by have := hmem i hi; omega, hsum⟩
    · have hm3 : 3 ≤ m := by omega
      have hpow : 2 ^ (m + 1) = 4 * 2 ^ (m - 1) := by
        rw [show m + 1 = (m - 1) + 2 by omega, pow_add]
        ring
      have hp := Nat.lt_two_pow_self (n := m - 1)
      have hlog : 2 ≤ Nat.log 2 (m + 1) := by
        by_contra hc
        have hu := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (m + 1)
        have hl := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ))
          (by omega : Nat.log 2 (m + 1) + 1 ≤ 2)
        norm_num at hl
        omega
      have hdelta : 4 ≤ 2 ^ Nat.log 2 (m + 1) := by
        simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hlog
      have hx' : x.val < 4 * (2 ^ (m - 1) - 1) := by unfold globalBound at hN; omega
      have hne' : x.val ≠ 4 * (2 ^ (m - 1) - 1) - (m - 1 - 1) := by omega
      obtain ⟨s, hs, hmem, hsum⟩ :=
        exists_mersenne_coin_multiset_of_lt_four_mul (by omega : 1 ≤ m - 1) x.val hx' hne'
      exact ⟨s, by omega, fun i hi ↦ by have := hmem i hi; omega, hsum⟩
  obtain ⟨s, hs, hmem, hsum⟩ := hcoins
  exact exists_fixed_multiset_sum_of_nat_coin_representation (by omega) x s hs hmem hsum

/-- The possible uncovered integer is exactly the sum of the full fixed set. -/
theorem sum_fixed_eq_cover_hole (n : ℕ) :
    (∑ i : Fin n, a i.val) = 2 ^ n - n - 1 := by
  have h := sum_a_add_dsum n (fun _ ↦ 1)
  have hd : dsum n (fun _ ↦ 1) = n := by simp [dsum]
  have hv : val n (fun _ ↦ 1) = 2 ^ n - 1 := by
    unfold val
    simpa only [one_mul] using sum_two_pow n
  rw [hd, hv] at h
  simp only [one_mul] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  omega

/-- Adding any residue to the first `m` fixed SI entries cannot improve on
the full fixed-set bound in dimension `m+1`. -/
theorem global_lower_bound_of_valid_fixed_prefix
    {m N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc = (a i.val : ZMod N)) :
    globalBound (m + 1) ≤ N := by
  classical
  by_contra hnot
  have hN : N < globalBound (m + 1) := by omega
  let x := ∑ i, g i
  have hx : x.val = 2 ^ (m + 1) - m - 2 := by
    by_contra hne
    obtain ⟨s, hcard, hsum⟩ := exists_fixed_multiset_sum_except_cover_hole hm hN x hne
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
  have hfull : g = fun i ↦ (a i.val : ZMod N) := by
    funext i
    exact Fin.lastCases hlast (fun j ↦ hprefix j) i
  have hv : Valid (m + 1) N := valid_fixed_of_validTuple (hfull ▸ hg)
  have hcard := Fintype.card_le_of_injective g (validTuple_injective g hg)
  simp only [Fintype.card_fin, ZMod.card] at hcard
  have hb := (nmin_eq (by omega : 2 ≤ m + 1)).2 ⟨by omega, hv⟩
  exact (not_le_of_gt hN) hb

/-- The full global bound holds for a coherent affine SI block plus an
arbitrary extra entry, without assuming closure of the full tuple. -/
theorem global_lower_bound_of_valid_affine_fixed_prefix
    {m N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 1))) (φ : ZMod N ≃+ ZMod N) (b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc) = φ (a i.val) + b) :
    globalBound (m + 1) ≤ N := by
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) b
  have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
  exact global_lower_bound_of_valid_fixed_prefix hm (fun i ↦ φ.symm (g (e i) - b)) hw
    (by intro i; simp [hprefix])

end MinModulus
