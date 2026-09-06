/-
# Quarter offsets from every independently lifted SI prefix entry

The previous H+1 exclusion extends to H+a_j for every prefix index j.
The uniform Mersenne-coin cover has at most one gap at every term budget.
For a nonterminal j its gap lies outside the low-residue interval; the
remaining exception forces the other extra to equal a_(j+1). For terminal
j, the second possible exception is a_(t-1), while the first completes
the full SI quotient prefix. Both cases are already excluded at G3.
-/
import MinModulus.SIQuarterExtra

namespace MinModulus
open Finset

/-- At any excess term budget, the interval up to the corresponding
multiple of the largest Mersenne coin has at most its first greedy gap. -/
theorem exists_mersenne_coin_multiset_of_lt_multiple
    {k : ℕ} (hk : 1 ≤ k) (d x : ℕ)
    (hx : x < (d + 2) * (2 ^ k - 1))
    (hne : x ≠ (d + 2) * (2 ^ k - 1) - (k - 1)) :
    ∃ s : Multiset ℕ, s.card ≤ k + d ∧
      (∀ i ∈ s, i ≤ k) ∧ (s.map a).sum = x := by
  by_cases hsmall : x < (d + 2) * (2 ^ k - 1) - (k - 1)
  · exact exists_mersenne_coin_multiset_of_lt hk d x hsmall
  let c := (d + 2) * (2 ^ k - 1) - x
  have hp := Nat.lt_two_pow_self (n := k)
  have hc : 1 ≤ c := by dsimp [c]; omega
  have hck : c ≤ k - 2 := by dsimp [c]; omega
  obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_tail_multiset hc k (by omega)
  refine ⟨Multiset.replicate (d + 1) k + s, by simp [hs]; omega, ?_, ?_⟩
  · intro i hi
    rcases Multiset.mem_add.mp hi with hi | hi
    · exact (Multiset.mem_replicate.mp hi).2.le
    · exact (hmem i hi).trans (by omega)
  · rw [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, hsum]
    simp only [a, nsmul_eq_mul]
    dsimp [c]
    have heq : (d + 2) * (2 ^ k - 1) = (d + 1) * (2 ^ k - 1) + (2 ^ k - 1) := by ring
    omega

/-- A quarter translate of any prefix coin has a two-hole m-term cover.
The low hole matters only below that extra; the high hole is translated. -/
theorem exists_multiset_sum_of_fixed_prefix_quarter_translate_except_holes
    {m M H : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M = 2 * H)
    (hH : H ≤ 2 ^ m - 2) (j : Fin m) (u : Fin (m + 1) → ZMod M)
    (hu : ∀ i : Fin m, u i.castSucc = (a i.val : ZMod M))
    (hq : u (Fin.last m) = ((H + a j.val : ℕ) : ZMod M))
    (z : ZMod M)
    (hne_low : z.val < H + a j.val → z.val ≠ 3 * (2 ^ (m - 1) - 1) - (m - 2))
    (hne_high : z ≠ ((H + a j.val : ℕ) : ZMod M) + ((2 ^ m - m : ℕ) : ZMod M)) :
    ∃ s : Multiset (Fin (m + 1)), s.card = m ∧ (s.map u).sum = z := by
  classical
  have hp := Nat.lt_two_pow_self (n := m - 1)
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hlarge := succ_le_two_pow_pred m hm
  have hz := z.val_lt
  have hjPow := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (show j.val ≤ m - 1 by omega)
  have haj : a j.val ≤ 2 ^ (m - 1) - 1 := by unfold a; omega
  have mapped (K r : ℕ) (s : Multiset (Fin m)) (hs : s.card = K)
      (hval : (s.map (fun i ↦ (a i.val : ZMod M))).sum = (r : ZMod M)) :
      (s.map Fin.castSucc).card = K ∧ ((s.map Fin.castSucc).map u).sum = (r : ZMod M) := by
    constructor
    · simpa using hs
    · simpa only [Multiset.map_map, Function.comp_def, hu] using hval
  by_cases hlow : z.val < H + a j.val
  · obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt_multiple
      (by omega : 1 ≤ m - 1) 1 z.val (by omega)
      (by convert hne_low hlow using 1; omega)
    obtain ⟨v, hv, hvsum⟩ := exists_fixed_multiset_sum_of_nat_coin_representation_card
      (m := m) (N := M) (K := m) (by omega) s (by omega)
      (fun i hi ↦ by have := hmem i hi; omega) hsum
    obtain ⟨hcard, hval⟩ := mapped m z.val v hv hvsum
    exact ⟨v.map Fin.castSucc, hcard, by simpa using hval⟩
  · let r := z.val - (H + a j.val)
    have hr : r < 2 * (2 ^ (m - 1) - 1) := by dsimp [r]; omega
    have hsumNat : H + a j.val + r = z.val := by dsimp [r]; omega
    have hrne : r ≠ 2 * (2 ^ (m - 1) - 1) - ((m - 1) - 1) := by
      intro heq
      apply hne_high
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

/-- Except at the terminal prefix index, the low hole lies beyond the
interval on which it could obstruct the quarter-translate cover. -/
theorem quarter_translate_le_low_cover_hole_of_not_last
    {m H : ℕ} (hm : 3 ≤ m) (hH : H ≤ 2 ^ m - 2)
    (j : Fin m) (hj : j.val < m - 1) :
    H + a j.val ≤ 3 * (2 ^ (m - 1) - 1) - (m - 2) := by
  have hp := Nat.lt_two_pow_self (n := m - 2)
  have hpow1 : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    rw [← pow_succ']; congr 1; omega
  have hpow2 : 2 ^ m = 4 * 2 ^ (m - 2) := by
    calc
      2 ^ m = 2 ^ ((m - 2) + 2) := by congr 1; omega
      _ = 4 * 2 ^ (m - 2) := by rw [pow_add]; ring
  have hjPow := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (show j.val ≤ m - 2 by omega)
  unfold a
  omega

/-- The other extra cannot be any SI prefix entry or the missing SI
endpoint: these are respectively actual collisions and a full lift prefix. -/
theorem not_validTuple_exceptional_of_si_lifts_last_eq_fixed
    {m k : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (hk : k ≤ m) (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g i.castSucc.castSucc) = (a i.val : ZMod (globalBound (m + 1))))
    (hlast : ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
      (g (Fin.last (m + 1))) = (a k : ZMod (globalBound (m + 1)))) : ¬ ValidTuple g := by
  by_cases hkm : k < m
  · let i : Fin m := ⟨k, hkm⟩
    apply not_validTuple_exceptional_of_last_collision_scaled_short_prefix hm hnpow g
      (Equiv.refl _) 1 0 i.castSucc.castSucc (Fin.castSucc_ne_last i.castSucc)
    · exact (hprefix i).trans hlast.symm
    · intro i
      simpa only [Equiv.refl_apply, one_mul, add_zero] using hprefix i
  · have hkm : k = m := by omega
    subst k
    let p := Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1))
    apply not_validTuple_exceptional_of_quotient_affine_fixed_prefix
      (by omega : 2 ≤ m + 1) hnpow g p (AddEquiv.refl _) 0
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [p, Equiv.swap_apply_left, AddEquiv.refl_apply, add_zero, Fin.val_last] using hlast
    · have hj : p j.castSucc.castSucc = j.castSucc.castSucc := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro heq
          exact Fin.castSucc_ne_last j (Fin.castSucc_injective (m + 1) heq)
        · exact Fin.castSucc_ne_last j.castSucc
      simpa only [hj, AddEquiv.refl_apply, add_zero, Fin.val_castSucc] using hprefix j

/-- Every quarter translate of an actual independently lifted SI prefix
entry is excluded at G3, not just the quarter translate of the lifted one. -/
theorem not_validTuple_exceptional_of_si_lifts_quarter_prefix
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1))) (j : Fin m)
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g i.castSucc.castSucc) = (a i.val : ZMod (globalBound (m + 1))))
    (hq : ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
      (g (Fin.last m).castSucc) =
        ((globalBound (m + 1) / 2 + a j.val : ℕ) : ZMod (globalBound (m + 1)))) :
    ¬ ValidTuple g := by
  classical
  intro hg
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (globalBound (m + 1)) := ⟨by omega⟩
  let M := globalBound (m + 1)
  let H := M / 2
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let u : Fin (m + 1) → ZMod (2 * M) := fun i ↦ g i.castSucc
  let X := ∑ i, g i
  have hy (k : ℕ) (hk : k ≤ m) : π (g (Fin.last (m + 1))) ≠ (a k : ZMod M) := by
    intro heq
    exact not_validTuple_exceptional_of_si_lifts_last_eq_fixed hm hnpow hk g hprefix heq hg
  have ht : 2 ≤ Nat.log 2 (m + 1) :=
    (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by norm_num; omega)
  have hD := Nat.pow_log_le_self 2 (show m + 1 ≠ 0 by omega)
  have hp := Nat.lt_two_pow_self (n := m)
  have hmPow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
  have htPow : 2 ^ Nat.log 2 (m + 1) = 2 * 2 ^ (Nat.log 2 (m + 1) - 1) := by
    rw [← pow_succ']; congr 1; omega
  have htLower : 2 ≤ 2 ^ (Nat.log 2 (m + 1) - 1) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ Nat.log 2 (m + 1) - 1)
  have hM : M = 2 * H := by dsimp [M, H, globalBound]; omega
  have hH : H ≤ 2 ^ m - 2 := by dsimp [M, H, globalBound]; omega
  have hcomp : H + a (Nat.log 2 (m + 1) - 1) = 2 ^ m - 1 := by
    dsimp [M, H, globalBound, a]
    omega
  have hlowIndex : Nat.log 2 (m + 1) - 1 ≤ m := by
    have := Nat.lt_two_pow_self (n := Nat.log 2 (m + 1)); omega
  have hsum : π X = ((2 ^ m - m - 1 : ℕ) : ZMod M) +
      ((H + a j.val : ℕ) : ZMod M) + π (g (Fin.last (m + 1))) := by
    dsimp only [X]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, map_add, map_add, map_sum, hq]
    congr 2
    simp only [π, M, hprefix, ← Nat.cast_sum, sum_fixed_eq_cover_hole]
  have hF : ((2 ^ m - m - 1 : ℕ) : ZMod M) + 1 = ((2 ^ m - m : ℕ) : ZMod M) := by
    have hn : (2 ^ m - m - 1) + 1 = 2 ^ m - m := by omega
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ ↦ (k : ZMod M)) hn
  have haj : (a (j.val + 1) : ZMod M) = 2 • (a j.val : ZMod M) + 1 := by
    have hnat : a (j.val + 1) = 2 * a j.val + 1 := by
      have := Nat.two_pow_pos j.val
      unfold a
      rw [pow_succ']
      omega
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, nsmul_eq_mul] using
      congrArg (fun k : ℕ ↦ (k : ZMod M)) hnat
  have hpair : 2 • u (Fin.last m) = 2 • u j.castSucc + M := by
    have hp' := two_nsmul_quarter_extra_eq_two_nsmul_one_add_half hM
      (u (Fin.last m) - u j.castSucc + 1) 1
      (by
        change π _ = _
        rw [map_add, map_sub, map_one, hq, hprefix]
        push_cast
        ring)
      (by simp)
    simp only [nsmul_eq_mul] at hp' ⊢
    linear_combination hp'
  let z := π (X - 2 • u j.castSucc)
  have hne_high : z ≠ ((H + a j.val : ℕ) : ZMod M) + ((2 ^ m - m : ℕ) : ZMod M) := by
    intro heq
    apply hy (j.val + 1) (by omega)
    dsimp only [z] at heq
    rw [map_sub, map_nsmul, hprefix, hsum, ← hF] at heq
    rw [haj]
    simp only [nsmul_eq_mul] at heq ⊢
    linear_combination heq
  have hne_low : z.val < H + a j.val → z.val ≠ 3 * (2 ^ (m - 1) - 1) - (m - 2) := by
    intro hzlow hzval
    by_cases hj : j.val < m - 1
    · have := quarter_translate_le_low_cover_hole_of_not_last hm hH j hj
      omega
    · have hjval : j.val = m - 1 := by omega
      apply hy (Nat.log 2 (m + 1) - 1) hlowIndex
      have hp' := Nat.lt_two_pow_self (n := m - 1)
      have hmPred : 2 ^ m = 2 * 2 ^ (m - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hnat : (3 * (2 ^ (m - 1) - 1) - (m - 2)) + 2 * a j.val =
          (2 ^ m - m - 1) + (H + a j.val) + a (Nat.log 2 (m + 1) - 1) := by
        rw [hjval]
        simp only [a] at hcomp ⊢
        omega
      have heq : z = ((3 * (2 ^ (m - 1) - 1) - (m - 2) : ℕ) : ZMod M) := by
        rw [← hzval, ZMod.natCast_zmod_val]
      dsimp only [z] at heq
      rw [map_sub, map_nsmul, hprefix, hsum] at heq
      have hc := congrArg (fun k : ℕ ↦ (k : ZMod M)) hnat
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul] at hc heq
      linear_combination heq + hc
  obtain ⟨s, hs, hproj⟩ := exists_multiset_sum_of_fixed_prefix_quarter_translate_except_holes
    hm hM hH j (fun i ↦ π (u i)) hprefix hq z hne_low hne_high
  have hproj' : π ((s.map u).sum + 2 • u j.castSucc) = π X := by
    rw [map_add, map_multiset_sum, Multiset.map_map]
    change (s.map (fun i ↦ π (u i))).sum + π (2 • u j.castSucc) = π X
    rw [hproj]
    dsimp only [z]
    rw [map_sub]
    abel
  obtain ⟨v, hv, hvsum⟩ := exists_multiset_sum_of_antipodal_coin_pair u j.castSucc (Fin.last m)
    hpair s (by omega : s.card + 2 = m + 2) X hproj'
  apply not_validTuple_of_multiset_omission g (v.map Fin.castSucc)
    (by simpa using hv) (by simpa only [u, Multiset.map_map, Function.comp_def] using hvsum)
    (Fin.last (m + 1)) ?_ hg
  intro hmem
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
  exact Fin.castSucc_ne_last i hi

/-- The all-index obstruction is invariant under reindexing and affine
automorphisms of the actual half quotient; upstairs lift bits stay arbitrary. -/
theorem not_validTuple_exceptional_of_quotient_affine_short_prefix_quarter_translate
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (e : Equiv.Perm (Fin (m + 2))) (j : Fin m)
    (φ : ZMod (globalBound (m + 1)) ≃+ ZMod (globalBound (m + 1)))
    (b : ZMod (globalBound (m + 1)))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g (e i.castSucc.castSucc)) = φ (a i.val) + b)
    (hq : ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
      (g (e (Fin.last m).castSucc)) =
        φ ((globalBound (m + 1) / 2 + a j.val : ℕ) : ZMod (globalBound (m + 1))) + b) :
    ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (globalBound (m + 1)) := ⟨by omega⟩
  letI : NeZero (2 * globalBound (m + 1)) := ⟨by omega⟩
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_lift_castHom (dvd_mul_left (globalBound (m + 1)) 2) φ
  let B : ZMod (2 * globalBound (m + 1)) := b.val
  have hv := validTuple_sub_const (fun i ↦ g (e i)) (validTuple_embedding e.toEmbedding g hg) B
  have hw := validTuple_comp hv Φ.symm.toAddMonoidHom Φ.symm.injective
  apply not_validTuple_exceptional_of_si_lifts_quarter_prefix hm hnpow
    (fun i ↦ Φ.symm (g (e i) - B)) j _ _ hw
  · intro i
    apply φ.injective
    rw [← hΦ, Φ.apply_symm_apply, map_sub, hprefix]
    simp [B]
  · apply φ.injective
    rw [← hΦ, Φ.apply_symm_apply, map_sub, hq]
    simp [B]

end MinModulus
