/-
# Two independently lifted extras separated by a quarter of the modulus

In the half quotient M=2H, extras separated by H select both sheets of
the one-hole Mersenne-coin cover. Their doubled lifts differ by M, so the
cover yields a full-length rival. At the lone hole one extra is negative
one, which instead forces coherent prefix lifts and the global bound.
-/
import MinModulus.SILiftMinusOne

namespace MinModulus
open Finset

/-- An antipodal pair of doubles and a remaining quotient representation
give an actual rival: one of the two coordinates occurs at least twice. -/
theorem not_validTuple_of_antipodal_double_pair_and_quotient_cover
    {n M : ℕ} [NeZero M] (g : Fin n → ZMod (2 * M)) (lo hi : Fin n)
    (hpair : 2 • g hi = 2 • g lo + M) (s : Multiset (Fin n))
    (hcard : s.card + 2 = n)
    (hproj : ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      ((s.map g).sum + 2 • g lo) =
        ZMod.castHom (dvd_mul_left M 2) (ZMod M) (∑ i, g i)) : ¬ ValidTuple g := by
  intro hg
  have bad (k : Fin n) (hsum : ((s + Multiset.replicate 2 k).map g).sum = ∑ i, g i) : False := by
    have hk := multiset_count_eq_one_of_validTuple g hg (s + Multiset.replicate 2 k)
      (by simpa using hcard) hsum k
    simp only [Multiset.count_add, Multiset.count_replicate_self] at hk
    omega
  rcases eq_or_eq_add_half_of_castHom_eq _ _ hproj with heq | heq
  · apply bad lo
    simpa only [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate] using heq
  · apply bad hi
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, hpair]
    rw [← add_assoc, heq, add_assoc, half_add_half (M := M) rfl, add_zero]

/-- Two antipodal quotient extras select a lower-half remainder. With
one extra and m-1 prefix coins, only the translated greedy holes can fail. -/
theorem exists_multiset_sum_of_fixed_prefix_antipodal_extras_except_holes
    {m M H : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M = 2 * H)
    (hH : H ≤ 2 ^ m - 1) (g : Fin (m + 2) → ZMod M)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = (a i.val : ZMod M))
    (hpair : g (Fin.last m).castSucc = g (Fin.last (m + 1)) + H)
    (z : ZMod M)
    (hx : z ≠ g (Fin.last m).castSucc + ((2 ^ m - m : ℕ) : ZMod M))
    (hy : z ≠ g (Fin.last (m + 1)) + ((2 ^ m - m : ℕ) : ZMod M)) :
    ∃ s : Multiset (Fin (m + 2)), s.card = m ∧ (s.map g).sum = z := by
  classical
  let x := (Fin.last m).castSucc
  let y := Fin.last (m + 1)
  have hHpos : 0 < H := by have := Nat.pos_of_ne_zero (NeZero.ne M); omega
  let w := z - g y
  have hwval := w.val_lt
  have hchoice : ∃ k : Fin (m + 2), (k = x ∨ k = y) ∧
      (z - g k).val < H := by
    by_cases hw : w.val < H
    · exact ⟨y, Or.inr rfl, hw⟩
    · refine ⟨x, Or.inl rfl, ?_⟩
      have hnat : w.val - H < H := by omega
      have hnatM : w.val - H < M := by omega
      have heq : z - g x = ((w.val - H : ℕ) : ZMod M) := by
        rw [Nat.cast_sub (by omega : H ≤ w.val), ZMod.natCast_zmod_val]
        rw [hpair]
        dsimp only [w]
        abel
      rw [heq, ZMod.val_natCast, Nat.mod_eq_of_lt hnatM]
      exact hnat
  obtain ⟨k, hk, hkval⟩ := hchoice
  let r := (z - g k).val
  have hr : r ≤ 2 * (2 ^ (m - 1) - 1) := by
    have hp := Nat.lt_two_pow_self (n := m - 1)
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
    dsimp only [r]
    omega
  have hsum : g k + (r : ZMod M) = z := by
    dsimp only [r]
    rw [ZMod.natCast_zmod_val]
    abel
  have hrne : r ≠ 2 * (2 ^ (m - 1) - 1) - ((m - 1) - 1) := by
    intro heq
    have hp := Nat.lt_two_pow_self (n := m - 1)
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
    have hrF : r = 2 ^ m - m := by omega
    rw [hrF] at hsum
    rcases hk with rfl | rfl
    · exact hx hsum.symm
    · exact hy hsum.symm
  have hrep : ∃ v : Multiset (Fin m), v.card = m - 1 ∧
      (v.map (fun i ↦ (a i.val : ZMod M))).sum = (r : ZMod M) := by
    by_cases hend : r = 2 * (2 ^ (m - 1) - 1)
    · apply exists_fixed_multiset_sum_of_nat_coin_representation_card (by omega)
        (Multiset.replicate 2 (m - 1))
      · simp; omega
      · intro i hi
        have := (Multiset.mem_replicate.mp hi).2
        omega
      · simp [a, hend]; omega
    · obtain ⟨s, hs, hmem, hval⟩ := exists_mersenne_coin_multiset_of_lt_two_mul
        (by omega : 1 ≤ m - 1) r (by omega) hrne
      exact exists_fixed_multiset_sum_of_nat_coin_representation_card
        (m := m) (N := M) (K := m - 1) (by omega) s hs
        (fun i hi ↦ by have := hmem i hi; omega) hval
  obtain ⟨v, hv, hvsum⟩ := hrep
  refine ⟨k ::ₘ v.map (fun i : Fin m ↦ i.castSucc.castSucc), ?_, ?_⟩
  · simp only [Multiset.card_cons, Multiset.card_map, hv]; omega
  · rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_map]
    change g k + (v.map (fun i : Fin m ↦ g i.castSucc.castSucc)).sum = z
    simp only [hprefix]
    rw [hvsum]
    exact hsum

/-- Quarter separation of the two extras yields the full numerical bound
at any positive even half modulus, with no coherence assumption. -/
theorem global_lower_bound_of_valid_si_lifts_quarter_pair
    {m M H : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M = 2 * H)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc.castSucc) = (a i.val : ZMod M))
    (hq : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last m).castSucc) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) + H) :
    globalBound (m + 2) ≤ 2 * M := by
  classical
  by_contra hbound
  have hcrit : 2 * M < globalBound (m + 2) := by omega
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let x := (Fin.last m).castSucc
  let y := Fin.last (m + 1)
  let X := ∑ i, g i
  have hH : H ≤ 2 ^ m - 2 := by
    have ht : 2 ≤ Nat.log 2 (m + 2) :=
      (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by norm_num; omega)
    have hD : 4 ≤ 2 ^ Nat.log 2 (m + 2) := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) ht
    have hp : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
    unfold globalBound at hcrit
    omega
  have hyneg : π (g y) ≠ -1 := by
    intro hy
    have := global_lower_bound_of_valid_si_lifts_neg_one hm g hg hprefix hy
    omega
  have hxneg : π (g x) ≠ -1 := by
    intro hx
    let p := Equiv.swap x y
    have hpfix (i : Fin m) : p i.castSucc.castSucc = i.castSucc.castSucc := by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro heq
        exact Fin.castSucc_ne_last i (Fin.castSucc_injective (m + 1) heq)
      · exact Fin.castSucc_ne_last i.castSucc
    have hv := validTuple_embedding p.toEmbedding g hg
    have hb := global_lower_bound_of_valid_si_lifts_neg_one hm (fun i ↦ g (p i)) hv
      (by intro i; rw [hpfix]; exact hprefix i)
      (by change π (g (p y)) = -1; simpa only [p, Equiv.swap_apply_right] using hx)
    omega
  have hsum : π X = ((2 ^ m - m - 1 : ℕ) : ZMod M) + π (g x) + π (g y) := by
    dsimp only [X, x, y]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, map_add, map_add, map_sum]
    congr 2
    simp only [π, hprefix, ← Nat.cast_sum, sum_fixed_eq_cover_hole]
  have hF : ((2 ^ m - m - 1 : ℕ) : ZMod M) + 1 = ((2 ^ m - m : ℕ) : ZMod M) := by
    have hn : (2 ^ m - m - 1) + 1 = 2 ^ m - m := by
      have := Nat.lt_two_pow_self (n := m); omega
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ ↦ (k : ZMod M)) hn
  let z := π (X - 2 • g y)
  have hz : z = ((2 ^ m - m - 1 : ℕ) : ZMod M) + H := by
    dsimp only [z]
    rw [map_sub, map_nsmul, hsum, hq]
    simp only [nsmul_eq_mul]
    ring
  have hne_x : z ≠ π (g x) + ((2 ^ m - m : ℕ) : ZMod M) := by
    intro heq
    apply hyneg
    rw [hz, hq, ← hF] at heq
    linear_combination -heq
  have hne_y : z ≠ π (g y) + ((2 ^ m - m : ℕ) : ZMod M) := by
    intro heq
    apply hxneg
    rw [hz, ← hF] at heq
    have hh : (H : ZMod M) + H = 0 := half_add_half hM
    linear_combination hq - heq + hh
  have hpair : 2 • g x = 2 • g y + M := by
    have hp := two_nsmul_quarter_extra_eq_two_nsmul_one_add_half hM (g x - g y + 1) 1
      (by
        change π _ = _
        rw [map_add, map_sub, map_one, hq]
        push_cast
        ring)
      (by simp)
    simp only [nsmul_eq_mul] at hp ⊢
    linear_combination hp
  obtain ⟨s, hs, hproj⟩ := exists_multiset_sum_of_fixed_prefix_antipodal_extras_except_holes
    hm hM (by omega) (fun i ↦ π (g i)) hprefix hq z hne_x hne_y
  apply not_validTuple_of_antipodal_double_pair_and_quotient_cover g y x hpair s
    (by omega : s.card + 2 = m + 2) ?_ hg
  change π _ = π X
  rw [map_add, map_multiset_sum, Multiset.map_map]
  change (s.map (fun i ↦ π (g i))).sum + π (2 • g y) = π X
  rw [hproj]
  dsimp only [z]
  rw [map_sub]
  abel

/-- Quotient affine transport and reindexing preserve the general
quarter-pair numerical bound, with every original lift bit arbitrary. -/
theorem global_lower_bound_of_valid_quotient_affine_short_prefix_quarter_pair
    {m M H : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M = 2 * H)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc.castSucc)) = φ (a i.val) + b)
    (hq : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (Fin.last m).castSucc)) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (Fin.last (m + 1)))) + φ H) :
    globalBound (m + 2) ≤ 2 * M := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_lift_castHom (dvd_mul_left M 2) φ
  let B : ZMod (2 * M) := b.val
  have hv := validTuple_sub_const (fun i ↦ g (e i)) (validTuple_embedding e.toEmbedding g hg) B
  have hw := validTuple_comp hv Φ.symm.toAddMonoidHom Φ.symm.injective
  have hnorm (i : Fin (m + 2)) : φ (π (Φ.symm (g (e i) - B))) = π (g (e i)) - b := by
    rw [← hΦ, Φ.apply_symm_apply, map_sub]
    simp [B, π]
  apply global_lower_bound_of_valid_si_lifts_quarter_pair hm hM
    (fun i ↦ Φ.symm (g (e i) - B)) hw
  · intro i
    apply φ.injective
    rw [hnorm, hprefix, add_sub_cancel_right]
  · apply φ.injective
    rw [map_add, hnorm, hnorm, hq]
    abel

/-- The completed quarter-pair cover excludes the exceptional modulus
without assuming any coherent lift bits or unrestricted global inputs. -/
theorem not_validTuple_exceptional_of_si_lifts_quarter_pair
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g i.castSucc.castSucc) = (a i.val : ZMod (globalBound (m + 1))))
    (hq : ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
      (g (Fin.last m).castSucc) =
        ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
          (g (Fin.last (m + 1))) + (globalBound (m + 1) / 2 : ℕ)) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (globalBound (m + 1)) := ⟨by omega⟩
  have ht : 2 ≤ Nat.log 2 (m + 1) :=
    (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by norm_num; omega)
  have hD := Nat.pow_log_le_self 2 (show m + 1 ≠ 0 by omega)
  have hp := Nat.lt_two_pow_self (n := m)
  have hmPow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
  have htPow : 2 ^ Nat.log 2 (m + 1) = 2 * 2 ^ (Nat.log 2 (m + 1) - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hM : globalBound (m + 1) = 2 * (globalBound (m + 1) / 2) := by
    unfold globalBound
    omega
  have hb := global_lower_bound_of_valid_si_lifts_quarter_pair hm hM g hg hprefix hq
  have hcrit := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ m + 1) hnpow
  change 2 * globalBound (m + 1) < globalBound (m + 2) at hcrit
  omega

/-- Direct affine G3 consumer for quarter separation between the extras. -/
theorem not_validTuple_exceptional_of_quotient_affine_short_prefix_quarter_pair
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (e : Equiv.Perm (Fin (m + 2)))
    (φ : ZMod (globalBound (m + 1)) ≃+ ZMod (globalBound (m + 1)))
    (b : ZMod (globalBound (m + 1)))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g (e i.castSucc.castSucc)) = φ (a i.val) + b)
    (hq : ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
      (g (e (Fin.last m).castSucc)) =
        ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
          (g (e (Fin.last (m + 1)))) + φ (globalBound (m + 1) / 2 : ℕ)) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (globalBound (m + 1)) := ⟨by omega⟩
  letI : NeZero (2 * globalBound (m + 1)) := ⟨by omega⟩
  let π := ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_lift_castHom (dvd_mul_left (globalBound (m + 1)) 2) φ
  let B : ZMod (2 * globalBound (m + 1)) := b.val
  have hv := validTuple_sub_const (fun i ↦ g (e i)) (validTuple_embedding e.toEmbedding g hg) B
  have hw := validTuple_comp hv Φ.symm.toAddMonoidHom Φ.symm.injective
  have hnorm (i : Fin (m + 2)) : φ (π (Φ.symm (g (e i) - B))) = π (g (e i)) - b := by
    rw [← hΦ, Φ.apply_symm_apply, map_sub]
    simp [B, π]
  apply not_validTuple_exceptional_of_si_lifts_quarter_pair hm hnpow
    (fun i ↦ Φ.symm (g (e i) - B)) _ _ hw
  · intro i
    apply φ.injective
    rw [hnorm, hprefix, add_sub_cancel_right]
  · apply φ.injective
    rw [map_add, hnorm, hnorm, hq]
    abel

end MinModulus
