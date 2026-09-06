/-
# Binary threshold for independently lifted quarter-separated extras

Two extras separated by a quarter of the original modulus force the full
binary lower bound when their remaining prefix is superincreasing in the
half quotient. At the Mersenne-cover hole, validity forces coherent lifts;
normalizing them to powers of two gives a binary-subset rival. Thus the
hole is excluded throughout the subbinary range, not only below the global
envelope. No compatibility of the original prefix lift bits is assumed.
-/
import MinModulus.SILiftQuarterPair

namespace MinModulus
open Finset

/-- Binary powers plus an order-two last entry and its quarter lift
cannot be valid below the binary modulus. A subset expansion supplies
the quotient target, and repeated last entries pad the exact length. -/
theorem not_validTuple_of_power_prefix_quarter_pair_lt_two_pow
    {m M H : ℕ} [NeZero M] (hM : M = 2 * H) (hH : H < 2 ^ m)
    (g : Fin (m + 2) → ZMod (2 * M))
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((2 ^ i.val : ℕ) : ZMod (2 * M)))
    (hy : g (Fin.last (m + 1)) = M)
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last m).castSucc) = H) :
    ¬ ValidTuple g := by
  classical
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let x := (Fin.last m).castSucc
  let y := Fin.last (m + 1)
  let T := 2 ^ m - H - 1
  have hHpos : 0 < H := by have := Nat.pos_of_ne_zero (NeZero.ne M); omega
  have hT : T < 2 ^ m := by dsimp [T]; omega
  obtain ⟨S, hS⟩ := exists_finset_fin_sum_two_pow_eq hT
  have hcard : S.card ≤ m := by simpa using Finset.card_le_univ S
  let s := S.val.map (fun i : Fin m ↦ i.castSucc.castSucc) +
    Multiset.replicate (m - S.card) y
  have hscard : s.card = m := by simp only [s, Multiset.card_add, Multiset.card_map,
    Multiset.card_replicate, Finset.card_val]; omega
  have hssum : (s.map g).sum = (T : ZMod (2 * M)) + (m - S.card) • g y := by
    simp only [s, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, Multiset.map_map, Function.comp_def, hprefix]
    congr 1
    rw [← Finset.sum_eq_multiset_sum, ← Nat.cast_sum, hS]
  have hsum : π (∑ i, g i) = ((2 ^ m - 1 : ℕ) : ZMod M) + H := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, map_add, map_add, map_sum, hx, hy, map_natCast]
    simp only [hprefix, map_natCast, ZMod.natCast_self, add_zero]
    congr 1
    rw [← Nat.cast_sum, Fin.sum_univ_eq_sum_range, sum_two_pow]
  have hpair : 2 • g x = 2 • g y + M := by
    have hc := nsmul_eq_of_even_of_castHom_eq (by decide : Even 2) (g x)
      (H : ZMod (2 * M)) (by simpa only [map_natCast] using hx)
    have hh : (M : ZMod (2 * M)) + M = 0 := half_add_half rfl
    have hcast : (M : ZMod (2 * M)) = 2 • (H : ZMod (2 * M)) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul] using
        congrArg (fun k : ℕ ↦ (k : ZMod (2 * M))) hM
    rw [hc, ← hcast, hy, two_nsmul, hh, zero_add]
  apply not_validTuple_of_antipodal_double_pair_and_quotient_cover g y x hpair s
    (by omega : s.card + 2 = m + 2)
  rw [map_add, hssum, map_add, map_natCast, map_nsmul, map_nsmul, hy, map_natCast,
    ZMod.natCast_self, smul_zero, smul_zero, add_zero, add_zero, hsum]
  have hnat : T + M = (2 ^ m - 1) + H := by dsimp [T]; omega
  simpa only [Nat.cast_add, ZMod.natCast_self, add_zero] using
    congrArg (fun k : ℕ ↦ (k : ZMod M)) hnat

/-- A lift of one through an even half modulus is self-inverse and fixes
the half-modulus element. No abstract unit choice is needed. -/
theorem mul_self_and_half_eq_of_castHom_eq_one
    {M H : ℕ} [NeZero M] (hM : M = 2 * H) (c : ZMod (2 * M))
    (hc : ZMod.castHom (dvd_mul_left M 2) (ZMod M) c = 1) :
    c * c = 1 ∧ c * M = M := by
  have h2M : (2 : ZMod (2 * M)) * M = 0 := by
    simpa only [two_mul] using (half_add_half (M := M) rfl)
  have hcast : (M : ZMod (2 * M)) = 2 * (H : ZMod (2 * M)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using congrArg (fun k : ℕ ↦ (k : ZMod (2 * M))) hM
  have hMM : (M : ZMod (2 * M)) * M = 0 := by
    calc
      (M : ZMod (2 * M)) * M = M * (2 * H) := congrArg (fun z ↦ (M : ZMod (2 * M)) * z) hcast
      _ = (2 * M) * H := by ring
      _ = 0 := by rw [h2M, zero_mul]
  rcases eq_or_eq_add_half_of_castHom_eq c 1 (by simpa only [map_one] using hc) with heq | heq
  · rw [heq]; simp
  · rw [heq]
    constructor
    · linear_combination hMM + h2M
    · linear_combination hMM

/-- At a negative-one cover exception, actual coherence and the lifted
one normalize the tuple to binary powers and an order-four/order-two pair. -/
theorem not_validTuple_of_si_lifts_neg_one_quarter_pair_subbinary
    {m M H : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M = 2 * H) (hH : H < 2 ^ m)
    (g : Fin (m + 2) → ZMod (2 * M))
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc.castSucc) = (a i.val : ZMod M))
    (hy : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) = -1)
    (hq : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last m).castSucc) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) + H) : ¬ ValidTuple g := by
  intro hg
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let one : Fin (m + 2) := (⟨1, by omega⟩ : Fin m).castSucc.castSucc
  let zero : Fin (m + 2) := (⟨0, by omega⟩ : Fin m).castSucc.castSucc
  let y := Fin.last (m + 1)
  let x := (Fin.last m).castSucc
  let b := g zero
  let v := fun i ↦ g i - b
  have hv : ValidTuple v := validTuple_sub_const g hg b
  have hb : π b = 0 := (hprefix ⟨0, by omega⟩).trans (by norm_num [a])
  have hzero : v zero = 0 := sub_self b
  have hpref : ∀ i : Fin m, π (v i.castSucc.castSucc) = (a i.val : ZMod M) := by
    intro i
    rw [map_sub, hprefix, hb, sub_zero]
  have hyv : π (v y) = -1 := by rw [map_sub, hy, hb, sub_zero]
  have hqv : π (v x) = π (v y) + H := by
    rw [map_sub, map_sub, hq, hb]
    abel
  let c := v one
  have hc : π c = 1 := (hpref ⟨1, by omega⟩).trans (by norm_num [a])
  have hcoh := scaled_fixed_short_prefix_of_valid_si_lifts_neg_one (by omega : 2 ≤ m)
    v hv hpref hzero hyv
  have hysum : v y + c = (M : ZMod (2 * M)) := by
    have hproj : π (v y + c) = π 0 := by rw [map_add, hyv, hc, map_zero]; simp
    rcases eq_or_eq_add_half_of_castHom_eq (v y + c) 0 hproj with hz | hh
    · exact False.elim (not_validTuple_of_double_eq_distinct_pair v y one zero
        (Fin.castSucc_ne_last ((⟨1, by omega⟩ : Fin m).castSucc)).symm
        (by rw [hzero, smul_zero]; exact hz.symm) hv)
    · simpa using hh
  obtain ⟨hcc, hcm⟩ := mul_self_and_half_eq_of_castHom_eq_one hM c hc
  let φ : ZMod (2 * M) →+ ZMod (2 * M) :=
    { toFun := fun z ↦ c * z, map_zero' := mul_zero c, map_add' := mul_add c }
  have hvc : ValidTuple (fun i ↦ c * v i) := by
    apply validTuple_of_comp φ
    convert hv using 1
    funext i
    change c * (c * v i) = v i
    rw [← mul_assoc, hcc, one_mul]
  have hw : ValidTuple (fun i ↦ c * v i + 1) := by
    simpa only [sub_neg_eq_add] using validTuple_sub_const (fun i ↦ c * v i) hvc (-1)
  apply not_validTuple_of_power_prefix_quarter_pair_lt_two_pow hM hH
    (fun i ↦ c * v i + 1) _ _ _ hw
  · intro i
    rw [hcoh]
    change c * (c * (a i.val : ZMod (2 * M))) + 1 = _
    rw [← mul_assoc, hcc, one_mul]
    have hnat : a i.val + 1 = 2 ^ i.val := by
      have hp : 0 < 2 ^ i.val := by positivity
      unfold a
      omega
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ ↦ (k : ZMod (2 * M))) hnat
  · change c * v y + 1 = (M : ZMod (2 * M))
    linear_combination c * hysum - hcc + hcm
  · change π (c * v x + 1) = H
    rw [map_add, map_mul, map_one, hc, one_mul, hqv, hyv]
    ring

/-- Quarter-separated extras cannot occur below the full binary modulus.
This strengthens the global envelope to every exact-stratum threshold. -/
theorem two_pow_le_of_valid_si_lifts_quarter_pair
    {m M H : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M = 2 * H)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc.castSucc) = (a i.val : ZMod M))
    (hq : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last m).castSucc) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) + H) :
    2 ^ (m + 2) ≤ 2 * M := by
  classical
  by_contra hbound
  have hH : H < 2 ^ m := by
    have hp : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
    omega
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let x := (Fin.last m).castSucc
  let y := Fin.last (m + 1)
  let X := ∑ i, g i
  have hyneg : π (g y) ≠ -1 := by
    intro hy
    exact not_validTuple_of_si_lifts_neg_one_quarter_pair_subbinary hm hM hH g hprefix hy hq hg
  have hxneg : π (g x) ≠ -1 := by
    intro hx
    let p := Equiv.swap x y
    have hpfix (i : Fin m) : p i.castSucc.castSucc = i.castSucc.castSucc := by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro heq
        exact Fin.castSucc_ne_last i (Fin.castSucc_injective (m + 1) heq)
      · exact Fin.castSucc_ne_last i.castSucc
    have hq' : π (g y) = π (g x) + H := by
      have hh : (H : ZMod M) + H = 0 := half_add_half hM
      linear_combination -hq - hh
    apply not_validTuple_of_si_lifts_neg_one_quarter_pair_subbinary hm hM hH (fun i ↦ g (p i))
      (by intro i; rw [hpfix]; exact hprefix i)
      (by change π (g (p y)) = -1; simpa only [p, Equiv.swap_apply_right] using hx)
      (by
        change π (g (p x)) = π (g (p y)) + H
        simpa only [p, Equiv.swap_apply_left, Equiv.swap_apply_right] using hq')
      (validTuple_embedding p.toEmbedding g hg)
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

/-- The full binary bound is preserved by reindexing and affine
automorphisms of the actual quotient, with arbitrary upstairs lift bits. -/
theorem two_pow_le_of_valid_quotient_affine_short_prefix_quarter_pair
    {m M H : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M = 2 * H)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc.castSucc)) = φ (a i.val) + b)
    (hq : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (Fin.last m).castSucc)) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (Fin.last (m + 1)))) + φ H) :
    2 ^ (m + 2) ≤ 2 * M := by
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
  apply two_pow_le_of_valid_si_lifts_quarter_pair hm hM
    (fun i ↦ Φ.symm (g (e i) - B)) hw
  · intro i
    apply φ.injective
    rw [hnorm, hprefix, add_sub_cancel_right]
  · apply φ.injective
    rw [map_add, hnorm, hnorm, hq]
    abel

/-- In particular, this independent-lift class satisfies every stratum
threshold, including the actual critical G1 threshold. -/
theorem stratum_lower_bound_of_valid_quotient_affine_short_prefix_quarter_pair
    {m M H : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M = 2 * H)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc.castSucc)) = φ (a i.val) + b)
    (hq : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (Fin.last m).castSucc)) =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (Fin.last (m + 1)))) + φ H)
    (t : ℕ) : stratumBound (m + 2) t ≤ 2 * M := by
  exact (Nat.sub_le _ _).trans
    (two_pow_le_of_valid_quotient_affine_short_prefix_quarter_pair hm hM g hg e φ b hprefix hq)

end MinModulus
