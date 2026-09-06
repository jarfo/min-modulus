import MinModulus.SIThreeExtensionBound

/-!
# One-extra covers and a two-large-parity-fibre binary bound

A valid coherent SI prefix with one arbitrary extra covers its cyclic group
with two additional coins below twice its binary threshold. Applying this
cover to the actual even fibre excludes subbinary tuples with a doubled
SI prefix, one further even entry, and two odd entries, in every n >= 7.
This is a structured class, not arbitrary three-omission deletion.
-/

namespace MinModulus

open Finset

/-- An initial-interval prefix representation, together with k copies of
the extra, represents the actual target with the specified total budget. -/
theorem exists_one_extra_sum_of_residual_cover
    {m M c k : ℕ} [NeZero M] (hm : 4 ≤ m) (hc : c + k ≤ 5) (hc2 : c ≤ 2)
    (u : Fin (m + 1) → ZMod M)
    (hp : ∀ i : Fin m, u i.castSucc = (a i.val : ZMod M)) (z : ZMod M) (q : ℤ)
    (hlo : 0 ≤ (z.val : ℤ) - k * (u (Fin.last m)).val + q*M)
    (hhi : (z.val : ℤ) - k * (u (Fin.last m)).val + q*M <
      (6 - ((c + k : ℕ) : ℤ)) * (2 ^ (m-1)-1) - m + 2) :
    ∃ s : Multiset (Fin (m + 1)), s.card = m + 3 - c ∧ (s.map u).sum = z := by
  let R : ℤ := z.val - k * (u (Fin.last m)).val + q*M
  let r := R.toNat
  have hr : (r : ℤ) = R := Int.toNat_of_nonneg hlo
  obtain ⟨s, hscard, hssum⟩ := exists_fixed_sum_three_extra_budget (N := M) hm hc
    (by rw [hr]; exact hhi)
  refine ⟨s.map Fin.castSucc + Multiset.replicate k (Fin.last m), ?_, ?_⟩
  · simp only [Multiset.card_add, Multiset.card_map, Multiset.card_replicate, hscard]
    omega
  · simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_map,
      Function.comp_def, hp, hssum, Multiset.map_replicate, Multiset.sum_replicate]
    have heq : (r : ℤ) + k * (u (Fin.last m)).val = z.val + q*M := by
      rw [hr]; dsimp [R]; ring
    have hcast := congrArg (fun x : ℤ ↦ (x : ZMod M)) heq
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_self, mul_zero, add_zero, nsmul_eq_mul] using hcast

/-- Four nonnegative translates and one wrapped translate cover the
whole interval in the localized one-extra range. -/
theorem one_extra_large_budget_interval_cover
    (m L M X R : ℤ) (hm : 4 ≤ m) (hL : 2*m-1 ≤ L)
    (hM : M ≤ 8*L+7) (hXlo : 2*L+m ≤ X)
    (hXhi : 2*L-m+1+X < M) (hRlo : 0 ≤ R) (hRhi : R < M) :
    (R < 6*L-m+2) ∨
    (X ≤ R ∧ R < X+5*L-m+2) ∨
    (2*X ≤ R ∧ R < 2*X+4*L-m+2) ∨
    (3*X ≤ R ∧ R < 3*X+3*L-m+2) ∨
    (2*X-M ≤ R ∧ R < 2*X-M+4*L-m+2) := by
  omega

/-- A valid one-extra coherent SI tuple covers its whole cyclic group
with two additional coins whenever the modulus is below twice its binary
threshold. The extra is arbitrary, and no tuple census is used. -/
theorem exists_multiset_sum_of_valid_one_extra_below_double_binary
    {m M : ℕ} [NeZero M] (hm : 4 ≤ m) (hM : M < 2 ^ (m + 2))
    (u : Fin (m + 1) → ZMod M) (hu : ValidTuple u)
    (hpref : ∀ i : Fin m, u i.castSucc = (a i.val : ZMod M)) (z : ZMod M) :
    ∃ s : Multiset (Fin (m + 1)), s.card = m + 3 ∧ (s.map u).sum = z := by
  have hp := Nat.lt_two_pow_self (n := m - 1)
  have hmexp := Nat.lt_two_pow_self (n := m)
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpow2 : 2 ^ (m + 2) = 8 * 2 ^ (m - 1) := by
    rw [pow_add, hpow]; norm_num; ring
  have hgrowth := twice_mul_sub_one_le_mersenne_pred hm
  by_cases hnext : u (Fin.last m) = (a m : ZMod M)
  · have hfull : ∀ i, u i = (a i.val : ZMod M) := by
      intro i; exact Fin.lastCases hnext (fun j ↦ hpref j) i
    obtain ⟨s, hcard, hs⟩ := exists_fixed_multiset_sum_of_modulus_le_initial_interval
      (m := m + 1) (d := 3) (by omega) (by
        simp only [Nat.add_sub_cancel]
        omega : M ≤ (3+2)*(2^((m+1)-1)-1)-((m+1)-2)) z
    exact ⟨s, by omega, by simpa only [hfull] using hs⟩
  let L : ℤ := 2 ^ (m - 1) - 1
  have hLcast : ((2 ^ (m - 1) - 1 : ℕ) : ℤ) = L := by
    dsimp [L]; rw [Int.natCast_sub (by omega), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have hScast : ((2 ^ m - m - 1 : ℕ) : ℤ) = 2*L-m+1 := by
    have hpowz : (2 : ℤ)^m = 2*(2 : ℤ)^(m-1) := by exact_mod_cast hpow
    rw [Int.natCast_sub (by omega), Int.natCast_sub (by omega), Nat.cast_pow]
    push_cast; dsimp [L]; omega
  have hLbound : 2*(m : ℤ)-1 ≤ L := by
    have h' : (((2*m-1 : ℕ) : ℤ)) ≤ ((2^(m-1)-1 : ℕ) : ℤ) := by exact_mod_cast hgrowth
    have hcast : ((2*m-1 : ℕ) : ℤ) = 2*m-1 := by omega
    rwa [hcast, hLcast] at h'
  have hMz : (M : ℤ) ≤ 8*L+7 := by
    have h' : (M : ℤ) < 8*(2 : ℤ)^(m-1) := by exact_mod_cast (hpow2 ▸ hM)
    dsimp [L]; omega
  have hzlo : 0 ≤ (z.val : ℤ) := by exact_mod_cast Nat.zero_le z.val
  have hzhi : (z.val : ℤ) < M := by exact_mod_cast z.val_lt
  by_cases hsmall : (M : ℤ) ≤ 6*L-m+2
  · apply exists_one_extra_sum_of_residual_cover (c := 0) (k := 0) hm (by omega) (by omega)
      u hpref z 0
    · change 0 ≤ (z.val : ℤ)-0*(u (Fin.last m)).val+0*M; omega
    · change (z.val : ℤ)-0*(u (Fin.last m)).val+0*M < (6-0)*L-m+2
      omega
  have hMlo : 4*(2^(m-1)-1)+4 ≤ M := by
    have h' : (4 : ℤ)*((2^(m-1)-1 : ℕ) : ℤ)+4 ≤ M := by rw [hLcast]; omega
    exact_mod_cast h'
  have hloc := fixed_prefix_extra_localization (by omega : 3 ≤ m) hMlo u hu hpref hnext
  have hXlo : 2*L+m ≤ ((u (Fin.last m)).val : ℤ) := by
    have h' : (4 : ℤ)*((2^(m-1)-1 : ℕ) : ℤ)+1 ≤
        ((2^m-m-1 : ℕ) : ℤ)+(u (Fin.last m)).val := by exact_mod_cast hloc.1
    rw [hLcast, hScast] at h'; omega
  have hXhi : 2*L-m+1+((u (Fin.last m)).val : ℤ) < M := by
    have h' : ((2^m-m-1 : ℕ) : ℤ)+(u (Fin.last m)).val < M := by exact_mod_cast hloc.2
    rwa [hScast] at h'
  rcases one_extra_large_budget_interval_cover m L M (u (Fin.last m)).val z.val
      (by exact_mod_cast hm) hLbound hMz hXlo hXhi hzlo hzhi with h | h | h | h | h
  · apply exists_one_extra_sum_of_residual_cover (c := 0) (k := 0) hm (by omega) (by omega) u hpref z 0
    · change 0 ≤ (z.val : ℤ)-0*(u (Fin.last m)).val+0*M; omega
    · change (z.val : ℤ)-0*(u (Fin.last m)).val+0*M < (6-0)*L-m+2; omega
  · apply exists_one_extra_sum_of_residual_cover (c := 0) (k := 1) hm (by omega) (by omega) u hpref z 0
    · omega
    · change (z.val : ℤ)-1*(u (Fin.last m)).val+0*M < (6-1)*L-m+2; omega
  · apply exists_one_extra_sum_of_residual_cover (c := 0) (k := 2) hm (by omega) (by omega) u hpref z 0
    · omega
    · change (z.val : ℤ)-2*(u (Fin.last m)).val+0*M < (6-2)*L-m+2; omega
  · apply exists_one_extra_sum_of_residual_cover (c := 0) (k := 3) hm (by omega) (by omega) u hpref z 0
    · omega
    · change (z.val : ℤ)-3*(u (Fin.last m)).val+0*M < (6-3)*L-m+2; omega
  · apply exists_one_extra_sum_of_residual_cover (c := 0) (k := 2) hm (by omega) (by omega) u hpref z 1
    · omega
    · change (z.val : ℤ)-2*(u (Fin.last m)).val+1*M < (6-2)*L-m+2; omega

/-- A doubled coherent prefix, one additional even entry and two odd
entries cannot form a valid subbinary tuple. The actual even fibre has a
full n-coin cover at half the modulus, giving an omitted-odd rival. -/
theorem not_validTuple_of_doubled_three_extra_one_even_subbinary
    {m M : ℕ} [NeZero M] (hm : 4 ≤ m) (hupper : 2*M < 2^(m+3))
    (g : Fin (m + 3) → ZMod (2*M))
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom 2 M (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last m).castSucc.castSucc) = 0)
    (hy : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last (m+1)).castSucc) = 1)
    (hz : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last (m+2))) = 1) :
    ¬ ValidTuple g := by
  intro hg
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  let τ := zmodScaleHom 2 M
  let π := ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
  obtain ⟨t, ht⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hx
  let u : Fin (m+1) → ZMod M := Fin.lastCases t (fun i : Fin m ↦ (a i.val : ZMod M))
  have hu : ValidTuple u := validTuple_fixed_extra_of_valid_scaled_short_prefix
    (fun i : Fin (m+2) ↦ g i.castSucc)
    (validTuple_embedding ⟨Fin.castSucc, Fin.castSucc_injective (m+2)⟩ g hg)
    hpref (Fin.last m).castSucc (by simp) t ht.symm
  have hMsmall : M < 2^(m+2) := by
    have hpow : 2^(m+3) = 2*2^(m+2) := by
      rw [show m+3=(m+2)+1 by omega, pow_succ']
    omega
  have hsumzero : π (∑ i, g i) = 0 := by
    rw [map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have hpzero (i : Fin m) : π (g i.castSucc.castSucc.castSucc) = 0 := by
      rw [hpref, zmodScaleHom_natCast]
      rw [map_natCast π, Nat.cast_mul]
      rw [ZMod.natCast_self, zero_mul]
    simp only [hpzero, Finset.sum_const_zero, π, hx, hy, hz, zero_add]
    decide
  obtain ⟨z, hztotal⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hsumzero
  obtain ⟨s, hscard, hssum⟩ := exists_multiset_sum_of_valid_one_extra_below_double_binary
    hm hMsmall u hu (by intro i; simp [u]) z
  let e : Fin (m+1) → Fin (m+3) := fun i ↦ i.castSucc.castSucc
  have hmap (i : Fin (m+1)) : g (e i) = τ (u i) := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [e, u, Fin.lastCases_last] using ht.symm
    · simpa only [e, u, Fin.lastCases_castSucc] using hpref j
  have hsum : ((s.map e).map g).sum = ∑ i, g i := by
    rw [Multiset.map_map]
    change (s.map (fun i ↦ g (e i))).sum = _
    simp only [hmap]
    have h := congrArg τ hssum
    have h' : (s.map (fun i ↦ τ (u i))).sum = τ z := by
      simpa only [map_multiset_sum, Multiset.map_map, Function.comp_def] using h
    exact h'.trans hztotal
  apply not_validTuple_of_multiset_omission g (s.map e)
    (by simpa only [Multiset.card_map] using hscard) hsum (Fin.last (m+2)) _ hg
  intro hmem
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
  have hval := congrArg Fin.val hi
  simp only [e, Fin.val_castSucc, Fin.val_last] at hval
  omega

/-- The preceding actual-fibre construction gives the full binary bound,
not merely the global envelope, for this two-large-parity-fibre class. -/
theorem binary_lower_bound_of_valid_doubled_three_extra_one_even
    {m M : ℕ} [NeZero M] (hm : 4 ≤ m)
    (g : Fin (m+3) → ZMod (2*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3)))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = zmodScaleHom 2 M (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last m).castSucc.castSucc)) = 0)
    (hy : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+1)).castSucc)) = 1)
    (hz : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+2)))) = 1) :
    2^(m+3) ≤ 2*M := by
  by_contra h
  exact not_validTuple_of_doubled_three_extra_one_even_subbinary hm (by omega)
    (fun i ↦ g (e i)) hpref hx hy hz (validTuple_embedding e.toEmbedding g hg)

/-- Translating the original tuple preserves the binary obstruction; the
extra parity classes are specified relative to the actual prefix coset. -/
theorem binary_lower_bound_of_valid_translated_doubled_three_extra_one_even
    {m M : ℕ} [NeZero M] (hm : 4 ≤ m)
    (g : Fin (m+3) → ZMod (2*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (b : ZMod (2*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = zmodScaleHom 2 M (a i.val : ZMod M) + b)
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last m).castSucc.castSucc)) =
      ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) b)
    (hy : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+1)).castSucc)) =
      ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) b + 1)
    (hz : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+2)))) =
      ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) b + 1) :
    2^(m+3) ≤ 2*M := by
  apply binary_lower_bound_of_valid_doubled_three_extra_one_even hm
    (fun i ↦ g (e i) - b)
    (validTuple_sub_const _ (validTuple_embedding e.toEmbedding g hg) b) (Equiv.refl _)
  · intro i; simp only [Equiv.refl_apply, hpref, add_sub_cancel_right]
  · simp only [Equiv.refl_apply, map_sub, hx, sub_self]
  · simp only [Equiv.refl_apply, map_sub, hy]; abel
  · simp only [Equiv.refl_apply, map_sub, hz]; abel

/-- The actual-fibre binary theorem directly implies the global lower bound. -/
theorem global_lower_bound_of_valid_doubled_three_extra_one_even
    {m M : ℕ} [NeZero M] (hm : 4 ≤ m)
    (g : Fin (m+3) → ZMod (2*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3)))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = zmodScaleHom 2 M (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last m).castSucc.castSucc)) = 0)
    (hy : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+1)).castSucc)) = 1)
    (hz : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+2)))) = 1) :
    globalBound (m+3) ≤ 2*M :=
  (Nat.sub_le _ _).trans (binary_lower_bound_of_valid_doubled_three_extra_one_even hm g hg e hpref hx hy hz)

/-- The binary theorem dominates every exact-stratum threshold. -/
theorem stratum_lower_bound_of_valid_doubled_three_extra_one_even
    {m M : ℕ} [NeZero M] (hm : 4 ≤ m) (s : ℕ)
    (g : Fin (m+3) → ZMod (2*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3)))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = zmodScaleHom 2 M (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last m).castSucc.castSucc)) = 0)
    (hy : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+1)).castSucc)) = 1)
    (hz : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+2)))) = 1) :
    stratumBound (m+3) s ≤ 2*M :=
  (Nat.sub_le _ _).trans (binary_lower_bound_of_valid_doubled_three_extra_one_even hm g hg e hpref hx hy hz)

end MinModulus
