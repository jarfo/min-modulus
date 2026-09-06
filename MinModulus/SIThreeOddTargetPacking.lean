import MinModulus.SIOneExtraFibreCover

/-!
# Three opposite-parity extras: actual pair-target packing

For a doubled coherent SI prefix with three odd extras, initial-interval
covers place the three actual removed-coordinate targets high in the half
modulus and force pairwise separation. This proves the first-even bound
for n >= 8, hence all global/even-stratum thresholds, and the binary bound
for n >= 9. Translation and reindexing are included. The target inequalities
are derived from validity, not supplied by a census or an open global gate.
-/

namespace MinModulus
open Finset

/-- A cover inside any actual mapped fibre, together with outside coins,
contradicts validity if a coordinate is omitted. No SI structure is needed. -/
theorem not_validTuple_of_actual_mapped_fibre_cover
    {m n M K : ℕ} {G : Type*} [AddCommGroup G]
    (τ : ZMod M →+ G) (u : Fin m → ZMod M) (g : Fin n → G)
    (f : Fin m → Fin n) (hpref : ∀ i, g (f i) = τ (u i))
    (z : ZMod M) (hcover : ∃ s : Multiset (Fin m), s.card = K ∧ (s.map u).sum = z)
    (t : Multiset (Fin n)) (hcard : K + t.card = n)
    (hsum : τ z + (t.map g).sum = ∑ i, g i)
    (j : Fin n) (hj : ∀ i, f i ≠ j) (hjt : j ∉ t) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨s, hs, hsz⟩ := hcover
  apply not_validTuple_of_multiset_omission g (s.map f + t)
    (by simpa only [Multiset.card_add, Multiset.card_map, hs] using hcard) ?_ j ?_ hg
  · have hmap : ((s.map f).map g).sum = τ z := by
      rw [Multiset.map_map]
      change (s.map (fun i ↦ g (f i))).sum = _
      simp only [hpref]
      simpa only [map_multiset_sum, Multiset.map_map, Function.comp_def] using congrArg τ hsz
    simpa only [Multiset.map_add, Multiset.sum_add, hmap] using hsum
  · intro hmem
    rcases Multiset.mem_add.mp hmem with h | h
    · obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp h
      exact hj i hi
    · exact hjt h

/-- If removing an outside coordinate leaves a subgroup target, that
target avoids the initial interval covered with n-1 prefix coins. -/
theorem three_extra_pair_target_large
    {m M : ℕ} [NeZero M] (hm : 4 ≤ m) {G : Type*} [AddCommGroup G]
    (τ : ZMod M →+ G) (g : Fin (m+3) → G) (hg : ValidTuple g)
    (f : Fin m → Fin (m+3)) (hpref : ∀ i, g (f i) = τ (a i.val : ZMod M))
    (x y : Fin (m+3)) (hxy : x ≠ y) (hx : ∀ i, f i ≠ x)
    (u : ZMod M) (hu : τ u = (∑ i, g i) - g y) :
    5 * (2^(m-1)-1) - (m-2) ≤ u.val := by
  by_contra hsmall
  obtain ⟨s, hcard, hs⟩ := exists_fixed_multiset_sum_of_lt_initial_interval
    (N := M) (d := 3) (by omega : 2 ≤ m) (by omega : u.val < _)
  apply not_validTuple_of_actual_mapped_fibre_cover τ (fun i : Fin m ↦ (a i.val : ZMod M))
    g f hpref u ⟨s, hcard, by simpa only [ZMod.natCast_zmod_val] using hs⟩ {y}
    (by simp; omega) (by simp only [Multiset.map_singleton, Multiset.sum_singleton]; rw [hu]; abel)
    x hx (by simpa only [Multiset.mem_singleton] using hxy) hg

/-- Two removed-coordinate targets must be separated by more than the
prefix sum. Otherwise transferring a copy between those coordinates gives
an actual omitted-coordinate rival through the m-coin prefix cover. -/
theorem three_extra_pair_targets_separated_ordered
    {m M : ℕ} [NeZero M] (hm : 4 ≤ m) {G : Type*} [AddCommGroup G]
    (τ : ZMod M →+ G) (g : Fin (m+3) → G) (hg : ValidTuple g)
    (f : Fin m → Fin (m+3)) (hpref : ∀ i, g (f i) = τ (a i.val : ZMod M))
    (x y z : Fin (m+3)) (hxy : x ≠ y) (hyz : y ≠ z) (hy : ∀ i, f i ≠ y)
    (htotal : (∑ i, g i) = τ (2^m-m-1 : ℕ) + g x + g y + g z)
    (u v : ZMod M) (hu : τ u = (∑ i, g i) - g x)
    (hv : τ v = (∑ i, g i) - g y) (huv : u.val ≤ v.val) :
    u.val + (2^m-m-1) < v.val := by
  by_contra hclose
  let S := 2^m-m-1
  let r := S - (v.val-u.val)
  have hr : r ≤ S := Nat.sub_le _ _
  have hp := Nat.lt_two_pow_self (n := m-1)
  have hpow : 2^m = 2*2^(m-1) := by rw [← pow_succ']; congr 1; omega
  have hinterval : r < (1+2)*(2^(m-1)-1)-(m-2) := by dsimp [S] at hr; omega
  obtain ⟨s, hcard, hs⟩ := exists_fixed_multiset_sum_of_lt_initial_interval
    (N := M) (d := 1) (by omega : 2 ≤ m) hinterval
  have hrval : (r : ZMod M) = (S : ZMod M) + u - v := by
    dsimp [r]
    rw [Nat.cast_sub (by dsimp [S]; omega), Nat.cast_sub huv,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  have hsum : τ (r : ZMod M) + 2 • g x + g z = ∑ i, g i := by
    rw [hrval, map_sub, map_add, hu, hv]
    dsimp [S]
    rw [htotal]
    abel
  apply not_validTuple_of_actual_mapped_fibre_cover τ (fun i : Fin m ↦ (a i.val : ZMod M))
    g f hpref (r : ZMod M) ⟨s, hcard, hs⟩ (Multiset.replicate 2 x + {z})
    (by simp; omega) (by simpa only [Multiset.map_add, Multiset.sum_add,
      Multiset.map_replicate, Multiset.sum_replicate, Multiset.map_singleton,
      Multiset.sum_singleton, add_assoc] using hsum) y hy ?_ hg
  simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton]
  tauto

/-- The separation conclusion does not depend on which target is smaller. -/
theorem three_extra_pair_targets_separated
    {m M : ℕ} [NeZero M] (hm : 4 ≤ m) {G : Type*} [AddCommGroup G]
    (τ : ZMod M →+ G) (g : Fin (m+3) → G) (hg : ValidTuple g)
    (f : Fin m → Fin (m+3)) (hpref : ∀ i, g (f i) = τ (a i.val : ZMod M))
    (x y z : Fin (m+3)) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : ∀ i, f i ≠ x) (hy : ∀ i, f i ≠ y)
    (htotal : (∑ i, g i) = τ (2^m-m-1 : ℕ) + g x + g y + g z)
    (u v : ZMod M) (hu : τ u = (∑ i, g i) - g x)
    (hv : τ v = (∑ i, g i) - g y) :
    u.val + (2^m-m-1) < v.val ∨ v.val + (2^m-m-1) < u.val := by
  rcases le_total u.val v.val with h | h
  · exact Or.inl (three_extra_pair_targets_separated_ordered hm τ g hg f hpref
      x y z hxy hyz hy htotal u v hu hv h)
  · exact Or.inr (three_extra_pair_targets_separated_ordered hm τ g hg f hpref
      y x z hxy.symm hxz hx (by rw [htotal]; abel) v u hv hu h)

/-- Three separated representatives in the top interval force enough
room in the modulus. This is an ordinary integer packing argument. -/
theorem three_separated_top_targets_modulus_bound
    (M C S U V W : ℕ) (hU : C ≤ U) (hV : C ≤ V) (hW : C ≤ W)
    (hUM : U < M) (hVM : V < M) (hWM : W < M)
    (hUV : U+S < V ∨ V+S < U) (hUW : U+S < W ∨ W+S < U)
    (hVW : V+S < W ∨ W+S < V) : C+2*S+3 ≤ M := by
  omega

/-- The three odd extras produce three actual pair targets. Prefix covers
force them into a short top interval and force pairwise separation, giving
a uniform stronger-than-binary bound in all sufficiently large dimensions. -/
theorem modulus_bound_of_valid_doubled_three_odd_extras
    {m M : ℕ} [NeZero M] (hm : 4 ≤ m)
    (g : Fin (m+3) → ZMod (2*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom 2 M (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last m).castSucc.castSucc) = 1)
    (hy : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last (m+1)).castSucc) = 1)
    (hz : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last (m+2))) = 1) :
    (5*(2^(m-1)-1)-(m-2)) + 2*(2^m-m-1) + 3 ≤ M := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  let τ := zmodScaleHom 2 M
  let π := ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
  let x : Fin (m+3) := (Fin.last m).castSucc.castSucc
  let y : Fin (m+3) := (Fin.last (m+1)).castSucc
  let z : Fin (m+3) := Fin.last (m+2)
  let f : Fin m → Fin (m+3) := fun i ↦ i.castSucc.castSucc.castSucc
  have hxy : x ≠ y := by intro h; have h' := congrArg Fin.val h; simp [x, y] at h'
  have hxz : x ≠ z := by intro h; have h' := congrArg Fin.val h; simp [x, z] at h'
  have hyz : y ≠ z := by intro h; have h' := congrArg Fin.val h; simp [y, z] at h'
  have hfx (i : Fin m) : f i ≠ x := by
    intro h; have h' := congrArg Fin.val h; simp only [f, x, Fin.val_castSucc, Fin.val_last] at h'; omega
  have hfy (i : Fin m) : f i ≠ y := by
    intro h; have h' := congrArg Fin.val h; simp only [f, y, Fin.val_castSucc, Fin.val_last] at h'; omega
  have hfz (i : Fin m) : f i ≠ z := by
    intro h; have h' := congrArg Fin.val h; simp only [f, z, Fin.val_castSucc, Fin.val_last] at h'; omega
  have htotal : (∑ i, g i) = τ (2^m-m-1 : ℕ) + g x + g y + g z := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [hpref, ← map_sum, ← Nat.cast_sum, sum_fixed_eq_cover_hole, τ, x, y, z]
  have hπtotal : π (∑ i, g i) = 1 := by
    rw [htotal, map_add, map_add, map_add]
    have hzero : π (τ (2^m-m-1 : ℕ)) = 0 := by
      rw [zmodScaleHom_natCast, map_natCast π, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [hzero]
    rw [show π (g x) = 1 from hx, show π (g y) = 1 from hy,
      show π (g z) = 1 from hz]
    decide
  have hker (j : Fin (m+3)) (hj : π (g j) = 1) : π ((∑ i, g i)-g j) = 0 := by
    rw [map_sub, hπtotal, hj, sub_self]
  obtain ⟨u, hu⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ (hker x hx)
  obtain ⟨v, hv⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ (hker y hy)
  obtain ⟨w, hw⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ (hker z hz)
  have hU := three_extra_pair_target_large hm τ g hg f hpref y x hxy.symm hfy u hu
  have hV := three_extra_pair_target_large hm τ g hg f hpref x y hxy hfx v hv
  have hW := three_extra_pair_target_large hm τ g hg f hpref x z hxz hfx w hw
  have hUV := three_extra_pair_targets_separated hm τ g hg f hpref x y z
    hxy hxz hyz hfx hfy htotal u v hu hv
  have hUW := three_extra_pair_targets_separated hm τ g hg f hpref x z y
    hxz hxy hyz.symm hfx hfz (by rw [htotal]; abel) u w hu hw
  have hVW := three_extra_pair_targets_separated hm τ g hg f hpref y z x
    hyz hxy.symm hxz.symm hfy hfz (by rw [htotal]; abel) v w hv hw
  exact three_separated_top_targets_modulus_bound M _ _ u.val v.val w.val
    hU hV hW u.val_lt v.val_lt w.val_lt hUV hUW hVW

/-- The Mersenne prefix grows past the linear threshold from length five. -/
theorem three_mul_le_mersenne_pred {m : ℕ} (hm : 5 ≤ m) :
    3*m ≤ 2^(m-1)-1 := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hp : 2^m = 2*2^(m-1) := by rw [← pow_succ']; congr 1; omega
    simp only [Nat.add_sub_cancel] at *
    omega

/-- Three opposite-parity extras force at least the strongest even-stratum
threshold, in every n>=8. No criticality or global conjecture is assumed. -/
theorem first_even_lower_bound_of_valid_doubled_three_odd_extras
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m)
    (g : Fin (m+3) → ZMod (2*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3)))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = zmodScaleHom 2 M (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last m).castSucc.castSucc)) = 1)
    (hy : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+1)).castSucc)) = 1)
    (hz : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+2)))) = 1) :
    2^(m+3)-2 ≤ 2*M := by
  have hbound := modulus_bound_of_valid_doubled_three_odd_extras (by omega : 4 ≤ m)
    (fun i ↦ g (e i)) (validTuple_embedding e.toEmbedding g hg) hpref hx hy hz
  have hgrowth := three_mul_le_mersenne_pred hm
  have hpow : 2^m = 2*2^(m-1) := by rw [← pow_succ']; congr 1; omega
  have hpow3 : 2^(m+3) = 16*2^(m-1) := by rw [pow_add, hpow]; norm_num; ring
  omega

/-- From n>=9 the packing bound even exceeds the binary threshold. -/
theorem binary_lower_bound_of_valid_doubled_three_odd_extras
    {m M : ℕ} [NeZero M] (hm : 6 ≤ m)
    (g : Fin (m+3) → ZMod (2*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3)))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = zmodScaleHom 2 M (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last m).castSucc.castSucc)) = 1)
    (hy : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+1)).castSucc)) = 1)
    (hz : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+2)))) = 1) :
    2^(m+3) ≤ 2*M := by
  have hbound := modulus_bound_of_valid_doubled_three_odd_extras (by omega : 4 ≤ m)
    (fun i ↦ g (e i)) (validTuple_embedding e.toEmbedding g hg) hpref hx hy hz
  have hgrowth := three_mul_le_mersenne_pred (m := m-1) (by omega)
  have hpow0 : 2^(m-1) = 2*2^(m-2) := by rw [← pow_succ']; congr 1; omega
  have hpow : 2^m = 2*2^(m-1) := by rw [← pow_succ']; congr 1; omega
  have hpow3 : 2^(m+3) = 16*2^(m-1) := by rw [pow_add, hpow]; norm_num; ring
  have he : m-1-1 = m-2 := by omega
  rw [he] at hgrowth
  omega

/-- Translation and reindexing retain the first-even threshold; parity is
measured relative to the actual prefix coset. -/
theorem first_even_lower_bound_of_valid_translated_doubled_three_odd_extras
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m)
    (g : Fin (m+3) → ZMod (2*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (b : ZMod (2*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = zmodScaleHom 2 M (a i.val : ZMod M)+b)
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last m).castSucc.castSucc)) =
      ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) b+1)
    (hy : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+1)).castSucc)) =
      ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) b+1)
    (hz : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+2)))) =
      ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) b+1) :
    2^(m+3)-2 ≤ 2*M := by
  apply first_even_lower_bound_of_valid_doubled_three_odd_extras hm
    (fun i ↦ g (e i)-b) (validTuple_sub_const _ (validTuple_embedding e.toEmbedding g hg) b)
    (Equiv.refl _)
  · intro i; simp only [Equiv.refl_apply, hpref, add_sub_cancel_right]
  · simp only [Equiv.refl_apply, map_sub, hx]; abel
  · simp only [Equiv.refl_apply, map_sub, hy]; abel
  · simp only [Equiv.refl_apply, map_sub, hz]; abel

/-- The actual translated class satisfies the global and every positive
exact-stratum threshold, not only a conditional packing statement. -/
theorem global_and_stratum_lower_bound_of_valid_doubled_three_odd_extras
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m)
    (g : Fin (m+3) → ZMod (2*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (b : ZMod (2*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = zmodScaleHom 2 M (a i.val : ZMod M)+b)
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last m).castSucc.castSucc)) =
      ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) b+1)
    (hy : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+1)).castSucc)) =
      ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) b+1)
    (hz : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (e (Fin.last (m+2)))) =
      ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) b+1) :
    globalBound (m+3) ≤ 2*M ∧ ∀ s : ℕ, 0 < s → stratumBound (m+3) s ≤ 2*M := by
  have hbound := first_even_lower_bound_of_valid_translated_doubled_three_odd_extras
    hm g hg e b hpref hx hy hz
  have hlog : 0 < Nat.log 2 (m+3) := Nat.log_pos (by norm_num) (by omega)
  have hpow : 2 ≤ 2^Nat.log 2 (m+3) := by
    exact Nat.le_trans (by norm_num : 2 ≤ 2^1) (Nat.pow_le_pow_right (by omega) hlog)
  constructor
  · exact (Nat.sub_le_sub_left hpow _).trans hbound
  · intro s hs
    have hmin : 1 ≤ min s (Nat.log 2 (m+3)) := by omega
    have hpow' : 2 ≤ 2^min s (Nat.log 2 (m+3)) := by
      exact Nat.le_trans (by norm_num : 2 ≤ 2^1) (Nat.pow_le_pow_right (by omega) hmin)
    exact (Nat.sub_le_sub_left hpow' _).trans hbound

end MinModulus
