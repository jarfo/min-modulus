/-
# Full two-extra global bound for arbitrary coherent SI multipliers

For every n>=5, a valid tuple containing c*(2^i-1)+b for i<n-2 satisfies
globalBound n, even when c is not a unit. Both extra entries are arbitrary.
No unrestricted G1/G2/G3 assumption or new finite tuple census is used.

Normalize c to a unit times a divisor d of N=d*M. Prefix validity reflects
to the fixed m=n-2 tuple at M, forcing d<=4 in a global counterexample.
The d=1 case is the preceding unit-affine two-extra theorem.

At index two, a subgroup extra completes the longer scaled SI prefix;
otherwise the extras sum into the subgroup and a prefix-only rival works.
At index three, extras either lie in the subgroup, share a coset, or have
opposite residues. Reflected bounds and m-term covers exclude all cases.
The small index-three arithmetic exception uses the proved odd n=5 bound.

At index four, only residues 2 and an odd residue survive those exclusions.
The (m-1)-term single-hole cover, with three copies of the odd extra y,
forces x=2*y+4. The parity-saving (m-2)-term cover, with three x's and one y,
forces y mod M=-3. The prefix's fixed-set power gap then closes the entire
tuple under u -> 2*u+4, so the affine-doubling global theorem applies.

Affine normalization gives the arbitrary-multiplier theorem and a direct
uniform G3 consumer. These require coherence in the full modulus; they
do not combine nonunits with arbitrary independent half-modulus shifts.
Exact G1/G2 strata for this class are proved separately in SITwoMultiplierStrata.
-/
import MinModulus.SITwoExtensionStrata

namespace MinModulus
open Finset

/-- Kernel elements of reduction modulo the subgroup index have an
actual preimage under the canonical scaling map. -/
theorem exists_zmodScaleHom_eq_of_castHom_eq_zero
    {d M : ℕ} [NeZero (d * M)] (x : ZMod (d * M))
    (hx : ZMod.castHom (dvd_mul_right d M) (ZMod d) x = 0) :
    ∃ z : ZMod M, zmodScaleHom d M z = x := by
  have hdvd : d ∣ x.val := by
    rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at hx
    exact hx
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨(k : ZMod M), ?_⟩
  rw [zmodScaleHom_natCast, ← hk, ZMod.natCast_zmod_val]

/-- Scaling after reduction computes multiplication by the subgroup index. -/
theorem zmodScaleHom_castHom {d M : ℕ} [NeZero (d * M)] (x : ZMod (d * M)) :
    zmodScaleHom d M (ZMod.castHom (dvd_mul_left M d) (ZMod M) x) = d • x := by
  have hx := ZMod.natCast_zmod_val x
  have hπ := congrArg (ZMod.castHom (dvd_mul_left M d) (ZMod M)) hx
  rw [map_natCast] at hπ
  rw [← hπ, zmodScaleHom_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]

/-- Reduction modulo an index has the expected natural representative. -/
theorem castHom_index_val {d M : ℕ} [NeZero d] [NeZero (d * M)]
    (x : ZMod (d * M)) :
    (ZMod.castHom (dvd_mul_right d M) (ZMod d) x).val = x.val % d := by
  have hπ := congrArg (ZMod.castHom (dvd_mul_right d M) (ZMod d)) (ZMod.natCast_zmod_val x)
  rw [map_natCast] at hπ
  rw [← hπ, ZMod.val_natCast]

/-- A prefix cover transported by an additive map, with non-reference
extra multiplicities, gives a genuine full-tuple rival. -/
theorem not_validTuple_of_mapped_fixed_block_two_extra_rival
    {m n M K α β : ℕ} {G : Type*} [AddCommGroup G]
    (τ : ZMod M →+ G) (g : Fin n → G) (f : Fin m ↪ Fin n)
    (hprefix : ∀ i, g (f i) = τ (a i.val : ZMod M))
    (x y : Fin n) (hxy : x ≠ y) (hx : ∀ i, f i ≠ x)
    (hα : α ≠ 1) (hcard : K + α + β = n) (z : ZMod M)
    (hcover : ∃ s : Multiset (Fin m), s.card = K ∧
      (s.map (fun i ↦ (a i.val : ZMod M))).sum = z)
    (hsum : τ z + α • g x + β • g y = ∑ i, g i) : ¬ ValidTuple g := by
  classical
  intro hg
  obtain ⟨s, hscard, hssum⟩ := hcover
  let t := s.map f + Multiset.replicate α x + Multiset.replicate β y
  have htcard : t.card = n := by simp [t, hscard, hcard]
  have htval : ((s.map f).map g).sum = τ z := by
    rw [Multiset.map_map]
    change (s.map (fun i ↦ g (f i))).sum = _
    simp only [hprefix]
    have ht := congrArg τ hssum
    simpa only [map_multiset_sum, Multiset.map_map, Function.comp_def] using ht
  have htsum : (t.map g).sum = ∑ i, g i := by
    simpa only [t, Multiset.map_add, Multiset.sum_add, htval,
      Multiset.map_replicate, Multiset.sum_replicate] using hsum
  have hxnot : x ∉ s.map f := by
    intro hmem
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
    exact hx i hi
  have hc := multiset_count_eq_one_of_validTuple g hg t htcard htsum x
  have hcother : (Multiset.replicate β y).count x = 0 :=
    Multiset.count_eq_zero.mpr (by intro hmem; exact hxy (Multiset.mem_replicate.mp hmem).2)
  simp only [t, Multiset.count_add, Multiset.count_eq_zero.mpr hxnot,
    Multiset.count_replicate_self, hcother, zero_add, add_zero] at hc
  exact hα hc

/-- A full residue cover from the initial Mersenne interval. -/
theorem exists_fixed_multiset_sum_of_modulus_le_initial_interval
    {m M d : ℕ} [NeZero M] (hm : 2 ≤ m)
    (hM : M ≤ (d + 2) * (2 ^ (m - 1) - 1) - (m - 2)) (z : ZMod M) :
    ∃ s : Multiset (Fin m), s.card = m - 1 + d ∧
      (s.map (fun i ↦ (a i.val : ZMod M))).sum = z := by
  have hz := z.val_lt
  obtain ⟨s, hs, hsum⟩ := exists_fixed_multiset_sum_of_lt_initial_interval
    (N := M) hm (by omega : z.val < (d + 2) * (2 ^ (m - 1) - 1) - (m - 2))
  exact ⟨s, hs, by simpa only [ZMod.natCast_zmod_val] using hsum⟩

/-- Retaining a scaled shorter prefix reflects validity to the fixed set. -/
theorem valid_fixed_of_valid_divisor_fixed_short_prefix
    {m d M : ℕ} (g : Fin (m + 2) → ZMod (d * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((d * a i.val : ℕ) : ZMod (d * M))) :
    Valid m M := by
  have hv := validTuple_embedding ⟨Fin.castSucc, Fin.castSucc_injective (m + 1)⟩ g hg
  exact valid_fixed_of_valid_divisor_fixed_prefix (fun i ↦ g i.castSucc) hv hprefix

/-- Any extra lying in the prefix subgroup yields an actual valid
one-extra SI extension in the smaller cyclic modulus. -/
theorem validTuple_fixed_extra_of_valid_scaled_short_prefix
    {m d M : ℕ} (g : Fin (m + 2) → ZMod (d * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M))
    (j : Fin (m + 2)) (hj : m ≤ j.val) (z : ZMod M)
    (hjz : g j = zmodScaleHom d M z) :
    ValidTuple (Fin.lastCases z (fun i : Fin m ↦ (a i.val : ZMod M))) := by
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
  change ValidTuple (fun i : Fin (m + 1) ↦ g (p i.castSucc)) at hv
  apply validTuple_of_comp (zmodScaleHom d M)
  have heq : (fun i : Fin (m + 1) ↦ g (p i.castSucc)) =
      (fun i ↦ zmodScaleHom d M (Fin.lastCases z (fun k : Fin m ↦ (a k.val : ZMod M)) i)) := by
    funext i
    refine Fin.lastCases ?_ (fun k ↦ ?_) i
    · simp [p, x, hjz]
    · simp [hfix, hprefix]
  rwa [← heq]

/-- Completing the scaled longer prefix gives the preceding full bound. -/
theorem global_lower_bound_of_valid_divisor_short_prefix_and_next
    {m d M : ℕ} [NeZero (d * M)] (hm : 2 ≤ m)
    (g : Fin (m + 2) → ZMod (d * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((d * a i.val : ℕ) : ZMod (d * M)))
    (j : Fin (m + 2)) (hj : m ≤ j.val)
    (hnext : g j = ((d * a m : ℕ) : ZMod (d * M))) :
    globalBound (m + 2) ≤ d * M := by
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
  apply global_lower_bound_of_valid_divisor_fixed_prefix (by omega)
    (fun i ↦ g (p i)) (validTuple_embedding p.toEmbedding g hg)
  intro i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · simpa [p, x] using hnext
  · rw [hfix, hprefix]
    rfl

/-- Five times the preceding two-step endpoint dominates the next global
envelope, including the two small dimensions. -/
theorem globalBound_add_two_le_five_mul {m : ℕ} (hm : 3 ≤ m) :
    globalBound (m + 2) ≤ 5 * globalBound m := by
  by_cases hm5 : 5 ≤ m
  · have hlin : 5 * m ≤ 2 ^ m := by
      induction m, hm5 using Nat.le_induction with
      | base => norm_num
      | succ m hm ih => rw [pow_succ']; omega
    have hlog := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
    have hfive : 5 * 2 ^ Nat.log 2 m ≤ 2 ^ m := (Nat.mul_le_mul_left 5 hlog).trans hlin
    have hpowle : 2 ^ Nat.log 2 m ≤ 2 ^ m := by omega
    have hdelta : 0 < 2 ^ Nat.log 2 (m + 2) := by positivity
    have hp : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
    unfold globalBound
    omega
  · have hcases : m = 3 ∨ m = 4 := by omega
    rcases hcases with rfl | rfl <;> norm_num [globalBound]

/-- An arbitrary coherent multiplier can have subgroup index at most
four in a putative two-extra global counterexample. -/
theorem divisor_le_four_of_valid_divisor_fixed_short_prefix_critical
    {m d M : ℕ} [NeZero (d * M)] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (d * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((d * a i.val : ℕ) : ZMod (d * M)))
    (hcrit : d * M < globalBound (m + 2)) : d ≤ 4 := by
  have hNpos := Nat.pos_of_ne_zero (NeZero.ne (d * M))
  have hMpos := Nat.pos_of_mul_pos_left hNpos
  letI : NeZero M := ⟨ne_of_gt hMpos⟩
  have hv := valid_fixed_of_valid_divisor_fixed_short_prefix g hg hprefix
  have hcard := Fintype.card_le_of_injective _ (validTuple_injective _ (validTuple_fixed_of_valid hv))
  simp only [Fintype.card_fin, ZMod.card] at hcard
  have hbound := (nmin_eq (by omega : 2 ≤ m)).2 ⟨by omega, hv⟩
  change globalBound m ≤ M at hbound
  have hratio := globalBound_add_two_le_five_mul hm
  nlinarith

/-- Sum normal form for a divisor-scaled shorter prefix. -/
theorem sum_divisor_fixed_short_prefix
    {m d M : ℕ} (g : Fin (m + 2) → ZMod (d * M))
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M)) :
    (∑ i, g i) = zmodScaleHom d M ((2 ^ m - m - 1 : ℕ) : ZMod M) +
      g (Fin.last m).castSucc + g (Fin.last (m + 1)) := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [hprefix, ← map_sum, ← Nat.cast_sum, sum_fixed_eq_cover_hole]

/-- If the sum of the extras is in the prefix subgroup, a full-length
prefix cover already gives a competing multiset. -/
theorem not_validTuple_of_scaled_short_prefix_extra_sum_zero
    {m d M : ℕ} [NeZero M] [NeZero (d * M)] (hm : 3 ≤ m)
    (hM : M ≤ 5 * (2 ^ (m - 1) - 1) - (m - 2))
    (g : Fin (m + 2) → ZMod (d * M))
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M))
    (hsum : ZMod.castHom (dvd_mul_right d M) (ZMod d)
      (g (Fin.last m).castSucc + g (Fin.last (m + 1))) = 0) : ¬ ValidTuple g := by
  let τ := zmodScaleHom d M
  obtain ⟨w, hw⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hsum
  let z := ((2 ^ m - m - 1 : ℕ) : ZMod M) + w
  have hc := exists_fixed_multiset_sum_of_modulus_le_initial_interval (d := 3) (by omega) hM z
  let f : Fin m ↪ Fin (m + 2) := ⟨fun i ↦ i.castSucc.castSucc,
    (Fin.castSucc_injective (m + 1)).comp (Fin.castSucc_injective m)⟩
  apply not_validTuple_of_mapped_fixed_block_two_extra_rival τ g f hprefix
    (Fin.last m).castSucc (Fin.last (m + 1)) (Fin.castSucc_ne_last _)
    (by intro i hi; exact Fin.castSucc_ne_last i (Fin.castSucc_injective (m + 1) hi))
    (by omega : 0 ≠ 1) (by omega : m - 1 + 3 + 0 + 0 = m + 2) z hc
  dsimp only [τ]
  simp only [zero_nsmul, add_zero, z, map_add, hw]
  rw [sum_divisor_fixed_short_prefix g hprefix]
  abel

/-- Extras in the same subgroup coset admit a doubled-extra rival when
the m-term prefix sumset covers the smaller modulus. -/
theorem not_validTuple_of_scaled_short_prefix_extra_difference_zero
    {m d M : ℕ} [NeZero M] [NeZero (d * M)] (hm : 3 ≤ m)
    (hM : M ≤ 3 * (2 ^ (m - 1) - 1) - (m - 2))
    (g : Fin (m + 2) → ZMod (d * M))
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M))
    (hdiff : ZMod.castHom (dvd_mul_right d M) (ZMod d)
      (g (Fin.last m).castSucc - g (Fin.last (m + 1))) = 0) : ¬ ValidTuple g := by
  let τ := zmodScaleHom d M
  obtain ⟨w, hw⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hdiff
  let z := ((2 ^ m - m - 1 : ℕ) : ZMod M) + w
  have hc := exists_fixed_multiset_sum_of_modulus_le_initial_interval (d := 1) (by omega) hM z
  let f : Fin m ↪ Fin (m + 2) := ⟨fun i ↦ i.castSucc.castSucc,
    (Fin.castSucc_injective (m + 1)).comp (Fin.castSucc_injective m)⟩
  apply not_validTuple_of_mapped_fixed_block_two_extra_rival τ g f hprefix
    (Fin.last m).castSucc (Fin.last (m + 1)) (Fin.castSucc_ne_last _)
    (by intro i hi; exact Fin.castSucc_ne_last i (Fin.castSucc_injective (m + 1) hi))
    (by omega : 0 ≠ 1) (by omega : m - 1 + 1 + 0 + 2 = m + 2) z hc
  dsimp only [τ]
  simp only [zero_nsmul, add_zero, z, map_add, hw]
  rw [sum_divisor_fixed_short_prefix g hprefix]
  simp only [two_nsmul]
  abel

/-- At index at least three, an extra in the prefix subgroup reflects
to a valid longer SI prefix at a modulus that is already too small. -/
theorem not_validTuple_of_divisor_short_prefix_zero_extra_of_three_le
    {m d M : ℕ} [NeZero M] [NeZero (d * M)] (hm : 3 ≤ m) (hd : 3 ≤ d)
    (hcrit : d * M < globalBound (m + 2))
    (g : Fin (m + 2) → ZMod (d * M))
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M))
    (j : Fin (m + 2)) (hj : m ≤ j.val)
    (hjzero : ZMod.castHom (dvd_mul_right d M) (ZMod d) (g j) = 0) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨z, hz⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hjzero
  have hv := validTuple_fixed_extra_of_valid_scaled_short_prefix g hg hprefix j hj z hz.symm
  have hbound := global_lower_bound_of_valid_fixed_prefix (by omega) _ hv
    (by intro i; simp only [Fin.lastCases_castSucc])
  have hratio := globalBound_succ_le_three_mul (by omega : 2 ≤ m + 1)
  nlinarith

/-- In the globally critical doubled case, the subgroup modulus lies
inside the one-extra completion interval. -/
theorem half_modulus_le_completion_bound_of_short_critical
    {m M : ℕ} (hm : 3 ≤ m) (hcrit : 2 * M < globalBound (m + 2)) :
    M ≤ 2 ^ (m + 1) - 3 := by
  have hp := Nat.lt_two_pow_self (n := m + 1)
  have hpow : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ']
  have hlog : 2 ≤ Nat.log 2 (m + 2) :=
    (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by norm_num; omega)
  have hdelta : 4 ≤ 2 ^ Nat.log 2 (m + 2) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hlog
  unfold globalBound at hcrit
  omega

/-- With two spare terms the prefix covers every residue below twice
the binary prefix endpoint. -/
theorem modulus_le_two_extra_initial_cover
    {m M : ℕ} (hm : 3 ≤ m) (hM : M ≤ 2 ^ (m + 1) - 2) :
    M ≤ 5 * (2 ^ (m - 1) - 1) - (m - 2) := by
  have hp := succ_le_two_pow_pred m hm
  have hpow : 2 ^ (m + 1) = 4 * 2 ^ (m - 1) := by
    rw [show m + 1 = (m - 1) + 2 by omega, pow_add]; ring
  omega

/-- An index-two extra in the prefix subgroup completes the longer
scaled SI prefix and contradicts global criticality. -/
theorem not_validTuple_of_doubled_short_prefix_zero_extra
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (hcrit : 2 * M < globalBound (m + 2))
    (g : Fin (m + 2) → ZMod (2 * M))
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom 2 M (a i.val : ZMod M))
    (j : Fin (m + 2)) (hj : m ≤ j.val)
    (hjzero : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g j) = 0) : ¬ ValidTuple g := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  intro hg
  obtain ⟨z, hz⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hjzero
  have hv := validTuple_fixed_extra_of_valid_scaled_short_prefix g hg hprefix j hj z hz.symm
  have hfull := eq_fixed_of_valid_fixed_prefix_of_modulus_le (by omega)
    (half_modulus_le_completion_bound_of_short_critical hm hcrit) _ hv
    (by intro i; simp only [Fin.lastCases_castSucc])
  have hznext : z = (a m : ZMod M) := by
    simpa only [Fin.lastCases_last, Fin.val_last] using congrFun hfull (Fin.last m)
  have hnext : g j = ((2 * a m : ℕ) : ZMod (2 * M)) := by
    rw [← hz, hznext, zmodScaleHom_natCast]
  have hbound := global_lower_bound_of_valid_divisor_short_prefix_and_next (by omega) g hg
    (by simpa only [zmodScaleHom_natCast] using hprefix) j hj hnext
  omega

/-- Both nonzero index-two residue classes sum to zero. -/
theorem zmod_two_extra_cases (x y : ZMod 2) : x = 0 ∨ y = 0 ∨ x + y = 0 := by
  revert x y
  decide

/-- The doubled coherent shorter prefix satisfies the full global bound. -/
theorem global_lower_bound_of_valid_doubled_fixed_short_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((2 * a i.val : ℕ) : ZMod (2 * M))) :
    globalBound (m + 2) ≤ 2 * M := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  by_contra hc
  have hcrit : 2 * M < globalBound (m + 2) := by omega
  have hpre : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom 2 M (a i.val : ZMod M) := by
    simpa only [zmodScaleHom_natCast] using hprefix
  let π := ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
  rcases zmod_two_extra_cases (π (g (Fin.last m).castSucc)) (π (g (Fin.last (m + 1)))) with hx | hy | hsum
  · exact not_validTuple_of_doubled_short_prefix_zero_extra hm hcrit g hpre
      (Fin.last m).castSucc (by simp) hx hg
  · exact not_validTuple_of_doubled_short_prefix_zero_extra hm hcrit g hpre
      (Fin.last (m + 1)) (by simp) hy hg
  · have hM := half_modulus_le_completion_bound_of_short_critical hm hcrit
    exact not_validTuple_of_scaled_short_prefix_extra_sum_zero hm
      (modulus_le_two_extra_initial_cover hm (by omega)) g hpre
      (by simpa only [map_add] using hsum) hg

/-- At index three, the smaller modulus is covered with only m terms.
The sole small arithmetic exception is excluded by the proved odd n=5
bound, not an additional global input. -/
theorem modulus_le_m_coin_cover_of_valid_triple_critical
    {m M : ℕ} (hm : 3 ≤ m) (hcrit : 3 * M < globalBound (m + 2))
    (g : Fin (m + 2) → ZMod (3 * M)) (hg : ValidTuple g) :
    M ≤ 3 * (2 ^ (m - 1) - 1) - (m - 2) := by
  by_cases hm5 : 5 ≤ m
  · have hp := three_mul_sub_one_le_mersenne_pred hm5
    have hdelta : 0 < 2 ^ Nat.log 2 (m + 2) := by positivity
    have hpow : 2 ^ (m + 2) = 8 * 2 ^ (m - 1) := by
      rw [show m + 2 = (m - 1) + 3 by omega, pow_add]; ring
    unfold globalBound at hcrit
    omega
  · have hcases : m = 3 ∨ m = 4 := by omega
    rcases hcases with rfl | rfl
    · norm_num [globalBound] at hcrit ⊢
      by_contra hc
      have hM : M = 9 := by omega
      have hodd : Odd (3 * M) := by rw [hM]; norm_num
      have := odd_min_five hodd g hg
      omega
    · norm_num [globalBound] at hcrit ⊢
      omega

/-- Two nonzero distinct classes modulo three are opposite. -/
theorem zmod_three_extra_cases (x y : ZMod 3) :
    x = 0 ∨ y = 0 ∨ x = y ∨ x + y = 0 := by
  revert x y
  decide

/-- A tripled coherent shorter prefix satisfies the full global bound. -/
theorem global_lower_bound_of_valid_tripled_fixed_short_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (3 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((3 * a i.val : ℕ) : ZMod (3 * M))) :
    globalBound (m + 2) ≤ 3 * M := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (3 * M) := ⟨by omega⟩
  by_contra hc
  have hcrit : 3 * M < globalBound (m + 2) := by omega
  have hpre : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom 3 M (a i.val : ZMod M) := by
    simpa only [zmodScaleHom_natCast] using hprefix
  have hM := modulus_le_m_coin_cover_of_valid_triple_critical hm hcrit g hg
  let π := ZMod.castHom (dvd_mul_right 3 M) (ZMod 3)
  rcases zmod_three_extra_cases (π (g (Fin.last m).castSucc)) (π (g (Fin.last (m + 1)))) with
    hx | hy | hdiff | hsum
  · exact not_validTuple_of_divisor_short_prefix_zero_extra_of_three_le hm (by omega)
      hcrit g hpre (Fin.last m).castSucc (by simp) hx hg
  · exact not_validTuple_of_divisor_short_prefix_zero_extra_of_three_le hm (by omega)
      hcrit g hpre (Fin.last (m + 1)) (by simp) hy hg
  · exact not_validTuple_of_scaled_short_prefix_extra_difference_zero hm hM g hpre
      (by
        change π (g (Fin.last m).castSucc - g (Fin.last (m + 1))) = 0
        rw [map_sub, hdiff, sub_self]) hg
  · have hhalf := half_modulus_le_completion_bound_of_short_critical hm
      (by omega : 2 * M < globalBound (m + 2))
    exact not_validTuple_of_scaled_short_prefix_extra_sum_zero hm
      (modulus_le_two_extra_initial_cover hm (by omega)) g hpre
      (by simpa only [map_add] using hsum) hg

/-- The (m-1)-term SI cover has just one possible hole below `2^m-2`. -/
theorem exists_fixed_multiset_sum_card_pred_except_hole
    {m M : ℕ} [NeZero M] (hm : 2 ≤ m) (hM : M ≤ 2 ^ m - 2)
    (z : ZMod M) (hne : z.val ≠ 2 ^ m - m) :
    ∃ s : Multiset (Fin m), s.card = m - 1 ∧
      (s.map (fun i ↦ (a i.val : ZMod M))).sum = z := by
  have hz := z.val_lt
  have hp := Nat.lt_two_pow_self (n := m - 1)
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt_two_mul
    (by omega : 1 ≤ m - 1) z.val (by omega) (by omega)
  obtain ⟨v, hv, hval⟩ := exists_fixed_multiset_sum_of_nat_coin_representation_card
    (N := M) (by omega : 0 < m) s hs (fun i hi ↦ by have := hmem i hi; omega) hsum
  exact ⟨v, hv, by simpa only [ZMod.natCast_zmod_val] using hval⟩

/-- The residual index-four classes are an even class 2 and an odd
class, after possibly swapping the two extras. -/
theorem zmod_four_extra_cases (x y : ZMod 4) :
    x = 0 ∨ y = 0 ∨ x = y ∨ x + y = 0 ∨
      (x = 2 ∧ (y = 1 ∨ y = 3)) ∨ (y = 2 ∧ (x = 1 ∨ x = 3)) := by
  revert x y
  decide

/-- At index four, tripling the odd extra forces the even extra to be
its affine double. The unique cover hole determines the relation. -/
theorem even_extra_eq_double_of_valid_quadrupled_short_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M ≤ 2 ^ m - 2)
    (g : Fin (m + 2) → ZMod (4 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom 4 M (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_right 4 M) (ZMod 4) (g (Fin.last m).castSucc) = 2)
    (hy : ZMod.castHom (dvd_mul_right 4 M) (ZMod 4) (g (Fin.last (m + 1))) = 1 ∨
      ZMod.castHom (dvd_mul_right 4 M) (ZMod 4) (g (Fin.last (m + 1))) = 3) :
    g (Fin.last m).castSucc = 2 * g (Fin.last (m + 1)) + 4 := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (4 * M) := ⟨by omega⟩
  let τ := zmodScaleHom 4 M
  let x := g (Fin.last m).castSucc
  let y := g (Fin.last (m + 1))
  have hzero : ZMod.castHom (dvd_mul_right 4 M) (ZMod 4) (x - 2 * y) = 0 := by
    simp only [map_sub, map_mul, map_ofNat, x, y, hx]
    rcases hy with hy | hy <;> rw [hy] <;> decide
  obtain ⟨w, hw⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hzero
  let σ : ZMod M := ((2 ^ m - m - 1 : ℕ) : ZMod M)
  let z := σ + w
  have hz : z.val = 2 ^ m - m := by
    by_contra hne
    have hcover := exists_fixed_multiset_sum_card_pred_except_hole (by omega) hM z hne
    let f : Fin m ↪ Fin (m + 2) := ⟨fun i ↦ i.castSucc.castSucc,
      (Fin.castSucc_injective (m + 1)).comp (Fin.castSucc_injective m)⟩
    apply not_validTuple_of_mapped_fixed_block_two_extra_rival τ g f hprefix
      (Fin.last m).castSucc (Fin.last (m + 1)) (Fin.castSucc_ne_last _)
      (by intro i hi; exact Fin.castSucc_ne_last i (Fin.castSucc_injective (m + 1) hi))
      (by omega : 0 ≠ 1) (by omega : m - 1 + 0 + 3 = m + 2) z hcover ?_ hg
    dsimp only [τ, z]
    rw [map_add, hw, sum_divisor_fixed_short_prefix g hprefix]
    dsimp [σ, x, y]
    simp only [nsmul_eq_mul]
    ring
  have hp := Nat.lt_two_pow_self (n := m)
  have hσ : σ + 1 = ((2 ^ m - m : ℕ) : ZMod M) := by
    have hn : 2 ^ m - m - 1 + 1 = 2 ^ m - m := by omega
    simpa only [Nat.cast_add, Nat.cast_one, σ] using congrArg (fun k : ℕ ↦ (k : ZMod M)) hn
  have hwone : w = 1 := by
    have hzc : z = ((2 ^ m - m : ℕ) : ZMod M) := by rw [← hz, ZMod.natCast_zmod_val]
    rw [← hσ] at hzc
    exact add_left_cancel hzc
  rw [hwone] at hw
  have hτone : zmodScaleHom 4 M 1 = 4 := by simpa using zmodScaleHom_natCast 4 M 1
  rw [hτone] at hw
  change x = 2 * y + 4
  linear_combination -hw

/-- The parity-saving cover forces the odd extra's projection to -3
once its even companion has been identified as its affine double. -/
theorem odd_extra_projection_eq_neg_three_of_valid_quadrupled_short_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hMeven : Even M) (hM : M ≤ 2 ^ m - 2)
    (g : Fin (m + 2) → ZMod (4 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom 4 M (a i.val : ZMod M))
    (hyodd : Odd (g (Fin.last (m + 1))).val)
    (hdouble : g (Fin.last m).castSucc = 2 * g (Fin.last (m + 1)) + 4) :
    ZMod.castHom (dvd_mul_left M 4) (ZMod M) (g (Fin.last (m + 1))) = -3 := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (4 * M) := ⟨by omega⟩
  let τ := zmodScaleHom 4 M
  let π := ZMod.castHom (dvd_mul_left M 4) (ZMod M)
  let y := g (Fin.last (m + 1))
  let σ : ZMod M := ((2 ^ m - m - 1 : ℕ) : ZMod M)
  let z := σ - π y - 2
  have hp := Nat.lt_two_pow_self (n := m)
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hzpar : z.val % 2 = m % 2 := by
    have heq : ((z.val + y.val + 2 : ℕ) : ZMod M) = ((2 ^ m - m - 1 : ℕ) : ZMod M) := by
      rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val]
      have hycast : (y.val : ZMod M) = π y := by
        simpa only [map_natCast] using congrArg π (ZMod.natCast_zmod_val y)
      rw [hycast]
      dsimp [z, σ]
      abel
    have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp heq
    have hmodtwo := hmod.of_dvd hMeven.two_dvd
    change (z.val + y.val + 2) % 2 = (2 ^ m - m - 1) % 2 at hmodtwo
    have hypar : y.val % 2 = 1 := by obtain ⟨r, hr⟩ := hyodd; dsimp [y]; omega
    omega
  have hz : z.val = 2 ^ m - m := by
    by_contra hne
    have hcover := exists_fixed_multiset_sum_of_parity_except_hole (by omega) hM z hne hzpar
    let f : Fin m ↪ Fin (m + 2) := ⟨fun i ↦ i.castSucc.castSucc,
      (Fin.castSucc_injective (m + 1)).comp (Fin.castSucc_injective m)⟩
    apply not_validTuple_of_mapped_fixed_block_two_extra_rival τ g f hprefix
      (Fin.last m).castSucc (Fin.last (m + 1)) (Fin.castSucc_ne_last _)
      (by intro i hi; exact Fin.castSucc_ne_last i (Fin.castSucc_injective (m + 1) hi))
      (by omega : 3 ≠ 1) (by omega : m - 2 + 3 + 1 = m + 2) z hcover ?_ hg
    have hτtwo : zmodScaleHom 4 M 2 = 8 := by simpa using zmodScaleHom_natCast 4 M 2
    dsimp only [τ, z, π]
    rw [map_sub, map_sub, zmodScaleHom_castHom, hτtwo, sum_divisor_fixed_short_prefix g hprefix,
      hdouble]
    dsimp [σ, y]
    simp only [nsmul_eq_mul]
    ring
  have hσ : σ + 1 = ((2 ^ m - m : ℕ) : ZMod M) := by
    have hn : 2 ^ m - m - 1 + 1 = 2 ^ m - m := by omega
    simpa only [Nat.cast_add, Nat.cast_one, σ] using congrArg (fun k : ℕ ↦ (k : ZMod M)) hn
  have hzc : z = ((2 ^ m - m : ℕ) : ZMod M) := by rw [← hz, ZMod.natCast_zmod_val]
  rw [← hσ] at hzc
  change π y = -3
  dsimp [z] at hzc
  linear_combination -hzc

/-- The two forced relations close the whole quadrupled tuple under
one affine doubling map, including the prefix's power-gap wrap. -/
theorem quadrupled_fixed_short_prefix_closed_of_extra_relations
    {m t M : ℕ} [NeZero M] (hm : 3 ≤ m) (htm : t < m)
    (hM : M = 2 ^ m - 2 ^ t) (g : Fin (m + 2) → ZMod (4 * M))
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((4 * a i.val : ℕ) : ZMod (4 * M)))
    (hdouble : g (Fin.last m).castSucc = 2 * g (Fin.last (m + 1)) + 4)
    (hproj : ZMod.castHom (dvd_mul_left M 4) (ZMod M) (g (Fin.last (m + 1))) = -3) :
    ∀ i, ∃ j, g j = 2 • g i + 4 := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (4 * M) := ⟨by omega⟩
  have hfour : 4 • g (Fin.last (m + 1)) = -12 := by
    rw [← zmodScaleHom_castHom, hproj, map_neg]
    have h3 : zmodScaleHom 4 M 3 = 12 := by simpa using zmodScaleHom_natCast 4 M 3
    rw [h3]
  have hxzero : 2 • g (Fin.last m).castSucc + 4 = 0 := by
    rw [hdouble]
    simp only [nsmul_eq_mul] at hfour ⊢
    linear_combination hfour
  intro i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · exact ⟨(Fin.last m).castSucc, by simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hdouble⟩
  · refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · refine ⟨(⟨0, by omega⟩ : Fin m).castSucc.castSucc, ?_⟩
      rw [hprefix, hxzero]
      norm_num [a]
    · by_cases hk : k.val + 1 < m
      · let j : Fin m := ⟨k.val + 1, hk⟩
        refine ⟨j.castSucc.castSucc, ?_⟩
        rw [hprefix, hprefix]
        have hn : 4 * a (k.val + 1) = 2 * (4 * a k.val) + 4 := by
          have hp : 0 < 2 ^ k.val := by positivity
          simp only [a, pow_succ']
          omega
        simpa only [j, Fin.val_mk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul] using
          congrArg (fun z : ℕ ↦ (z : ZMod (4 * M))) hn
      · let j : Fin m := ⟨t, htm⟩
        refine ⟨j.castSucc.castSucc, ?_⟩
        rw [hprefix, hprefix]
        have hkv : k.val = m - 1 := by omega
        have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
          rw [← pow_succ']; congr 1; omega
        have hp : 0 < 2 ^ (m - 1) := by positivity
        have hpt : 0 < 2 ^ t := by positivity
        have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) htm.le
        have hn : 2 * (4 * a k.val) + 4 = 4 * a t + 4 * M := by
          simp only [a, hkv]
          omega
        have hc := congrArg (fun z : ℕ ↦ (z : ZMod (4 * M))) hn
        rw [Nat.cast_add (4 * a t), ZMod.natCast_self, add_zero] at hc
        simpa only [j, Fin.val_mk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul] using hc.symm

/-- Mixed even/odd index-four extras force affine doubling closure and
therefore the full global bound. All relations are derived from validity. -/
theorem global_lower_bound_of_valid_quadrupled_mixed_short_prefix
    {m t M : ℕ} [NeZero M] (hm : 3 ≤ m) (hMeven : Even M)
    (hMsmall : M ≤ 2 ^ m - 2) (htm : t < m) (hM : M = 2 ^ m - 2 ^ t)
    (g : Fin (m + 2) → ZMod (4 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((4 * a i.val : ℕ) : ZMod (4 * M)))
    (hx : ZMod.castHom (dvd_mul_right 4 M) (ZMod 4) (g (Fin.last m).castSucc) = 2)
    (hy : ZMod.castHom (dvd_mul_right 4 M) (ZMod 4) (g (Fin.last (m + 1))) = 1 ∨
      ZMod.castHom (dvd_mul_right 4 M) (ZMod 4) (g (Fin.last (m + 1))) = 3) :
    globalBound (m + 2) ≤ 4 * M := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (4 * M) := ⟨by omega⟩
  have hpre : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom 4 M (a i.val : ZMod M) := by
    simpa only [zmodScaleHom_natCast] using hprefix
  have hdouble := even_extra_eq_double_of_valid_quadrupled_short_prefix hm hMsmall g hg hpre hx hy
  have hyodd : Odd (g (Fin.last (m + 1))).val := by
    have hval := castHom_index_val (d := 4) (g (Fin.last (m + 1)))
    have hres : (g (Fin.last (m + 1))).val % 4 = 1 ∨
        (g (Fin.last (m + 1))).val % 4 = 3 := by
      rcases hy with hy | hy
      · rw [hy] at hval
        left
        rw [show (1 : ZMod 4).val = 1 by decide] at hval
        exact hval.symm
      · rw [hy] at hval
        right
        rw [show (3 : ZMod 4).val = 3 by decide] at hval
        exact hval.symm
    refine ⟨(g (Fin.last (m + 1))).val / 2, ?_⟩
    omega
  have hproj := odd_extra_projection_eq_neg_three_of_valid_quadrupled_short_prefix
    hm hMeven hMsmall g hg hpre hyodd hdouble
  exact global_lower_bound_of_valid_affine_doubling_closed (by omega) g hg 4
    (quadrupled_fixed_short_prefix_closed_of_extra_relations hm htm hM g hprefix hdouble hproj)

/-- A quadrupled coherent shorter prefix satisfies the global bound in
every dimension. The only mixed-coset case forces full affine closure. -/
theorem global_lower_bound_of_valid_quadrupled_fixed_short_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (4 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((4 * a i.val : ℕ) : ZMod (4 * M))) :
    globalBound (m + 2) ≤ 4 * M := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (4 * M) := ⟨by omega⟩
  by_contra hc
  have hcrit : 4 * M < globalBound (m + 2) := by omega
  have hpre : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom 4 M (a i.val : ZMod M) := by
    simpa only [zmodScaleHom_natCast] using hprefix
  have hhalf := half_modulus_le_completion_bound_of_short_critical hm
    (by omega : 2 * (2 * M) < globalBound (m + 2))
  have hMsmall : M ≤ 2 ^ m - 2 := by rw [pow_succ'] at hhalf; omega
  have hv := valid_fixed_of_valid_divisor_fixed_short_prefix g hg hprefix
  have hcard := Fintype.card_le_of_injective _ (validTuple_injective _ (validTuple_fixed_of_valid hv))
  simp only [Fintype.card_fin, ZMod.card] at hcard
  obtain ⟨t, htm, hMgap⟩ := exists_power_gap_of_valid_fixed_lt_two_pow hm (by omega) (by omega) hv
  have ht : 1 ≤ t := by
    by_contra ht
    have ht0 : t = 0 := by omega
    rw [ht0] at hMgap
    norm_num at hMgap
    omega
  have hMeven : Even M := by
    apply even_iff_two_dvd.mpr
    rw [hMgap]
    exact Nat.dvd_sub (dvd_pow_self 2 (by omega : m ≠ 0)) (dvd_pow_self 2 (by omega : t ≠ 0))
  have hMcover : M ≤ 3 * (2 ^ (m - 1) - 1) - (m - 2) := by
    have hp := Nat.lt_two_pow_self (n := m - 1)
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  let π := ZMod.castHom (dvd_mul_right 4 M) (ZMod 4)
  rcases zmod_four_extra_cases (π (g (Fin.last m).castSucc)) (π (g (Fin.last (m + 1)))) with
    hx | hy | hdiff | hsum | hmixed | hmixed
  · exact not_validTuple_of_divisor_short_prefix_zero_extra_of_three_le hm (by omega)
      hcrit g hpre (Fin.last m).castSucc (by simp) hx hg
  · exact not_validTuple_of_divisor_short_prefix_zero_extra_of_three_le hm (by omega)
      hcrit g hpre (Fin.last (m + 1)) (by simp) hy hg
  · exact not_validTuple_of_scaled_short_prefix_extra_difference_zero hm hMcover g hpre
      (by
        change π (g (Fin.last m).castSucc - g (Fin.last (m + 1))) = 0
        rw [map_sub, hdiff, sub_self]) hg
  · exact not_validTuple_of_scaled_short_prefix_extra_sum_zero hm
      (by omega) g hpre (by simpa only [map_add] using hsum) hg
  · exact hc (global_lower_bound_of_valid_quadrupled_mixed_short_prefix hm hMeven hMsmall
      htm hMgap g hg hprefix hmixed.1 hmixed.2)
  · let x : Fin (m + 2) := (Fin.last m).castSucc
    let y : Fin (m + 2) := Fin.last (m + 1)
    let p := Equiv.swap x y
    have hfix (i : Fin m) : p i.castSucc.castSucc = i.castSucc.castSucc := by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro heq
        exact Fin.castSucc_ne_last i (Fin.castSucc_injective (m + 1) heq)
      · exact Fin.castSucc_ne_last i.castSucc
    have hppre : ∀ i : Fin m, g (p i.castSucc.castSucc) = ((4 * a i.val : ℕ) : ZMod (4 * M)) := by
      intro i
      rw [hfix, hprefix]
    apply hc
    apply global_lower_bound_of_valid_quadrupled_mixed_short_prefix hm hMeven hMsmall
      htm hMgap (fun i ↦ g (p i)) (validTuple_embedding p.toEmbedding g hg) hppre
    · simpa only [p, x, y, Equiv.swap_apply_left] using hmixed.1
    · simpa only [p, x, y, Equiv.swap_apply_right] using hmixed.2

/-- Every divisor-scaled coherent SI prefix with two arbitrary extras
satisfies the full global bound. No unit assumption remains. -/
theorem global_lower_bound_of_valid_divisor_fixed_short_prefix
    {m d M : ℕ} [NeZero (d * M)] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (d * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((d * a i.val : ℕ) : ZMod (d * M))) :
    globalBound (m + 2) ≤ d * M := by
  have hNpos := Nat.pos_of_ne_zero (NeZero.ne (d * M))
  have hdpos := Nat.pos_of_mul_pos_right hNpos
  have hMpos := Nat.pos_of_mul_pos_left hNpos
  letI : NeZero M := ⟨ne_of_gt hMpos⟩
  by_contra hc
  have hcrit : d * M < globalBound (m + 2) := by omega
  have hd := divisor_le_four_of_valid_divisor_fixed_short_prefix_critical hm g hg hprefix hcrit
  interval_cases d
  · apply hc
    simpa using (global_lower_bound_of_valid_fixed_short_prefix hm g hg (by simpa using hprefix))
  · exact hc (global_lower_bound_of_valid_doubled_fixed_short_prefix hm g hg hprefix)
  · exact hc (global_lower_bound_of_valid_tripled_fixed_short_prefix hm g hg hprefix)
  · exact hc (global_lower_bound_of_valid_quadrupled_fixed_short_prefix hm g hg hprefix)

/-- The full global bound for a coherent affine SI prefix of length n-2
under an arbitrary multiplier, with two unrestricted extra entries. -/
theorem global_lower_bound_of_valid_scaled_fixed_short_prefix
    {m N : ℕ} [NeZero N] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc) = c * (a i.val : ZMod N) + b) :
    globalBound (m + 2) ≤ N := by
  obtain ⟨d, hd, u, hu, hc⟩ := ZMod.eq_unit_mul_divisor c
  obtain ⟨M, hM⟩ := hd
  subst N
  obtain ⟨v, rfl⟩ := hu
  let φ : ZMod (d * M) ≃+ ZMod (d * M) :=
    (ZMod.AddAutEquivUnits (d * M)).symm (Additive.ofMul v)
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) b
  have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
  apply global_lower_bound_of_valid_divisor_fixed_short_prefix hm
    (fun i ↦ φ.symm (g (e i) - b)) hw
  intro i
  apply φ.injective
  rw [φ.apply_symm_apply, hprefix, add_sub_cancel_right, hc]
  change (v : ZMod (d * M)) * d * (a i.val : ZMod (d * M)) =
    (v : ZMod (d * M)) * ((d * a i.val : ℕ) : ZMod (d * M))
  push_cast
  ring

/-- Direct uniform G3 exclusion for every coherent shorter-prefix
multiplier, including nonunits, with both extras arbitrary. -/
theorem not_validTuple_exceptional_of_scaled_fixed_short_prefix
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod (2 * globalBound (m + 1)))
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc) =
      c * (a i.val : ZMod (2 * globalBound (m + 1))) + b) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (2 * globalBound (m + 1)) := ⟨by omega⟩
  exact (not_lt_of_ge (global_lower_bound_of_valid_scaled_fixed_short_prefix hm g hg e c b hprefix))
    (two_mul_globalBound_lt_succ_of_not_power (by omega) hnpow)

end MinModulus
