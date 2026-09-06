/-
# Global bound for coherent SI prefixes with arbitrary multipliers

A valid n-tuple containing c*(2^i-1)+b for i<n-1 satisfies globalBound n,
even when c is not a unit. The remaining entry is arbitrary. No global
G1/G2/G3 assumption or finite-instance argument is used.

Factor c as a unit times a divisor d of the ambient modulus d*M and
normalize the unit. The retained prefix reflects to the fixed set modulo
M, so M>=globalBound(n-1). In a global counterexample this forces d<=2.
The d=1 case is the existing SI-extension theorem. At d=2, fixed-set
power-gap classification forces the exact exceptional modulus.

For that index-two case, a parity refinement saves one coin in the prefix
cover. Three copies of the extra entry then give a competing full-length
multiset. If the extra entry is even, the binary bound inside the even
subgroup already contradicts validity. The cover's sole possible hole
forces affine doubling closure, excluded by the proved class theorem.

These results broaden coherent-prefix global and G3 bounds to arbitrary
multipliers. They do not combine arbitrary nonunit multipliers with
independent half-modulus shifts, nor prove the unrestricted global gates.
-/
import MinModulus.SILiftCover
import MinModulus.DoublingClosureStrata

namespace MinModulus
open Finset

/-- Remove zero coins without increasing cardinality or changing value. -/
theorem exists_positive_mersenne_coin_multiset (s : Multiset ℕ) :
    ∃ v : Multiset ℕ, v.card ≤ s.card ∧ (∀ i ∈ v, 0 < i) ∧
      (∀ i ∈ v, i ∈ s) ∧ (v.map a).sum = (s.map a).sum := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, by simp, by simp, by simp, by simp⟩
  | @cons i s ih =>
    obtain ⟨v, hv, hpos, hmem, hsum⟩ := ih
    by_cases hi : i = 0
    · subst i
      refine ⟨v, by simp only [Multiset.card_cons]; omega, hpos,
        fun j hj ↦ Multiset.mem_cons_of_mem (hmem j hj), ?_⟩
      simpa [a] using hsum
    · refine ⟨i ::ₘ v, by simp only [Multiset.card_cons]; omega, ?_, ?_, ?_⟩
      · intro j hj
        rcases Multiset.mem_cons.mp hj with rfl | hj
        · omega
        · exact hpos j hj
      · intro j hj
        rcases Multiset.mem_cons.mp hj with rfl | hj
        · simp
        · exact Multiset.mem_cons_of_mem (hmem j hj)
      · simp only [Multiset.map_cons, Multiset.sum_cons, hsum]

/-- Every nonzero Mersenne coin is odd, so coin count and value have the
same parity after zero removal. -/
theorem mersenne_coin_sum_mod_two_eq_card
    (s : Multiset ℕ) (hpos : ∀ i ∈ s, 0 < i) :
    (s.map a).sum % 2 = s.card % 2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons i s ih =>
    have hi : 0 < i := hpos i (by simp)
    have hs := ih (fun j hj ↦ hpos j (Multiset.mem_cons_of_mem hj))
    have hai : a i % 2 = 1 := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      have hp : 0 < 2 ^ j := by positivity
      unfold a
      rw [pow_succ']
      omega
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    omega

/-- A parity mismatch with the upper cardinality bound saves one coin. -/
theorem exists_mersenne_coin_multiset_of_lt_two_mul_parity
    {k : ℕ} (hk : 1 ≤ k) (x : ℕ) (hx : x < 2 * (2 ^ k - 1))
    (hne : x ≠ 2 * (2 ^ k - 1) - (k - 1)) (hpar : x % 2 ≠ k % 2) :
    ∃ s : Multiset ℕ, s.card ≤ k - 1 ∧
      (∀ i ∈ s, i ≤ k) ∧ (s.map a).sum = x := by
  obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt_two_mul hk x hx hne
  obtain ⟨v, hv, hpos, hvs, hvsum⟩ := exists_positive_mersenne_coin_multiset s
  have hmod := mersenne_coin_sum_mod_two_eq_card v hpos
  rw [hvsum, hsum] at hmod
  refine ⟨v, by omega, fun i hi ↦ hmem i (hvs i hi), hvsum.trans hsum⟩

/-- The parity class of `m` has an `(m-2)`-term prefix cover with the
same sole possible hole `2^m-m`. -/
theorem exists_fixed_multiset_sum_of_parity_except_hole
    {m M : ℕ} [NeZero M] (hm : 2 ≤ m) (hM : M ≤ 2 ^ m - 2)
    (x : ZMod M) (hne : x.val ≠ 2 ^ m - m) (hpar : x.val % 2 = m % 2) :
    ∃ s : Multiset (Fin m), s.card = m - 2 ∧
      (s.map (fun i ↦ (a i.val : ZMod M))).sum = x := by
  classical
  have hx := x.val_lt
  have hp := Nat.lt_two_pow_self (n := m - 1)
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt_two_mul_parity
    (by omega : 1 ≤ m - 1) x.val (by omega) (by omega) (by omega)
  let f : ℕ → Fin m := fun i ↦ ⟨i % m, Nat.mod_lt i (by omega)⟩
  let v := s.map f
  have hvcard : v.card ≤ m - 2 := by simp only [v, Multiset.card_map]; omega
  have hvsum : (v.map (fun i ↦ (a i.val : ZMod M))).sum = x := by
    have heq : v.map (fun i ↦ (a i.val : ZMod M)) = s.map (fun i ↦ (a i : ZMod M)) := by
      dsimp only [v]
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro i hi
      have hi' : i < m := by have := hmem i hi; omega
      simp [f, Nat.mod_eq_of_lt hi']
    rw [heq]
    have hc : (s.map (fun i ↦ (a i : ZMod M))).sum = ((s.map a).sum : ℕ) := by simp
    rw [hc, hsum, ZMod.natCast_zmod_val]
  let z : Fin m := ⟨0, by omega⟩
  refine ⟨v + Multiset.replicate (m - 2 - v.card) z, ?_, ?_⟩
  · simp only [Multiset.card_add, Multiset.card_replicate]
    omega
  · simpa [z, a] using hvsum

/-- The canonical additive embedding of the index-two cyclic subgroup. -/
def zmodDoubleHom (M : ℕ) : ZMod M →+ ZMod (2 * M) :=
  ZMod.lift M ⟨2 • Int.castAddHom (ZMod (2 * M)), by
    change 2 • ((M : ℤ) : ZMod (2 * M)) = 0
    simp only [Int.cast_natCast, nsmul_eq_mul, Nat.cast_ofNat]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using ZMod.natCast_self (2 * M)⟩

/-- Doubling the natural representative computes the subgroup embedding. -/
theorem zmodDoubleHom_natCast (M k : ℕ) :
    zmodDoubleHom M (k : ZMod M) = (2 * k : ℕ) := by
  have h := ZMod.lift_coe M
    (⟨2 • Int.castAddHom (ZMod (2 * M)), by
      change 2 • ((M : ℤ) : ZMod (2 * M)) = 0
      simp only [Int.cast_natCast, nsmul_eq_mul, Nat.cast_ofNat]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using ZMod.natCast_self (2 * M)⟩) (k : ℤ)
  simpa [zmodDoubleHom, nsmul_eq_mul] using h

/-- A valid tuple contained in the even subgroup obeys the binary bound
inside that subgroup, not merely in the ambient group. -/
theorem two_pow_pred_le_half_of_validTuple_even_values
    {n M : ℕ} [NeZero M] (g : Fin n → ZMod (2 * M)) (hg : ValidTuple g)
    (heven : ∀ i, Even (g i).val) : 2 ^ (n - 1) ≤ M := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  let f : Fin n → ZMod M := fun i ↦ (((g i).val / 2 : ℕ) : ZMod M)
  have hf : ∀ i, zmodDoubleHom M (f i) = g i := by
    intro i
    change zmodDoubleHom M (((g i).val / 2 : ℕ) : ZMod M) = g i
    rw [zmodDoubleHom_natCast]
    have hdiv := (heven i).two_dvd
    rw [Nat.mul_div_cancel' hdiv, ZMod.natCast_zmod_val]
  have hv : ValidTuple f := by
    apply validTuple_of_comp (zmodDoubleHom M)
    simpa only [hf] using hg
  simpa only [ZMod.card] using two_pow_pred_le_card_of_validTuple f hv

/-- Reducing modulo the half modulus and embedding back doubles an entry. -/
theorem zmodDoubleHom_castHom {M : ℕ} [NeZero M] (x : ZMod (2 * M)) :
    zmodDoubleHom M (ZMod.castHom (dvd_mul_left M 2) (ZMod M) x) = 2 • x := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  rw [← ZMod.natCast_zmod_val x, map_natCast, zmodDoubleHom_natCast]
  simp [nsmul_eq_mul]

/-- In the sole uncovered case, the doubled prefix and extra entry form
an affine-doubling-closed tuple. -/
theorem doubled_fixed_prefix_closed_of_extra_projection_neg_one
    {m t M : ℕ} [NeZero M] (hm : 2 ≤ m) (htm : t < m)
    (hM : M = 2 ^ m - 2 ^ t) (g : Fin (m + 1) → ZMod (2 * M))
    (hprefix : ∀ i : Fin m, g i.castSucc = ((2 * a i.val : ℕ) : ZMod (2 * M)))
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last m)) = -1) :
    ∀ i, ∃ j, g j = 2 • g i + 2 := by
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  have hextra : 2 • g (Fin.last m) + 2 = 0 := by
    rw [← zmodDoubleHom_castHom, hx, map_neg]
    have h1 := zmodDoubleHom_natCast M 1
    norm_num at h1
    rw [h1]
    abel
  intro i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · refine ⟨(⟨0, by omega⟩ : Fin m).castSucc, ?_⟩
    rw [hprefix, hextra]
    norm_num [a]
  · by_cases hk : k.val + 1 < m
    · let j : Fin m := ⟨k.val + 1, hk⟩
      refine ⟨j.castSucc, ?_⟩
      rw [hprefix, hprefix]
      have hn : 2 * a (k.val + 1) = 2 * (2 * a k.val) + 2 := by
        have hp := Nat.one_le_pow k.val 2 (by norm_num)
        simp only [a, pow_succ']
        omega
      simpa only [j, Fin.val_mk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul] using
        congrArg (fun z : ℕ ↦ (z : ZMod (2 * M))) hn
    · let j : Fin m := ⟨t, htm⟩
      refine ⟨j.castSucc, ?_⟩
      rw [hprefix, hprefix]
      have hkv : k.val = m - 1 := by omega
      have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hp := Nat.one_le_pow (m - 1) 2 (by norm_num)
      have hpt := Nat.one_le_pow t 2 (by norm_num)
      have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) htm.le
      have hn : 2 * (2 * a k.val) + 2 = 2 * a t + 2 * M := by
        simp only [a, hkv]
        omega
      have hc := congrArg (fun z : ℕ ↦ (z : ZMod (2 * M))) hn
      rw [Nat.cast_add (2 * a t), ZMod.natCast_self, add_zero] at hc
      simpa only [j, Fin.val_mk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul] using hc.symm

/-- At an even half modulus below the binary range, validity forces the
arbitrary extra entry of a doubled SI prefix to project to -1. -/
theorem extra_projection_eq_neg_one_of_valid_doubled_fixed_prefix
    {m M : ℕ} [NeZero M] (hm : 2 ≤ m) (hMeven : Even M) (hMlt : M < 2 ^ m)
    (g : Fin (m + 1) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc = ((2 * a i.val : ℕ) : ZMod (2 * M))) :
    ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last m)) = -1 := by
  classical
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  have hMtwo : 2 ∣ M := hMeven.two_dvd
  have hpowm := Nat.lt_two_pow_self (n := m)
  have hp : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hMbound : M ≤ 2 ^ m - 2 := by
    obtain ⟨r, hr⟩ := hMeven
    omega
  let x := g (Fin.last m)
  have hxodd : Odd x.val := by
    rcases Nat.even_or_odd x.val with he | ho
    · have hev : ∀ i, Even (g i).val := by
        intro i
        refine Fin.lastCases he (fun j ↦ ?_) i
        rw [hprefix, Nat.even_iff, ZMod.val_natCast,
          Nat.mod_mod_of_dvd _ (dvd_mul_right 2 M)]
        omega
      have hbound := two_pow_pred_le_half_of_validTuple_even_values (M := M) g hg hev
      simp only [Nat.add_sub_cancel] at hbound
      omega
    · exact ho
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let σ : ZMod M := ∑ i : Fin m, (a i.val : ZMod M)
  let y := σ - π x
  have hσ : σ = ((2 ^ m - m - 1 : ℕ) : ZMod M) := by
    dsimp [σ]
    rw [← Nat.cast_sum, sum_fixed_eq_cover_hole]
  have hypar : y.val % 2 = m % 2 := by
    have hc : ((y.val + x.val : ℕ) : ZMod M) = ((2 ^ m - m - 1 : ℕ) : ZMod M) := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val]
      have hxcast : (x.val : ZMod M) = π x := by
        simpa only [map_natCast] using congrArg π (ZMod.natCast_zmod_val x)
      rw [hxcast, ← hσ]
      exact sub_add_cancel σ (π x)
    have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hc
    have hmodtwo := hmod.of_dvd hMtwo
    change (y.val + x.val) % 2 = (2 ^ m - m - 1) % 2 at hmodtwo
    have hxmod : x.val % 2 = 1 := by obtain ⟨r, hr⟩ := hxodd; omega
    omega
  by_cases hyhole : y.val = 2 ^ m - m
  · have hycast : y = ((2 ^ m - m : ℕ) : ZMod M) := by
      rw [← hyhole, ZMod.natCast_zmod_val]
    have hσadd : σ + 1 = ((2 ^ m - m : ℕ) : ZMod M) := by
      rw [hσ]
      have hn : 2 ^ m - m - 1 + 1 = 2 ^ m - m := by omega
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun z : ℕ ↦ (z : ZMod M)) hn
    change π x = -1
    change σ - π x = _ at hycast
    rw [← hσadd] at hycast
    linear_combination -hycast
  · obtain ⟨s, hs, hsum⟩ := exists_fixed_multiset_sum_of_parity_except_hole
      (M := M) hm hMbound y hyhole hypar
    let v := s.map Fin.castSucc + Multiset.replicate 3 (Fin.last m)
    have hvcard : v.card = m + 1 := by simp only [v, Multiset.card_add,
      Multiset.card_map, Multiset.card_replicate, hs]; omega
    have hprefix' : ∀ i : Fin m, g i.castSucc = zmodDoubleHom M (a i.val : ZMod M) := by
      intro i
      rw [hprefix, zmodDoubleHom_natCast]
    have hssum : ((s.map Fin.castSucc).map g).sum = zmodDoubleHom M y := by
      rw [← hsum, map_multiset_sum, Multiset.map_map, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro i _
      exact hprefix' i
    have hσsum : zmodDoubleHom M σ = ∑ i : Fin m, g i.castSucc := by
      simp only [σ, map_sum, ← hprefix']
    have hvsum : (v.map g).sum = ∑ i, g i := by
      simp only [v, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
        Multiset.sum_replicate, hssum]
      rw [Fin.sum_univ_castSucc]
      change zmodDoubleHom M (σ - π x) + 3 • x = _
      rw [map_sub, hσsum, zmodDoubleHom_castHom]
      simp only [show (3 : ℕ) = 2 + 1 by rfl, add_nsmul, one_nsmul]
      abel
    have hcount : v.count (Fin.last m) = 3 := by
      have hnot : Fin.last m ∉ s.map Fin.castSucc := by
        intro hmem
        obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
        have heq := congrArg Fin.val hi
        simp only [Fin.val_castSucc, Fin.val_last] at heq
        omega
      simp only [v, Multiset.count_add, Multiset.count_replicate]
      rw [Multiset.count_eq_zero.mpr hnot, zero_add]
      simp
    have ho := multiset_count_eq_one_of_validTuple g hg v hvcard hvsum (Fin.last m)
    omega

/-- A doubled SI extension at an even power-gap half modulus is forced
by validity to have full affine doubling closure. -/
theorem affine_doubling_closed_of_valid_doubled_fixed_prefix
    {m t M : ℕ} [NeZero M] (hm : 2 ≤ m) (ht : 1 ≤ t) (htm : t < m)
    (hM : M = 2 ^ m - 2 ^ t) (g : Fin (m + 1) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc = ((2 * a i.val : ℕ) : ZMod (2 * M))) :
    ∀ i, ∃ j, g j = 2 • g i + 2 := by
  have hMeven : Even M := by
    apply even_iff_two_dvd.mpr
    rw [hM]
    exact Nat.dvd_sub (by simpa only [pow_one] using pow_dvd_pow 2 (by omega : 1 ≤ m))
      (by simpa only [pow_one] using pow_dvd_pow 2 ht)
  have hMlt : M < 2 ^ m := by
    have hpos : 0 < 2 ^ t := by positivity
    have hp : 0 < 2 ^ m := by positivity
    omega
  exact doubled_fixed_prefix_closed_of_extra_projection_neg_one hm htm hM g hprefix
    (extra_projection_eq_neg_one_of_valid_doubled_fixed_prefix hm hMeven hMlt g hg hprefix)

/-- Uniform G3 exclusion for an SI prefix in the index-two subgroup,
with an arbitrary extra residue in the ambient cyclic group. -/
theorem not_validTuple_exceptional_of_doubled_fixed_prefix
    {m : ℕ} (hm : 2 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 1) ≠ m + 1)
    (g : Fin (m + 1) → ZMod (2 * globalBound m))
    (hprefix : ∀ i : Fin m,
      g i.castSucc = ((2 * a i.val : ℕ) : ZMod (2 * globalBound m))) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound m := (nmin_eq hm).1.1
  letI : NeZero (globalBound m) := ⟨by omega⟩
  have ht : 1 ≤ Nat.log 2 m := by
    apply (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr
    simpa using hm
  have hlog := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
  have htm : Nat.log 2 m < m := lt_of_lt_of_le Nat.lt_two_pow_self hlog
  have hclosed := affine_doubling_closed_of_valid_doubled_fixed_prefix
    hm ht htm (show globalBound m = 2 ^ m - 2 ^ Nat.log 2 m from rfl) g hg hprefix
  exact not_validTuple_exceptional_of_affine_doubling_closed (by omega) hnpow g 2 hclosed hg

/-- The global envelope grows by at most a factor of three. -/
theorem globalBound_succ_le_three_mul {m : ℕ} (hm : 2 ≤ m) :
    globalBound (m + 1) ≤ 3 * globalBound m := by
  by_cases hm2 : m = 2
  · subst m; norm_num [globalBound]
  have hm3 : 3 ≤ m := by omega
  have hsmall := succ_le_two_pow_pred m hm3
  have hp : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hlog := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
  have hlognext := Nat.pow_log_le_self 2 (by omega : m + 1 ≠ 0)
  have hmon : Nat.log 2 m ≤ Nat.log 2 (m + 1) :=
    Nat.le_log_of_pow_le (by norm_num) (hlog.trans (Nat.le_succ m))
  have hpowmon := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hmon
  unfold globalBound
  rw [pow_succ']
  omega

/-- If doubling a valid fixed-set modulus is still globally subcritical,
that modulus is exactly the preceding endpoint, in a non-power dimension. -/
theorem eq_globalBound_of_valid_fixed_double_lt
    {m D : ℕ} (hm : 2 ≤ m) (hD : 2 ≤ D) (hv : Valid m D)
    (hcrit : 2 * D < globalBound (m + 1)) :
    D = globalBound m ∧ 2 ^ Nat.log 2 (m + 1) ≠ m + 1 := by
  by_cases hm2 : m = 2
  · subst m
    norm_num [globalBound] at hcrit ⊢
    omega
  have hm3 : 3 ≤ m := by omega
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
  have hdelta : 0 < 2 ^ Nat.log 2 (m + 1) := by positivity
  have hupper : D < 2 ^ m := by unfold globalBound at hcrit; omega
  obtain ⟨t, ht, heq⟩ := exists_power_gap_of_valid_fixed_lt_two_pow hm3 hD hupper hv
  have hbound := (nmin_eq hm).2 ⟨hD, hv⟩
  have hlog := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
  have hp := Nat.lt_two_pow_self (n := m)
  have htlog : t ≤ Nat.log 2 m := by
    apply (pow_le_pow_iff_right₀ (by omega : 1 < (2 : ℕ))).mp
    have htle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) ht.le
    rw [heq] at hbound
    omega
  have hlognext : Nat.log 2 (m + 1) ≤ t := by
    by_contra hnot
    have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : t + 1 ≤ Nat.log 2 (m + 1))
    rw [pow_succ'] at hle
    rw [heq] at hcrit
    unfold globalBound at hcrit
    omega
  have hmon : Nat.log 2 m ≤ Nat.log 2 (m + 1) :=
    Nat.le_log_of_pow_le (by norm_num) (hlog.trans (Nat.le_succ m))
  have ht' : t = Nat.log 2 m := by omega
  refine ⟨by simpa [ht', globalBound] using heq, ?_⟩
  exact (Nat.log_eq_log_succ_iff (b := 2) (n := m) (by omega) (by omega)).mp (by omega)

/-- The canonical scaling homomorphism from modulus `M` to modulus `d*M`.
Validity reflection needs only additivity, not injectivity. -/
def zmodScaleHom (d M : ℕ) : ZMod M →+ ZMod (d * M) :=
  ZMod.lift M ⟨d • Int.castAddHom (ZMod (d * M)), by
    change d • ((M : ℤ) : ZMod (d * M)) = 0
    simp only [Int.cast_natCast, nsmul_eq_mul]
    rw [← Nat.cast_mul, ZMod.natCast_self]⟩

/-- Natural-cast computation for the cyclic scaling homomorphism. -/
theorem zmodScaleHom_natCast (d M k : ℕ) :
    zmodScaleHom d M (k : ZMod M) = (d * k : ℕ) := by
  have h := ZMod.lift_coe M
    (⟨d • Int.castAddHom (ZMod (d * M)), by
      change d • ((M : ℤ) : ZMod (d * M)) = 0
      simp only [Int.cast_natCast, nsmul_eq_mul]
      rw [← Nat.cast_mul, ZMod.natCast_self]⟩) (k : ℤ)
  simpa [zmodScaleHom, nsmul_eq_mul] using h

/-- The full global lower bound for a divisor-scaled coherent SI prefix
and an arbitrary extra entry. The only proper-subgroup obstruction is the
index-two exceptional case, already excluded by the parity cover. -/
theorem global_lower_bound_of_valid_divisor_fixed_prefix
    {m d M : ℕ} [NeZero (d * M)] (hm : 2 ≤ m)
    (g : Fin (m + 1) → ZMod (d * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc = ((d * a i.val : ℕ) : ZMod (d * M))) :
    globalBound (m + 1) ≤ d * M := by
  have hNpos : 0 < d * M := Nat.pos_of_ne_zero (NeZero.ne (d * M))
  have hdpos : 0 < d := Nat.pos_of_mul_pos_right hNpos
  have hMpos : 0 < M := Nat.pos_of_mul_pos_left hNpos
  letI : NeZero M := ⟨ne_of_gt hMpos⟩
  let e : Fin m ↪ Fin (m + 1) := ⟨Fin.castSucc, Fin.castSucc_injective m⟩
  have hsub := validTuple_embedding e g hg
  change ValidTuple (fun i : Fin m ↦ g i.castSucc) at hsub
  have hfixed : ValidTuple (fun i : Fin m ↦ (a i.val : ZMod M)) := by
    apply validTuple_of_comp (zmodScaleHom d M)
    simpa only [zmodScaleHom_natCast, ← hprefix] using hsub
  have hcard := Fintype.card_le_of_injective _ (validTuple_injective _ hfixed)
  simp only [Fintype.card_fin, ZMod.card] at hcard
  have hv := valid_fixed_of_validTuple hfixed
  have hbound := (nmin_eq hm).2 ⟨by omega, hv⟩
  change globalBound m ≤ M at hbound
  by_contra hnot
  have hcrit : d * M < globalBound (m + 1) := by omega
  have hratio := globalBound_succ_le_three_mul hm
  have hdsmall : d ≤ 2 := by nlinarith
  interval_cases d
  · apply hnot
    simpa using global_lower_bound_of_valid_fixed_prefix hm g hg
      (by simpa using hprefix)
  · obtain ⟨hM, hnpow⟩ := eq_globalBound_of_valid_fixed_double_lt hm (by omega) hv (by omega)
    subst M
    exact not_validTuple_exceptional_of_doubled_fixed_prefix hm hnpow g hprefix hg

/-- The full global bound for a coherent affine SI prefix with any
multiplier, including nonunits, and an arbitrary extra residue. -/
theorem global_lower_bound_of_valid_scaled_fixed_prefix
    {m N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 1))) (c b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc) = c * (a i.val : ZMod N) + b) :
    globalBound (m + 1) ≤ N := by
  obtain ⟨d, hd, u, hu, hc⟩ := ZMod.eq_unit_mul_divisor c
  obtain ⟨M, hM⟩ := hd
  subst N
  obtain ⟨v, rfl⟩ := hu
  let φ : ZMod (d * M) ≃+ ZMod (d * M) :=
    (ZMod.AddAutEquivUnits (d * M)).symm (Additive.ofMul v)
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) b
  have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
  apply global_lower_bound_of_valid_divisor_fixed_prefix hm
    (fun i ↦ φ.symm (g (e i) - b)) hw
  intro i
  apply φ.injective
  rw [φ.apply_symm_apply, hprefix, add_sub_cancel_right, hc]
  change (v : ZMod (d * M)) * d * (a i.val : ZMod (d * M)) =
    (v : ZMod (d * M)) * ((d * a i.val : ℕ) : ZMod (d * M))
  push_cast
  ring

/-- The exceptional modulus is strictly below the next global envelope
exactly in the non-power dimension relevant to G3. -/
theorem two_mul_globalBound_lt_succ_of_not_power
    {m : ℕ} (hm : 2 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 1) ≠ m + 1) :
    2 * globalBound m < globalBound (m + 1) := by
  have hlog : Nat.log 2 m = Nat.log 2 (m + 1) :=
    (Nat.log_eq_log_succ_iff (b := 2) (n := m) (by omega) (by omega)).mpr hnpow
  have hdelta := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
  have hpos : 0 < 2 ^ Nat.log 2 m := by positivity
  have hp := Nat.lt_two_pow_self (n := m)
  unfold globalBound
  rw [← hlog, pow_succ']
  omega

/-- Direct G3 consumer for every coherent SI multiplier, not just units. -/
theorem not_validTuple_exceptional_of_scaled_fixed_prefix
    {m : ℕ} (hm : 2 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 1) ≠ m + 1)
    (g : Fin (m + 1) → ZMod (2 * globalBound m))
    (e : Equiv.Perm (Fin (m + 1))) (c b : ZMod (2 * globalBound m))
    (hprefix : ∀ i : Fin m,
      g (e i.castSucc) = c * (a i.val : ZMod (2 * globalBound m)) + b) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound m := (nmin_eq hm).1.1
  letI : NeZero (2 * globalBound m) := ⟨by omega⟩
  exact (not_lt_of_ge (global_lower_bound_of_valid_scaled_fixed_prefix hm g hg e c b hprefix))
    (two_mul_globalBound_lt_succ_of_not_power hm hnpow)

end MinModulus
