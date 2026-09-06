/-
# Uniform exceptional-modulus cover for independent SI lifts

Let m be the retained dimension, t=floor(log₂ m), and M=2^m-2^t.
If m+1 is not a power of two, every independent lift of the m fixed SI
entries from ZMod M to ZMod (2*M) has a full (m+1)-fold sumset. Thus no
extra residue can extend this prefix to a valid tuple at the exceptional
modulus. Reindexing, translation and unit scaling are also allowed.

The quotient's (m-1)-term sumset has at most one hole, 2^m-m. Two copies
of entries m-1 and t-1 form an antipodal pair regardless of lift bits,
covering both sheets except possibly the target R=2^(t+1)-m-2. For that
target choose j=ceil(log₂(m-2^t+2)). Repeating entries m-j and t-j exactly
2^j times gives another lift-independent antipodal pair, with enough
remaining terms for ones and zero padding. The non-power boundary is
exactly what makes this repair fit in m+1 terms.

No finite enumeration or unrestricted G1/G2/G3 assumption is used. This
closes all independent SI lifts, not arbitrary non-SI endpoint prefixes
or the claim that an arbitrary exceptional tuple contains such a prefix.
-/
import MinModulus.SIExtensionStrata

namespace MinModulus
open Finset

/-- With `k` coins through `2^k-1`, only the first greedy gap can be
missing below twice the largest coin. -/
theorem exists_mersenne_coin_multiset_of_lt_two_mul
    {k : ℕ} (hk : 1 ≤ k) (x : ℕ) (hx : x < 2 * (2 ^ k - 1))
    (hne : x ≠ 2 * (2 ^ k - 1) - (k - 1)) :
    ∃ s : Multiset ℕ, s.card ≤ k ∧
      (∀ i ∈ s, i ≤ k) ∧ (s.map a).sum = x := by
  by_cases hsmall : x < 2 * (2 ^ k - 1) - (k - 1)
  · simpa using exists_mersenne_coin_multiset_of_lt hk 0 x hsmall
  let c := 2 * (2 ^ k - 1) - x
  have hp := Nat.lt_two_pow_self (n := k)
  have hc : 1 ≤ c := by dsimp [c]; omega
  have hck : c ≤ k - 2 := by dsimp [c]; omega
  obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_tail_multiset hc k (by omega)
  refine ⟨k ::ₘ s, by simp [hs]; omega, ?_, ?_⟩
  · intro i hi
    rcases Multiset.mem_cons.mp hi with rfl | hi
    · rfl
    · exact (hmem i hi).trans (by omega)
  · rw [Multiset.map_cons, Multiset.sum_cons, hsum]
    simp only [a]
    dsimp [c]
    omega

/-- Equal reductions modulo `M` differ by zero or the half modulus. -/
theorem eq_or_eq_add_half_of_castHom_eq
    {M : ℕ} [NeZero M] (x y : ZMod (2 * M))
    (h : ZMod.castHom (dvd_mul_left M 2) (ZMod M) x =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) y) :
    x = y ∨ x = y + M := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  let z := x - y
  have hz : ZMod.castHom (dvd_mul_left M 2) (ZMod M) z = 0 := by
    simp only [z, map_sub, h, sub_self]
  rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at hz
  obtain ⟨q, hq⟩ := hz
  have hlt := z.val_lt
  have hqsmall : q = 0 ∨ q = 1 := by
    have hqle : q < 2 := by nlinarith
    omega
  have hzval : z.val = 0 ∨ z.val = M := by rcases hqsmall with rfl | rfl <;> simp_all
  have hzcast : z = (z.val : ZMod (2 * M)) := (ZMod.natCast_zmod_val z).symm
  rcases hzval with hzval | hzval
  · left
    have : x - y = 0 := by change z = 0; rw [hzcast, hzval]; simp
    exact sub_eq_zero.mp this
  · right
    have : x - y = (M : ZMod (2 * M)) := by change z = M; rw [hzcast, hzval]
    exact sub_eq_iff_eq_add.mp this |>.trans (add_comm _ _)

/-- Even multiplicities erase every independent half-modulus lift bit. -/
theorem nsmul_eq_of_even_of_castHom_eq
    {M c : ℕ} [NeZero M] (hc : Even c) (x y : ZMod (2 * M))
    (h : ZMod.castHom (dvd_mul_left M 2) (ZMod M) x =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) y) : c • x = c • y := by
  rcases eq_or_eq_add_half_of_castHom_eq x y h with rfl | hxy
  · rfl
  · obtain ⟨d, rfl⟩ := hc
    have hh := half_add_half (M := M) rfl
    have hkill : (d + d) • (M : ZMod (2 * M)) = 0 := by
      rw [add_nsmul, ← smul_add, hh, smul_zero]
    rw [hxy, smul_add, hkill, add_zero]

/-- The one exceptional target admits a repair using an even power-of-two
number of repeated endpoint coins, leaving enough ones for padding. -/
theorem exists_si_lift_repair_power
    {m t : ℕ} (_ht : 1 ≤ t) (hlower : 2 ^ t ≤ m)
    (hupper : m + 2 ≤ 2 ^ (t + 1)) :
    ∃ j, 1 ≤ j ∧ j ≤ t ∧ m - 2 ^ t + 2 ≤ 2 ^ j ∧
      2 * 2 ^ j ≤ m + (m - 2 ^ t) + 3 := by
  let d := m - 2 ^ t
  let j := Nat.clog 2 (d + 2)
  have hjpos : 0 < j := Nat.clog_pos (by omega) (by omega)
  have hjle : j ≤ t := Nat.clog_le_of_le_pow (by dsimp [d]; rw [pow_succ'] at hupper; omega)
  have hdle : d + 2 ≤ 2 ^ j := Nat.le_pow_clog (by omega) _
  have hjprev : 2 ^ (j - 1) < d + 2 :=
    Nat.pow_pred_clog_lt_self (b := 2) (x := d + 2) (by omega) (by omega)
  have hjpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
    rw [← pow_succ']; congr 1
  refine ⟨j, by omega, hjle, hdle, ?_⟩
  by_cases heq : j = t
  · rw [heq] at hjpow hjprev ⊢
    dsimp [d] at hjprev
    omega
  · have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : j + 1 ≤ t)
    rw [pow_succ'] at hle
    omega

/-- In the quotient, `m-1` terms from the `m` SI entries cover every
residue except possibly `2^m-m`. The actual lifts are arbitrary. -/
theorem exists_lift_multiset_sum_mod_except_hole
    {m M : ℕ} [NeZero M] (hm : 2 ≤ m) (hM : M ≤ 2 ^ m - 2)
    (u : Fin m → ZMod (2 * M))
    (hu : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (u i) = (a i.val : ZMod M))
    (x : ZMod M) (hne : x.val ≠ 2 ^ m - m) :
    ∃ s : Multiset (Fin m), s.card = m - 1 ∧
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) ((s.map u).sum) = x := by
  classical
  have hx := x.val_lt
  have hp := Nat.lt_two_pow_self (n := m - 1)
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt_two_mul
    (by omega : 1 ≤ m - 1) x.val (by omega) (by omega)
  let f : ℕ → Fin m := fun i ↦ ⟨i % m, Nat.mod_lt i (by omega)⟩
  let v := s.map f
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  have hvcard : v.card ≤ m - 1 := by simpa [v] using hs
  have hvsum : π ((v.map u).sum) = x := by
    have heq : v.map (fun i ↦ π (u i)) = s.map (fun i ↦ (a i : ZMod M)) := by
      dsimp only [v]
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro i hi
      have hi' : i < m := by have := hmem i hi; omega
      simp [π, hu, f, Nat.mod_eq_of_lt hi']
    rw [map_multiset_sum, Multiset.map_map]
    change (v.map (fun i ↦ π (u i))).sum = x
    rw [heq]
    have hc : (s.map (fun i ↦ (a i : ZMod M))).sum = ((s.map a).sum : ℕ) := by simp
    rw [hc, hsum, ZMod.natCast_zmod_val]
  let z : Fin m := ⟨0, by omega⟩
  refine ⟨v + Multiset.replicate (m - 1 - v.card) z, ?_, ?_⟩
  · simp only [Multiset.card_add, Multiset.card_replicate]
    omega
  · change π _ = x
    rw [Multiset.map_add, Multiset.sum_add, map_add, hvsum,
      Multiset.map_replicate, Multiset.sum_replicate, map_nsmul]
    simp [π, hu, z, a]

/-- A power-of-two multiplicity shifts a Mersenne coin's exponent. -/
theorem pow_mul_a_sub {k j : ℕ} (hj : j ≤ k) :
    2 ^ j * a (k - j) = 2 ^ k - 2 ^ j := by
  unfold a
  rw [Nat.mul_sub_left_distrib, ← pow_add, mul_one,
    show j + (k - j) = k by omega]

/-- Every lifted SI prefix retains a family of antipodal repeated-coin
pairs. Even multiplicities make this independent of all lift bits. -/
theorem pow_nsmul_si_lift_pair
    {m t j M : ℕ} [NeZero M] (htm : t < m) (hj : 1 ≤ j) (hjt : j ≤ t)
    (hM : M = 2 ^ m - 2 ^ t) (u : Fin m → ZMod (2 * M))
    (hu : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (u i) = (a i.val : ZMod M)) :
    2 ^ j • u ⟨m - j, by omega⟩ =
      2 ^ j • u ⟨t - j, by omega⟩ + M := by
  have hc : Even (2 ^ j) := by
    refine ⟨2 ^ (j - 1), ?_⟩
    have hp : 2 ^ j = 2 * 2 ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have heven (i : Fin m) : 2 ^ j • u i = 2 ^ j • (a i.val : ZMod (2 * M)) :=
    nsmul_eq_of_even_of_castHom_eq hc _ _ (by simpa only [map_natCast] using hu i)
  rw [heven, heven]
  simp only [nsmul_eq_mul]
  have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) htm.le
  have hjle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hjt
  have hn : 2 ^ j * a (m - j) = 2 ^ j * a (t - j) + M := by
    rw [pow_mul_a_sub (by omega), pow_mul_a_sub hjt, hM]
    omega
  simpa only [Nat.cast_add, Nat.cast_mul] using
    congrArg (fun k : ℕ ↦ (k : ZMod (2 * M))) hn

/-- A quotient representation and an antipodal repeated-coin pair lift
to an exact representation on either sheet. -/
theorem exists_multiset_sum_of_antipodal_coin_pair
    {m M c L : ℕ} [NeZero M] (u : Fin m → ZMod (2 * M))
    (lo hi : Fin m) (hpair : c • u hi = c • u lo + M)
    (s : Multiset (Fin m)) (hcard : s.card + c = L)
    (x : ZMod (2 * M))
    (hproj : ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      ((s.map u).sum + c • u lo) = ZMod.castHom (dvd_mul_left M 2) (ZMod M) x) :
    ∃ v : Multiset (Fin m), v.card = L ∧ (v.map u).sum = x := by
  rcases eq_or_eq_add_half_of_castHom_eq _ x hproj with heq | heq
  · refine ⟨s + Multiset.replicate c lo, by simpa using hcard, ?_⟩
    simpa using heq
  · refine ⟨s + Multiset.replicate c hi, by simpa using hcard, ?_⟩
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, hpair]
    rw [← add_assoc, heq, add_assoc, half_add_half (M := M) rfl, add_zero]

/-- Uniform full coverage for independently lifted SI endpoints away
from power-of-two full dimensions. No lift-bit normalization is required. -/
theorem exists_multiset_sum_of_si_lifts
    {m t M : ℕ} [NeZero M] (hm : 2 ≤ m) (ht : 1 ≤ t)
    (hlower : 2 ^ t ≤ m) (hupper : m + 2 ≤ 2 ^ (t + 1))
    (hM : M = 2 ^ m - 2 ^ t) (u : Fin m → ZMod (2 * M))
    (hu : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (u i) = (a i.val : ZMod M))
    (x : ZMod (2 * M)) :
    ∃ v : Multiset (Fin m), v.card = m + 1 ∧ (v.map u).sum = x := by
  classical
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  have hπu : ∀ i, π (u i) = (a i.val : ZMod M) := hu
  have htm : t < m := lt_of_lt_of_le Nat.lt_two_pow_self hlower
  have hMbound : M ≤ 2 ^ m - 2 := by
    have htwo : 2 ≤ 2 ^ t := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) ht
    omega
  let lo : Fin m := ⟨t - 1, by omega⟩
  let hi : Fin m := ⟨m - 1, by omega⟩
  have hpair : 2 • u hi = 2 • u lo + M := by
    simpa only [pow_one] using pow_nsmul_si_lift_pair htm (by omega : 1 ≤ 1) ht hM u hu
  let y : ZMod M := π (x - 2 • u lo)
  by_cases hy : y.val ≠ 2 ^ m - m
  · obtain ⟨s, hcard, hsum⟩ := exists_lift_multiset_sum_mod_except_hole hm hMbound u hu y hy
    apply exists_multiset_sum_of_antipodal_coin_pair u lo hi hpair s (by omega) x
    change π _ = π x
    rw [map_add, hsum]
    simp [y]
  · have hyval : y.val = 2 ^ m - m := by omega
    let R := 2 ^ (t + 1) - m - 2
    have hpowt : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ']
    have hpowm := Nat.lt_two_pow_self (n := m)
    have hloNat : 2 * a (t - 1) = 2 ^ t - 2 := by
      simpa using pow_mul_a_sub ht
    have hRnat : (2 ^ m - m) + 2 * a (t - 1) = M + R := by
      dsimp [R]
      omega
    have hxproj : π x = (R : ZMod M) := by
      have hycast : y = ((2 ^ m - m : ℕ) : ZMod M) := by
        rw [← hyval, ZMod.natCast_zmod_val]
      have heq : π x = y + 2 • (a (t - 1) : ZMod M) := by
        simp only [y, map_sub, map_nsmul, hπu, lo]
        abel
      rw [heq, hycast, nsmul_eq_mul]
      have hcast := congrArg (fun k : ℕ ↦ (k : ZMod M)) hRnat
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        ZMod.natCast_self, zero_add] using hcast
    obtain ⟨j, hj, hjt, hdle, hbudget⟩ := exists_si_lift_repair_power ht hlower hupper
    let c := 2 ^ j
    let z := c - (m - 2 ^ t) - 2
    have htotal : z + c ≤ m + 1 := by dsimp [z, c]; omega
    let slo : Fin m := ⟨t - j, by omega⟩
    let shi : Fin m := ⟨m - j, by omega⟩
    let one : Fin m := ⟨1, by omega⟩
    let zero : Fin m := ⟨0, by omega⟩
    let s := Multiset.replicate z one + Multiset.replicate (m + 1 - c - z) zero
    have hscard : s.card + c = m + 1 := by
      simp only [s, Multiset.card_add, Multiset.card_replicate]
      omega
    have hspair : c • u shi = c • u slo + M := pow_nsmul_si_lift_pair htm hj hjt hM u hu
    apply exists_multiset_sum_of_antipodal_coin_pair u slo shi hspair s hscard x
    change π _ = π x
    have hsproj : π ((s.map u).sum) = (z : ZMod M) := by
      simp only [s, Multiset.map_add, Multiset.sum_add, map_add,
        Multiset.map_replicate, Multiset.sum_replicate, map_nsmul, hπu]
      norm_num [one, zero, a]
    rw [map_add, hsproj, map_nsmul, hπu, hxproj]
    have hjle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hjt
    have hzNat : z + c * a (t - j) = R := by
      dsimp [c]
      rw [pow_mul_a_sub hjt]
      dsimp [z, c, R]
      omega
    simpa only [slo, Fin.val_mk, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul] using
      congrArg (fun k : ℕ ↦ (k : ZMod M)) hzNat

/-- A fully covering lifted prefix excludes every possible extra entry. -/
theorem not_validTuple_of_si_lift_prefix
    {m t M : ℕ} [NeZero M] (hm : 2 ≤ m) (ht : 1 ≤ t)
    (hlower : 2 ^ t ≤ m) (hupper : m + 2 ≤ 2 ^ (t + 1))
    (hM : M = 2 ^ m - 2 ^ t) (g : Fin (m + 1) → ZMod (2 * M))
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M)) : ¬ ValidTuple g := by
  classical
  intro hg
  obtain ⟨s, hcard, hsum⟩ := exists_multiset_sum_of_si_lifts hm ht hlower hupper hM
    (fun i : Fin m ↦ g i.castSucc) hprefix (∑ i, g i)
  let v := s.map Fin.castSucc
  have hvcard : v.card = m + 1 := by simpa [v] using hcard
  have hvsum : (v.map g).sum = ∑ i, g i := by
    simpa only [v, Multiset.map_map, Function.comp_def] using hsum
  have hnot : Fin.last m ∉ v := by
    intro hmem
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
    have heq := congrArg Fin.val hi
    simp only [Fin.val_castSucc, Fin.val_last] at heq
    omega
  have hz := Multiset.count_eq_zero.mpr hnot
  have ho := multiset_count_eq_one_of_validTuple g hg v hvcard hvsum (Fin.last m)
  omega

/-- Uniform exceptional G3 exclusion for every independent lift of the
downstairs SI endpoint, with the extra residue arbitrary. -/
theorem not_validTuple_exceptional_of_si_lift_prefix
    {m : ℕ} (hm : 2 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 1) ≠ m + 1)
    (g : Fin (m + 1) → ZMod (2 * globalBound m))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound m) 2) (ZMod (globalBound m))
        (g i.castSucc) = (a i.val : ZMod (globalBound m))) : ¬ ValidTuple g := by
  have hB : 2 ≤ globalBound m := (nmin_eq hm).1.1
  letI : NeZero (globalBound m) := ⟨by omega⟩
  have hlog : Nat.log 2 m = Nat.log 2 (m + 1) :=
    (Nat.log_eq_log_succ_iff (b := 2) (n := m) (by omega) (by omega)).mpr hnpow
  have hupper := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (m + 1)
  rw [← hlog] at hupper
  have ht : 1 ≤ Nat.log 2 m := by
    apply (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr
    simpa using hm
  exact not_validTuple_of_si_lift_prefix (M := globalBound m) hm ht (Nat.pow_log_le_self 2 (by omega))
    (by omega) rfl g hprefix

/-- Reindexing, translation, unit scaling, and arbitrary independent lift
bits preserve the exceptional-lift obstruction for this SI class. -/
theorem not_validTuple_exceptional_of_affine_si_lifts
    {m : ℕ} (hm : 2 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 1) ≠ m + 1)
    (g : Fin (m + 1) → ZMod (2 * globalBound m))
    (e : Equiv.Perm (Fin (m + 1)))
    (φ : ZMod (2 * globalBound m) ≃+ ZMod (2 * globalBound m))
    (b : ZMod (2 * globalBound m)) (ε : Fin m → ℕ)
    (hprefix : ∀ i : Fin m,
      g (e i.castSucc) = φ ((a i.val : ZMod (2 * globalBound m)) + ε i • globalBound m) + b) :
    ¬ ValidTuple g := by
  intro hg
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) b
  have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
  apply not_validTuple_exceptional_of_si_lift_prefix hm hnpow
    (fun i ↦ φ.symm (g (e i) - b)) _ hw
  intro i
  rw [hprefix, add_sub_cancel_right, AddEquiv.symm_apply_apply, map_add, map_nsmul, map_natCast]
  simp

/-- Every additive automorphism of a finite cyclic quotient lifts to the
ambient cyclic group, by surjectivity of reduction on units. -/
theorem exists_addEquiv_lift_castHom
    {M N : ℕ} [NeZero N] (h : M ∣ N) (φ : ZMod M ≃+ ZMod M) :
    ∃ Φ : ZMod N ≃+ ZMod N, ∀ x,
      ZMod.castHom h (ZMod M) (Φ x) = φ (ZMod.castHom h (ZMod M) x) := by
  let u := (ZMod.AddAutEquivUnits M φ).toMul
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective h u
  let Φ : ZMod N ≃+ ZMod N := (ZMod.AddAutEquivUnits N).symm (Additive.ofMul v)
  have hφ : ∀ x, (u : ZMod M) * x = φ x := by
    intro x
    have heq := congrArg (fun f : AddAut (ZMod M) ↦ f x)
      ((ZMod.AddAutEquivUnits M).symm_apply_apply φ)
    exact heq
  refine ⟨Φ, fun x ↦ ?_⟩
  change ZMod.castHom h (ZMod M) ((v : ZMod N) * x) = _
  rw [map_mul]
  have hv' := congrArg (fun w : (ZMod M)ˣ ↦ (w : ZMod M)) hv
  change ZMod.castHom h (ZMod M) (v : ZMod N) = (u : ZMod M) at hv'
  rw [hv', hφ]

/-- G3 exclusion when the actual retained quotient prefix is affine SI;
the lifts upstairs are completely unrestricted. -/
theorem not_validTuple_exceptional_of_quotient_affine_fixed_prefix
    {m : ℕ} (hm : 2 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 1) ≠ m + 1)
    (g : Fin (m + 1) → ZMod (2 * globalBound m))
    (e : Equiv.Perm (Fin (m + 1)))
    (φ : ZMod (globalBound m) ≃+ ZMod (globalBound m)) (b : ZMod (globalBound m))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound m) 2) (ZMod (globalBound m))
        (g (e i.castSucc)) = φ (a i.val) + b) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound m := (nmin_eq hm).1.1
  letI : NeZero (globalBound m) := ⟨by omega⟩
  letI : NeZero (2 * globalBound m) := ⟨by omega⟩
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_lift_castHom (dvd_mul_left (globalBound m) 2) φ
  let B : ZMod (2 * globalBound m) := b.val
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) B
  have hw := validTuple_comp hv Φ.symm.toAddMonoidHom Φ.symm.injective
  apply not_validTuple_exceptional_of_si_lift_prefix hm hnpow
    (fun i ↦ Φ.symm (g (e i) - B)) _ hw
  intro i
  apply φ.injective
  rw [← hΦ, Φ.apply_symm_apply, map_sub, hprefix]
  simp [B]

end MinModulus
