/-
# Order-three pair descent for the G1 program

An adjacent-heavy omission triangle exposes two tuple coordinates whose
difference is nonzero 3-torsion.  This module turns that structural output
into a genuine descent: delete both coordinates and quotient by the subgroup
they generate.  A quotient rival lifts with target `0`, `t`, or `-t`; the two
nonzero targets are canceled by assigning multiplicities `(0,2)` or `(2,0)`
to the deleted pair, contradicting validity of the original tuple.
-/
import MinModulus.G1Triangle

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- Every integer multiple of a nonzero element of order three is `0`, the
element itself, or its negative. -/
theorem zsmul_eq_zero_or_self_or_neg_of_order_three {t : G}
    (htne : t ≠ 0) (ht3 : (3 : ℕ) • t = 0) (a : ℤ) :
    a • t = 0 ∨ a • t = t ∨ a • t = -t := by
  have horder : addOrderOf t = 3 := addOrderOf_eq_prime ht3 htne
  have hreduce := mod_addOrderOf_zsmul t a
  rw [horder] at hreduce
  have hnonneg : 0 ≤ a % (3 : ℤ) := Int.emod_nonneg _ (by norm_num)
  have hlt : a % (3 : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have htwo : (2 : ℤ) • t = -t := by
    rw [two_zsmul, eq_neg_iff_add_eq_zero]
    have ht3' : t + t + t = 0 := by
      calc
        t + t + t = (3 : ℕ) • t := by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul,
            two_nsmul, one_nsmul]
        _ = 0 := ht3
    simpa [add_assoc, add_comm, add_left_comm] using ht3'
  interval_cases hrem : a % (3 : ℤ)
  · left
    rw [← hreduce, zero_zsmul]
  · right; left
    rw [← hreduce, one_zsmul]
  · right; right
    rw [← hreduce, htwo]

/-- **Order-three pair descent.**  If two entries of a valid `(n+2)`-tuple
differ by a nonzero element `t` of order three, deleting both entries and
passing to `G ⧸ ⟨t⟩` leaves a valid `n`-tuple. -/
theorem pair_descent_order_three
    (g : Fin (n + 2) → G) (hg : ValidTuple g) {t : G}
    (htne : t ≠ 0) (ht3 : (3 : ℕ) • t = 0)
    {p r : Fin (n + 2)} (hpr : g p - g r = t) :
    ∃ g' : Fin n → G ⧸ AddSubgroup.zmultiples t, ValidTuple g' := by
  have hprIdx : p ≠ r := by
    intro hidx
    subst r
    rw [sub_self] at hpr
    exact htne hpr.symm
  obtain ⟨r', hr'⟩ := Fin.exists_succAbove_eq (Ne.symm hprIdx)
  let emb : Fin n → Fin (n + 2) := fun i => p.succAbove (r'.succAbove i)
  let qmap : G →+ G ⧸ AddSubgroup.zmultiples t :=
    QuotientAddGroup.mk' (AddSubgroup.zmultiples t)
  refine ⟨fun i => qmap (g (emb i)), ?_⟩
  intro k hksum hkval
  let K₁ : Fin (n + 1) → ℕ := r'.insertNth 1 k
  let K : Fin (n + 2) → ℕ := p.insertNth 1 K₁
  have hKp : K p = 1 := by simp [K]
  have hKr : K r = 1 := by rw [← hr']; simp [K, K₁]
  have hKemb : ∀ i, K (emb i) = k i := by
    intro i
    simp [K, K₁, emb]
  have hKsum : (∑ i, K i) = n + 2 := by
    rw [Fin.sum_univ_succAbove K p, hKp]
    have hout : ∀ i, K (p.succAbove i) = K₁ i := by
      intro i
      simp [K]
    rw [Finset.sum_congr rfl fun i _ => hout i,
      Fin.sum_univ_succAbove K₁ r']
    simp only [K₁, Fin.insertNth_apply_same]
    have hin : ∀ i, K₁ (r'.succAbove i) = k i := by
      intro i
      simp [K₁]
    rw [Finset.sum_congr rfl fun i _ => hin i, hksum]
    omega
  let rest : G := ∑ i, k i • g (emb i)
  let base : G := ∑ i, g (emb i)
  have hKweighted : (∑ i, K i • g i) = g p + g r + rest := by
    rw [Fin.sum_univ_succAbove (fun i => K i • g i) p, hKp, one_nsmul]
    have hout : ∀ i, K (p.succAbove i) • g (p.succAbove i) =
        K₁ i • g (p.succAbove i) := by
      intro i
      simp [K]
    rw [Finset.sum_congr rfl fun i _ => hout i,
      Fin.sum_univ_succAbove (fun i => K₁ i • g (p.succAbove i)) r']
    simp only [K₁, Fin.insertNth_apply_same, one_nsmul, hr']
    have hin : ∀ i, K₁ (r'.succAbove i) • g (p.succAbove (r'.succAbove i)) =
        k i • g (emb i) := by
      intro i
      simp [K₁, emb]
    rw [Finset.sum_congr rfl fun i _ => hin i]
    simp only [rest]
    abel
  have hbaseWeighted : (∑ i, g i) = g p + g r + base := by
    rw [Fin.sum_univ_succAbove g p,
      Fin.sum_univ_succAbove (fun i => g (p.succAbove i)) r', hr']
    simp only [base, emb]
    abel
  have hmap : qmap (∑ i, K i • g i) = qmap (∑ i, g i) := by
    rw [hKweighted, hbaseWeighted]
    simp only [map_add, rest, base, map_sum, map_nsmul]
    rw [hkval]
  have hker : (∑ i, K i • g i) - ∑ i, g i ∈ qmap.ker := by
    rw [AddMonoidHom.mem_ker, map_sub, hmap, sub_self]
  rw [QuotientAddGroup.ker_mk'] at hker
  obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.mp hker
  rcases zsmul_eq_zero_or_self_or_neg_of_order_three htne ht3 a with
      hzero | ht | hneg
  · have hdiff : (∑ i, K i • g i) - ∑ i, g i = 0 := by rw [← ha, hzero]
    have hones := hg K hKsum (sub_eq_zero.mp hdiff)
    intro i
    have hi := hones (emb i)
    rw [hKemb i] at hi
    exact hi
  · have hdiff : (∑ i, K i • g i) - ∑ i, g i = t := by rw [← ha, ht]
    let K₂ : Fin (n + 1) → ℕ := r'.insertNth 2 k
    let K' : Fin (n + 2) → ℕ := p.insertNth 0 K₂
    have hK'p : K' p = 0 := by simp [K']
    have hK'sum : (∑ i, K' i) = n + 2 := by
      rw [Fin.sum_univ_succAbove K' p, hK'p]
      have hout : ∀ i, K' (p.succAbove i) = K₂ i := by
        intro i
        simp [K']
      rw [Finset.sum_congr rfl fun i _ => hout i,
        Fin.sum_univ_succAbove K₂ r']
      simp only [K₂, Fin.insertNth_apply_same]
      have hin : ∀ i, K₂ (r'.succAbove i) = k i := by
        intro i
        simp [K₂]
      rw [Finset.sum_congr rfl fun i _ => hin i, hksum]
      omega
    have hK'weighted : (∑ i, K' i • g i) = (2 : ℕ) • g r + rest := by
      rw [Fin.sum_univ_succAbove (fun i => K' i • g i) p, hK'p, zero_nsmul,
        zero_add]
      have hout : ∀ i, K' (p.succAbove i) • g (p.succAbove i) =
          K₂ i • g (p.succAbove i) := by
        intro i
        simp [K']
      rw [Finset.sum_congr rfl fun i _ => hout i,
        Fin.sum_univ_succAbove (fun i => K₂ i • g (p.succAbove i)) r']
      simp only [K₂, Fin.insertNth_apply_same, hr']
      have hin : ∀ i, K₂ (r'.succAbove i) • g (p.succAbove (r'.succAbove i)) =
          k i • g (emb i) := by
        intro i
        simp [K₂, emb]
      rw [Finset.sum_congr rfl fun i _ => hin i]
    have hKeq : (∑ i, K i • g i) = (∑ i, g i) + t := by
      calc
        (∑ i, K i • g i) = ((∑ i, K i • g i) - ∑ i, g i) + ∑ i, g i := by abel
        _ = t + ∑ i, g i := by rw [hdiff]
        _ = (∑ i, g i) + t := by abel
    have hK'eq : (∑ i, K' i • g i) = ∑ i, g i := by
      rw [hK'weighted]
      calc
        (2 : ℕ) • g r + rest = (g p + g r + rest) - (g p - g r) := by
          simp only [two_nsmul]
          abel
        _ = (∑ i, K i • g i) - t := by rw [← hKweighted, hpr]
        _ = ∑ i, g i := by rw [hKeq]; abel
    have hones := hg K' hK'sum hK'eq
    have hpone := hones p
    rw [hK'p] at hpone
    omega
  · have hdiff : (∑ i, K i • g i) - ∑ i, g i = -t := by rw [← ha, hneg]
    let K₂ : Fin (n + 1) → ℕ := r'.insertNth 0 k
    let K' : Fin (n + 2) → ℕ := p.insertNth 2 K₂
    have hK'r : K' r = 0 := by rw [← hr']; simp [K', K₂]
    have hK'sum : (∑ i, K' i) = n + 2 := by
      rw [Fin.sum_univ_succAbove K' p]
      have hK'p : K' p = 2 := by simp [K']
      rw [hK'p]
      have hout : ∀ i, K' (p.succAbove i) = K₂ i := by
        intro i
        simp [K']
      rw [Finset.sum_congr rfl fun i _ => hout i,
        Fin.sum_univ_succAbove K₂ r']
      simp only [K₂, Fin.insertNth_apply_same]
      have hin : ∀ i, K₂ (r'.succAbove i) = k i := by
        intro i
        simp [K₂]
      rw [Finset.sum_congr rfl fun i _ => hin i, hksum]
      omega
    have hK'weighted : (∑ i, K' i • g i) = (2 : ℕ) • g p + rest := by
      rw [Fin.sum_univ_succAbove (fun i => K' i • g i) p]
      have hK'p : K' p = 2 := by simp [K']
      rw [hK'p]
      have hout : ∀ i, K' (p.succAbove i) • g (p.succAbove i) =
          K₂ i • g (p.succAbove i) := by
        intro i
        simp [K']
      rw [Finset.sum_congr rfl fun i _ => hout i,
        Fin.sum_univ_succAbove (fun i => K₂ i • g (p.succAbove i)) r']
      simp only [K₂, Fin.insertNth_apply_same, zero_nsmul, zero_add]
      have hin : ∀ i, K₂ (r'.succAbove i) • g (p.succAbove (r'.succAbove i)) =
          k i • g (emb i) := by
        intro i
        simp [K₂, emb]
      rw [Finset.sum_congr rfl fun i _ => hin i]
    have hKeq : (∑ i, K i • g i) = (∑ i, g i) - t := by
      calc
        (∑ i, K i • g i) = ((∑ i, K i • g i) - ∑ i, g i) + ∑ i, g i := by abel
        _ = -t + ∑ i, g i := by rw [hdiff]
        _ = (∑ i, g i) - t := by abel
    have hK'eq : (∑ i, K' i • g i) = ∑ i, g i := by
      rw [hK'weighted]
      calc
        (2 : ℕ) • g p + rest = (g p + g r + rest) + (g p - g r) := by
          simp only [two_nsmul]
          abel
        _ = (∑ i, K i • g i) + t := by rw [← hKweighted, hpr]
        _ = ∑ i, g i := by rw [hKeq]; abel
    have hones := hg K' hK'sum hK'eq
    have hrone := hones r
    rw [hK'r] at hrone
    omega

/-- The nonzero 3-torsion difference exposed by two adjacent heavy omission
edges feeds directly into order-three pair descent: delete the two nonshared
triangle coordinates and quotient by their difference. -/
theorem exists_validTuple_quotient_of_two_adjacent_heavy_opposites
    (g : Fin (n + 2) → G) (hg : ValidTuple g) {h : G}
    {cPQ cQR : Fin (n + 2) → ℤ} (hcPQ : Witness g h cPQ)
    (hcQR : Witness g h cQR) (p q r : Fin (n + 2))
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hPQ : ∀ i, cPQ i = -1 ↔ i = p ∨ i = q)
    (hQR : ∀ i, cQR i = -1 ↔ i = q ∨ i = r)
    (hPQr : cPQ r = 2) (hQRp : cQR p = 2) :
    ∃ g' : Fin n → G ⧸ AddSubgroup.zmultiples (g p - g r), ValidTuple g' := by
  obtain ⟨htne, ht3⟩ :=
    nonzero_three_torsion_of_two_adjacent_heavy_opposites g hg hcPQ hcQR
      p q r hpq hqr hrp hPQ hQR hPQr hQRp
  have ht3n : (3 : ℕ) • (g p - g r) = 0 := by
    rw [← natCast_zsmul]
    exact ht3
  exact pair_descent_order_three g hg htne ht3n rfl

/-- Quotienting by a nonzero element of order three divides the group
cardinality by three. -/
theorem nat_card_quotient_three_smul {t : G} (htne : t ≠ 0)
    (ht3 : (3 : ℕ) • t = 0) :
    Nat.card (G ⧸ AddSubgroup.zmultiples t) * 3 = Nat.card G := by
  have horder : addOrderOf t = 3 := addOrderOf_eq_prime ht3 htne
  have hcardH : Nat.card (AddSubgroup.zmultiples t) = 3 := by
    rw [Nat.card_zmultiples, horder]
  rw [← hcardH]
  exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm

/-- A nonzero element killed by `3` in `ZMod N` is one of the two nonzero
thirds of the modulus. -/
theorem zmod_eq_third_or_two_thirds_of_order_three
    {N : ℕ} [NeZero N] (t : ZMod N) (htne : t ≠ 0)
    (ht3 : (3 : ℕ) • t = 0) :
    t = (N / 3 : ℕ) ∨ t = (2 * (N / 3) : ℕ) := by
  have hdiv : 3 ∣ N := by
    by_contra hnot
    have hinj := zmod_three_zsmul_injective hnot
    apply htne
    apply hinj
    change ((3 : ℕ) : ℤ) • t = ((3 : ℕ) : ℤ) • (0 : ZMod N)
    rw [natCast_zsmul, natCast_zsmul, ht3, nsmul_zero]
  let M := N / 3
  have hN : N = 3 * M := by
    rw [show 3 * M = N by exact Nat.mul_div_cancel' hdiv]
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hMpos : 0 < M := by omega
  have htvalne : t.val ≠ 0 := by
    intro hval
    apply htne
    calc
      t = (t.val : ZMod N) := t.natCast_zmod_val.symm
      _ = 0 := by rw [hval, Nat.cast_zero]
  have hzval : ((3 * t.val : ℕ) : ZMod N) = 0 := by
    calc
      ((3 * t.val : ℕ) : ZMod N) = (3 : ℕ) • (t.val : ZMod N) := by
        rw [Nat.cast_mul, nsmul_eq_mul]
      _ = (3 : ℕ) • t := by rw [t.natCast_zmod_val]
      _ = 0 := ht3
  have hdvdval : N ∣ 3 * t.val := by
    rw [ZMod.natCast_eq_zero_iff] at hzval
    exact hzval
  obtain ⟨k, hk⟩ := hdvdval
  have hval : t.val = M * k := by
    have hk' : 3 * t.val = 3 * M * k := by
      calc
        3 * t.val = N * k := hk
        _ = (3 * M) * k := by rw [hN]
    exact Nat.mul_left_cancel (by norm_num : 0 < 3)
      (hk'.trans (Nat.mul_assoc 3 M k))
  have hkpos : 0 < k := by
    by_contra hk0
    have : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [this, Nat.mul_zero] at hval
    exact htvalne hval
  have hklt : k < 3 := by
    have htlt' : M * k < 3 * M := by
      calc
        M * k = t.val := hval.symm
        _ < N := t.val_lt
        _ = 3 * M := hN
    exact (Nat.mul_lt_mul_left hMpos).mp (by simpa [Nat.mul_comm] using htlt')
  have hkcases : k = 1 ∨ k = 2 := by omega
  rcases hkcases with rfl | rfl
  · left
    calc
      t = (t.val : ZMod N) := t.natCast_zmod_val.symm
      _ = (M : ZMod N) := by rw [hval, Nat.mul_one]
  · right
    change t = (2 * M : ℕ)
    calc
      t = (t.val : ZMod N) := t.natCast_zmod_val.symm
      _ = (2 * M : ℕ) := by rw [hval, Nat.mul_comm]

/-- Therefore every nonzero order-three element of `ZMod N` generates the
canonical subgroup generated by `N/3`. -/
theorem zmultiples_order_three_eq_third
    {N : ℕ} [NeZero N] (t : ZMod N) (htne : t ≠ 0)
    (ht3 : (3 : ℕ) • t = 0) :
    AddSubgroup.zmultiples t = AddSubgroup.zmultiples ((N / 3 : ℕ) : ZMod N) := by
  rcases zmod_eq_third_or_two_thirds_of_order_three t htne ht3 with ht | ht
  · rw [ht]
  · let M := N / 3
    have hdiv : 3 ∣ N := by
      by_contra hnot
      have hinj := zmod_three_zsmul_injective hnot
      exact htne (hinj (by
        change ((3 : ℕ) : ℤ) • t = ((3 : ℕ) : ℤ) • (0 : ZMod N)
        rw [natCast_zsmul, natCast_zsmul, ht3, nsmul_zero]))
    have hN : N = 3 * M := by
      rw [show 3 * M = N by exact Nat.mul_div_cancel' hdiv]
    apply le_antisymm
    · rw [AddSubgroup.zmultiples_le]
      rw [ht, AddSubgroup.mem_zmultiples_iff]
      refine ⟨2, ?_⟩
      simp only [two_zsmul]
      push_cast
      ring
    · rw [AddSubgroup.zmultiples_le, AddSubgroup.mem_zmultiples_iff]
      refine ⟨2, ?_⟩
      rw [ht]
      change (2 : ℤ) • ((2 * M : ℕ) : ZMod N) = (M : ZMod N)
      simp only [two_zsmul]
      calc
        ((2 * M : ℕ) : ZMod N) + ((2 * M : ℕ) : ZMod N) = (4 * M : ℕ) := by
          push_cast
          ring
        _ = (N + M : ℕ) := by congr 1; omega
        _ = (M : ZMod N) := by push_cast; simp

/-- The quotient by any nonzero order-three element of `ZMod N` is
canonically additively equivalent to `ZMod (N/3)`. -/
noncomputable def quotOrderThreeEquivZMod
    {N : ℕ} [NeZero N] (t : ZMod N) (htne : t ≠ 0)
    (ht3 : (3 : ℕ) • t = 0) :
    (ZMod N ⧸ AddSubgroup.zmultiples t) ≃+ ZMod (N / 3) := by
  have hdiv : 3 ∣ N := by
    by_contra hnot
    have hinj := zmod_three_zsmul_injective hnot
    exact htne (hinj (by
      change ((3 : ℕ) : ℤ) • t = ((3 : ℕ) : ℤ) • (0 : ZMod N)
      rw [natCast_zsmul, natCast_zsmul, ht3, nsmul_zero]))
  have hMpos : 0 < N / 3 := Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hdiv) (by norm_num)
  letI : NeZero (N / 3) := ⟨Nat.ne_of_gt hMpos⟩
  have hMdvd : N / 3 ∣ N := by
    refine ⟨3, ?_⟩
    rw [Nat.mul_comm, Nat.mul_div_cancel' hdiv]
  exact (QuotientAddGroup.quotientAddEquivOfEq
    (zmultiples_order_three_eq_third t htne ht3)).trans
      (quotZMultiplesEquivZMod hMdvd)

/-- Cyclic operational form of the adjacent-heavy descent: a valid
`(n+2)`-tuple modulo `N` with two adjacent heavy omission edges yields a valid
`n`-tuple modulo `N/3`. -/
theorem exists_validTuple_third_of_two_adjacent_heavy_opposites
    {N : ℕ} [NeZero N] (g : Fin (n + 2) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {cPQ cQR : Fin (n + 2) → ℤ}
    (hcPQ : Witness g h cPQ) (hcQR : Witness g h cQR)
    (p q r : Fin (n + 2)) (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hPQ : ∀ i, cPQ i = -1 ↔ i = p ∨ i = q)
    (hQR : ∀ i, cQR i = -1 ↔ i = q ∨ i = r)
    (hPQr : cPQ r = 2) (hQRp : cQR p = 2) :
    ∃ g' : Fin n → ZMod (N / 3), ValidTuple g' := by
  obtain ⟨htne, ht3z⟩ :=
    nonzero_three_torsion_of_two_adjacent_heavy_opposites g hg hcPQ hcQR
      p q r hpq hqr hrp hPQ hQR hPQr hQRp
  have ht3 : (3 : ℕ) • (g p - g r) = 0 := by
    rw [← natCast_zsmul]
    exact ht3z
  obtain ⟨gq, hgq⟩ :=
    exists_validTuple_quotient_of_two_adjacent_heavy_opposites g hg hcPQ hcQR
      p q r hpq hqr hrp hPQ hQR hPQr hQRp
  let e := quotOrderThreeEquivZMod (g p - g r) htne ht3
  exact ⟨fun i => e (gq i), validTuple_comp hgq e.toAddMonoidHom e.injective⟩

end MinModulus
