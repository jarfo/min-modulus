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

end MinModulus
