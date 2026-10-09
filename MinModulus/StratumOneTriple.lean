import MinModulus.StratumOneAssemble

/-!
# The stratum-one compatible pair

Over a support `T` of size `s` the two level assignments

* `conLevel a`  : level `s-1` at `a`, level `0` elsewhere,
* `disLevel b`  : level `0` at `b`, level `1` elsewhere,

both have total level `s - 1`, so by `coeffSum_assemble` and
`value_assemble` each assembles to a vector of coordinate sum `1` and
value `∑_{t ∈ T} 2^(t-1)`.

This file computes the two vectors pointwise and proves that their sum is
bounded by `1` coordinatewise under the three conditions produced by the
pigeonhole.
-/

namespace MinModulus

open Finset

namespace StratumOne

variable {d : ℕ}

/-- Level assignment concentrating all promotion at `a`. -/
def conLevel (T : Finset (ZMod d)) (a : ZMod d) : ZMod d → ℕ :=
  fun t => if t = a then T.card - 1 else 0

/-- Level assignment distributing one promotion to every element but `b`. -/
def disLevel (b : ZMod d) : ZMod d → ℕ := fun t => if t = b then 0 else 1

theorem sum_conLevel {T : Finset (ZMod d)} {a : ZMod d} (ha : a ∈ T) :
    ∑ t ∈ T, (conLevel T a t : ℤ) = (T.card : ℤ) - 1 := by
  classical
  have h : ∀ t ∈ T, ((conLevel T a t : ℕ) : ℤ)
      = if t = a then ((T.card - 1 : ℕ) : ℤ) else 0 := by
    intro t _; unfold conLevel; split <;> simp
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' T a]
  simp only [ha, if_true]
  have hpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨a, ha⟩
  omega

theorem sum_disLevel {T : Finset (ZMod d)} {b : ZMod d} (hb : b ∈ T) :
    ∑ t ∈ T, (disLevel b t : ℤ) = (T.card : ℤ) - 1 := by
  classical
  have h : ∀ t ∈ T, ((disLevel b t : ℕ) : ℤ) = 1 - (if t = b then (1 : ℤ) else 0) := by
    intro t _; unfold disLevel; split <;> simp
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.sum_ite_eq' T b (fun _ => (1 : ℤ))]
  simp [hb]

/-- Indicator sums over a shifted membership condition. -/
theorem sum_indicator_shift (S : Finset (ZMod d)) (x : ZMod d) :
    ∑ t ∈ S, (if x = t - 1 then (1 : ℤ) else 0)
      = if x + 1 ∈ S then (1 : ℤ) else 0 := by
  classical
  have hiff : ∀ t : ZMod d, (x = t - 1) ↔ (t = x + 1) := by
    intro t; constructor <;> intro h <;> [rw [h]; rw [h]] <;> ring
  rw [Finset.sum_congr rfl (fun t _ => by rw [if_congr (hiff t) rfl rfl])]
  rw [Finset.sum_ite_eq' S (x + 1) (fun _ => (1 : ℤ))]

theorem runSet_zero (t : ZMod d) : runSet t 0 = (∅ : Finset (ZMod d)) := by
  simp [runSet]

theorem levelVec_zero (t x : ZMod d) :
    levelVec t 0 x = if x = t - 1 then (1 : ℤ) else 0 := by
  simp [levelVec, runSet_zero]

theorem levelVec_one (t x : ZMod d) :
    levelVec t 1 x = (if x = t then (1 : ℤ) else 0) - (if x = t - 1 then 1 else 0) := by
  have hrun : runSet t 1 = {t - 1} := by
    simp [runSet]
  have ht : t - 1 + ((1 : ℕ) : ZMod d) = t := by push_cast; ring
  simp [levelVec, hrun]

/-- Casting is injective below the modulus. -/
theorem natCast_inj_lt {i j : ℕ} (hi : i < d) (hj : j < d)
    (h : ((i : ZMod d)) = (j : ZMod d)) : i = j := by
  have hi' : ((i : ZMod d)).val = i := by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt hi
  have hj' : ((j : ZMod d)).val = j := by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt hj
  rw [← hi', ← hj', h]

/-- The first negative really is in the run. -/
theorem pred_mem_runSet {a : ZMod d} {ℓ : ℕ} (h : 1 ≤ ℓ) : a - 1 ∈ runSet a ℓ := by
  rw [runSet, Finset.mem_image]
  exact ⟨0, Finset.mem_range.mpr (by omega), by simp⟩

/-- The top of the promotion, `a + (s - 2)`. -/
def topIdx (T : Finset (ZMod d)) (a : ZMod d) : ZMod d :=
  a - 1 + ((T.card - 1 : ℕ) : ZMod d)

/-- The top of the promotion is not one of its negatives. -/
theorem topIdx_not_mem_runSet {T : Finset (ZMod d)} {a : ZMod d}
    (h : T.card - 1 < d) : topIdx T a ∉ runSet a (T.card - 1) := by
  intro hmem
  rw [runSet, Finset.mem_image] at hmem
  obtain ⟨j, hj, hji⟩ := hmem
  rw [Finset.mem_range] at hj
  have hcast : ((j : ZMod d)) = ((T.card - 1 : ℕ) : ZMod d) := by
    unfold topIdx at hji
    exact add_left_cancel hji
  have := natCast_inj_lt (by omega) h hcast
  omega

/-- The top of the promotion differs from the first negative. -/
theorem topIdx_ne_pred {T : Finset (ZMod d)} {a : ZMod d}
    (h1 : 1 ≤ T.card - 1) (h2 : T.card - 1 < d) : topIdx T a ≠ a - 1 := by
  intro hEq
  unfold topIdx at hEq
  have hz : ((T.card - 1 : ℕ) : ZMod d) = ((0 : ℕ) : ZMod d) := by
    have h0 : a - 1 + ((T.card - 1 : ℕ) : ZMod d) = a - 1 + ((0 : ℕ) : ZMod d) := by
      simpa using hEq
    exact add_left_cancel h0
  have := natCast_inj_lt h2 (by omega) hz
  omega

/-- The concentrated vector, pointwise: one positive at the top of the
promotion, the negative run, and the level-zero positives of the rest. -/
theorem assemble_conLevel_apply {T : Finset (ZMod d)} {a : ZMod d} (ha : a ∈ T)
    (x : ZMod d) :
    assemble T (conLevel T a) x
      = (if x = topIdx T a then (1 : ℤ) else 0)
        - (if x ∈ runSet a (T.card - 1) then 1 else 0)
        + (if x + 1 ∈ T.erase a then 1 else 0) := by
  classical
  unfold assemble
  rw [← Finset.add_sum_erase _ _ ha]
  have hhead : levelVec a (conLevel T a a) x
      = (if x = topIdx T a then (1 : ℤ) else 0)
        - (if x ∈ runSet a (T.card - 1) then 1 else 0) := by
    unfold conLevel levelVec topIdx; simp
  have htail : ∀ t ∈ T.erase a, levelVec t (conLevel T a t) x
      = (if x = t - 1 then (1 : ℤ) else 0) := by
    intro t ht
    have hne : t ≠ a := Finset.ne_of_mem_erase ht
    have : conLevel T a t = 0 := by unfold conLevel; simp [hne]
    rw [this, levelVec_zero]
  rw [hhead, Finset.sum_congr rfl htail, sum_indicator_shift]

/-- The distributed vector, pointwise. -/
theorem assemble_disLevel_apply {T : Finset (ZMod d)} {b : ZMod d} (hb : b ∈ T)
    (x : ZMod d) :
    assemble T (disLevel b) x
      = (if x = b - 1 then (1 : ℤ) else 0)
        + (if x ∈ T.erase b then 1 else 0)
        - (if x + 1 ∈ T.erase b then 1 else 0) := by
  classical
  unfold assemble
  rw [← Finset.add_sum_erase _ _ hb]
  have hhead : levelVec b (disLevel b b) x = (if x = b - 1 then (1 : ℤ) else 0) := by
    unfold disLevel; simp [levelVec_zero]
  have htail : ∀ t ∈ T.erase b, levelVec t (disLevel b t) x
      = (if x = t then (1 : ℤ) else 0) - (if x = t - 1 then 1 else 0) := by
    intro t ht
    have hne : t ≠ b := Finset.ne_of_mem_erase ht
    have : disLevel b t = 1 := by unfold disLevel; simp [hne]
    rw [this, levelVec_one]
  rw [hhead, Finset.sum_congr rfl htail, Finset.sum_sub_distrib,
    sum_indicator_shift]
  have hmem : ∑ t ∈ T.erase b, (if x = t then (1 : ℤ) else 0)
      = if x ∈ T.erase b then 1 else 0 := by
    rw [Finset.sum_congr rfl (fun t _ => by rw [if_congr (eq_comm (a := x) (b := t)) rfl rfl])]
    rw [Finset.sum_ite_eq' (T.erase b) x (fun _ => (1 : ℤ))]
  rw [hmem]
  ring

/-- Erasing two distinct members of `T` differs by two point indicators. -/
theorem erase_diff_indicator {T : Finset (ZMod d)} {a b : ZMod d}
    (ha : a ∈ T) (hb : b ∈ T) (y : ZMod d) :
    (if y ∈ T.erase a then (1 : ℤ) else 0) - (if y ∈ T.erase b then 1 else 0)
      = (if y = b then 1 else 0) - (if y = a then 1 else 0) := by
  classical
  by_cases hy : y ∈ T
  · have h1 : (y ∈ T.erase a) ↔ y ≠ a := by simp [Finset.mem_erase, hy]
    have h2 : (y ∈ T.erase b) ↔ y ≠ b := by simp [Finset.mem_erase, hy]
    simp only [h1, h2]
    by_cases hya : y = a
    · by_cases hyb : y = b
      · have hab : a = b := by rw [← hya, hyb]
        simp [hya, hab]
      · have hab : a ≠ b := by rw [← hya]; exact hyb
        simp [hya, hab]
    · by_cases hyb : y = b
      · have hba : b ≠ a := by rw [← hyb]; exact hya
        simp [hyb, hba]
      · simp [hya, hyb]
  · have h1 : y ∉ T.erase a := fun h => hy (Finset.mem_of_mem_erase h)
    have h2 : y ∉ T.erase b := fun h => hy (Finset.mem_of_mem_erase h)
    have h3 : y ≠ a := fun h => hy (h ▸ ha)
    have h4 : y ≠ b := fun h => hy (h ▸ hb)
    simp [h1, h2, h3, h4]

theorem succ_eq_iff (x c : ZMod d) : (x + 1 = c) ↔ (x = c - 1) := by
  constructor <;> intro h
  · rw [← h]; ring
  · rw [h]; ring

/-- **Compatibility, coincident indices.**  When the concentrated and
distributed vectors share their distinguished index, the two
`T.erase a` terms cancel and the single condition `topIdx ∉ T.erase a`
suffices. -/
theorem compat_self {T : Finset (ZMod d)} {a : ZMod d} (ha : a ∈ T)
    (hs : 2 ≤ T.card) (hsd : T.card < d)
    (hC : topIdx T a ∉ T.erase a) (x : ZMod d) :
    assemble T (conLevel T a) x + assemble T (disLevel a) x ≤ 1 := by
  classical
  have hcard1 : 1 ≤ T.card - 1 := by omega
  have hcardd : T.card - 1 < d := by omega
  have hTop : topIdx T a ∉ runSet a (T.card - 1) := topIdx_not_mem_runSet hcardd
  have hTopPred : topIdx T a ≠ a - 1 := topIdx_ne_pred hcard1 hcardd
  have hPred : a - 1 ∈ runSet a (T.card - 1) := pred_mem_runSet hcard1
  rw [assemble_conLevel_apply ha, assemble_disLevel_apply ha]
  by_cases h1 : x = topIdx T a
  · have e1 : x ∉ runSet a (T.card - 1) := by rw [h1]; exact hTop
    have e2 : ¬ (x = a - 1) := by rw [h1]; exact hTopPred
    have e3 : x ∉ T.erase a := by rw [h1]; exact hC
    simp only [if_pos h1, if_neg e1, if_neg e2, if_neg e3]
    split_ifs <;> omega
  · by_cases h2 : x = a - 1
    · have e4 : x ∈ runSet a (T.card - 1) := by rw [h2]; exact hPred
      simp only [if_neg h1, if_pos h2, if_pos e4]
      split_ifs <;> omega
    · simp only [if_neg h1, if_neg h2]
      split_ifs <;> omega

/-- **Compatibility, distinct indices.**  With `b ≠ a` the three conditions
produced by the pigeonhole — `b - 1` inside the negative run, `b - 1`
outside `T`, and the top outside `T.erase b` — make the two vectors
compatible. -/
theorem compat_pair {T : Finset (ZMod d)} {a b : ZMod d} (ha : a ∈ T) (hb : b ∈ T)
    (hab : a ≠ b) (hs : 2 ≤ T.card) (hsd : T.card < d)
    (hC1 : b - 1 ∈ runSet a (T.card - 1)) (hC2 : b - 1 ∉ T)
    (hC3 : topIdx T a ∉ T.erase b) (x : ZMod d) :
    assemble T (conLevel T a) x + assemble T (disLevel b) x ≤ 1 := by
  classical
  have hcard1 : 1 ≤ T.card - 1 := by omega
  have hcardd : T.card - 1 < d := by omega
  have hTop : topIdx T a ∉ runSet a (T.card - 1) := topIdx_not_mem_runSet hcardd
  have hTopPred : topIdx T a ≠ a - 1 := topIdx_ne_pred hcard1 hcardd
  rw [assemble_conLevel_apply ha, assemble_disLevel_apply hb]
  -- replace the `erase a` indicator using the two-point difference
  have hEA : (if x + 1 ∈ T.erase a then (1 : ℤ) else 0)
      = (if x + 1 ∈ T.erase b then 1 else 0) + (if x + 1 = b then 1 else 0)
        - (if x + 1 = a then 1 else 0) := by
    have h := erase_diff_indicator ha hb (x + 1); linarith
  rw [hEA, if_congr (succ_eq_iff x b) rfl rfl, if_congr (succ_eq_iff x a) rfl rfl]
  by_cases h1 : x = b - 1
  · have hxTop : x ≠ topIdx T a := by
      intro hEq; exact hTop (hEq ▸ (h1 ▸ hC1))
    have hxT : x ∉ T.erase b := fun h => hC2 (h1 ▸ Finset.mem_of_mem_erase h)
    have hxa : x ≠ a - 1 := by
      intro hEq
      apply hab
      have : b - 1 = a - 1 := h1 ▸ hEq
      have : b = a := by
        have := congrArg (· + 1) this; simpa using this
      exact this.symm
    have e1 : x ∈ runSet a (T.card - 1) := by rw [h1]; exact hC1
    simp only [if_neg hxTop, if_pos e1, if_pos h1, if_neg hxa, if_neg hxT]
    split_ifs <;> omega
  · by_cases h2 : x = topIdx T a
    · have e2 : x ∉ runSet a (T.card - 1) := by rw [h2]; exact hTop
      have e3 : x ∉ T.erase b := by rw [h2]; exact hC3
      have e4 : ¬ (x = a - 1) := by rw [h2]; exact hTopPred
      simp only [if_neg h1, if_pos h2, if_neg e2, if_neg e3, if_neg e4]
      split_ifs <;> omega
    · simp only [if_neg h1, if_neg h2]
      split_ifs <;> omega

/-- The concentrated vector never drops below `-1`: its only negatives are
the run, which has distinct indices. -/
theorem assemble_conLevel_ge {T : Finset (ZMod d)} {a : ZMod d} (ha : a ∈ T)
    (x : ZMod d) : -1 ≤ assemble T (conLevel T a) x := by
  classical
  rw [assemble_conLevel_apply ha]; split_ifs <;> omega

/-- The distributed vector never drops below `-1`. -/
theorem assemble_disLevel_ge {T : Finset (ZMod d)} {b : ZMod d} (hb : b ∈ T)
    (x : ZMod d) : -1 ≤ assemble T (disLevel b) x := by
  classical
  rw [assemble_disLevel_apply hb]; split_ifs <;> omega

/-- `topIdx` written with the shift `s - 2`. -/
theorem topIdx_eq_add {T : Finset (ZMod d)} (a : ZMod d) :
    topIdx T a = a + (((T.card - 1 : ℕ) : ZMod d) - 1) := by
  unfold topIdx; ring

variable [NeZero d]

/-- **The stratum-one compatible pair.**  For every support `T` with
`2 ≤ |T| < d` there are two level assignments whose assembled vectors each
have coordinate sum `1` and value `∑_{t ∈ T} 2^(t-1)`, and whose sum is
bounded by `1` coordinatewise.

These are exactly the two block vectors of the cancelling triple: the third
member is their negative, carried by the extra entry with multiplicity two. -/
theorem exists_compatible_pair (T : Finset (ZMod d))
    (hs : 2 ≤ T.card) (hsd : T.card < d) :
    ∃ L₁ L₂ : ZMod d → ℕ,
      coeffSum (assemble T L₁) = 1 ∧ coeffSum (assemble T L₂) = 1 ∧
      value (assemble T L₁) = ∑ t ∈ T, pow2 (t - 1) ∧
      value (assemble T L₂) = ∑ t ∈ T, pow2 (t - 1) ∧
      (∀ x, -1 ≤ assemble T L₁ x) ∧ (∀ x, -1 ≤ assemble T L₂ x) ∧
      ∀ x, assemble T L₁ x + assemble T L₂ x ≤ 1 := by
  classical
  have hne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hdpos : 1 ≤ d := by omega
  -- the two level assignments always have admissible levels
  have hLcon : ∀ (a : ZMod d), ∀ t ∈ T, conLevel T a t ≤ d := by
    intro a t _; unfold conLevel; split <;> omega
  have hLdis : ∀ (b : ZMod d), ∀ t ∈ T, disLevel b t ≤ d := by
    intro b t _; unfold disLevel; split <;> omega
  -- a uniform packaging of the two assignments, given a compatible pair
  have pack : ∀ a b : ZMod d, a ∈ T → b ∈ T →
      (∀ x, assemble T (conLevel T a) x + assemble T (disLevel b) x ≤ 1) →
      ∃ L₁ L₂ : ZMod d → ℕ,
        coeffSum (assemble T L₁) = 1 ∧ coeffSum (assemble T L₂) = 1 ∧
        value (assemble T L₁) = ∑ t ∈ T, pow2 (t - 1) ∧
        value (assemble T L₂) = ∑ t ∈ T, pow2 (t - 1) ∧
        (∀ x, -1 ≤ assemble T L₁ x) ∧ (∀ x, -1 ≤ assemble T L₂ x) ∧
        ∀ x, assemble T L₁ x + assemble T L₂ x ≤ 1 := by
    intro a b ha hb hcompat
    refine ⟨conLevel T a, disLevel b, ?_, ?_, ?_, ?_,
      assemble_conLevel_ge ha, assemble_disLevel_ge hb, hcompat⟩
    · rw [coeffSum_assemble T _ (hLcon a), sum_conLevel ha]; ring
    · rw [coeffSum_assemble T _ (hLdis b), sum_disLevel hb]; ring
    · exact value_assemble T _ (hLcon a)
    · exact value_assemble T _ (hLdis b)
  rcases exists_stratum_one_index_pair T hne hsd (((T.card - 1 : ℕ) : ZMod d) - 1)
    with ⟨a, ha, hA⟩ | ⟨a, ha, hfail, hmem⟩
  · -- coincident indices
    refine pack a a ha ha ?_
    exact compat_self ha hs hsd (by rw [topIdx_eq_add]; exact hA)
  · -- distinct indices: `b` is the top of the promotion
    set b : ZMod d := a + (((T.card - 1 : ℕ) : ZMod d) - 1) with hbdef
    have hb : b ∈ T := Finset.mem_of_mem_erase hmem
    have hba : b ≠ a := Finset.ne_of_mem_erase hmem
    have htop : topIdx T a = b := by rw [topIdx_eq_add, hbdef]
    have hC2 : b - 1 ∉ T := by
      have : b - 1 = a + ((((T.card - 1 : ℕ) : ZMod d) - 1) - 1) := by rw [hbdef]; ring
      rw [this]; exact hfail
    have hj : ((T.card - 2 : ℕ) : ZMod d) = ((T.card - 1 : ℕ) : ZMod d) - 1 := by
      have hrw : T.card - 1 = (T.card - 2) + 1 := by omega
      rw [hrw]; push_cast; ring
    have hC1 : b - 1 ∈ runSet a (T.card - 1) := by
      rw [runSet, Finset.mem_image]
      refine ⟨T.card - 2, Finset.mem_range.mpr (by omega), ?_⟩
      rw [hj, hbdef]; ring
    have hC3 : topIdx T a ∉ T.erase b := by
      rw [htop]; exact fun h => (Finset.ne_of_mem_erase h) rfl
    exact pack a b ha hb (compat_pair ha hb (Ne.symm hba) hs hsd hC1 hC2 hC3)

end StratumOne

end MinModulus
