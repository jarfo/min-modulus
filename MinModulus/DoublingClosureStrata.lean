/-
# Exact power-gap order and stratum bounds for affine doubling closure

The first full doubling orbit returns after n steps to some earlier step t.
Its generator order divides 2^n-2^t. Validity's binary half bound excludes
every proper divisor, giving exact order. Transporting the closed tuple to
this generated subgroup and applying the proved global class bound forces
t ≤ floor(log₂ n). The power gap divides the ambient modulus, so its
two-power factor also forces t ≤ the ambient valuation.

This proves the full stratum bound, with explicit critical-G1 exclusion,
odd-G2 threshold, and exceptional-G3 exclusion for this class. None of the
three unrestricted global conjectural inputs is assumed or proved here.
-/
import MinModulus.DoublingClosure

namespace MinModulus
open Finset Function

/-- A valid doubling-closed tuple has a full-orbit generator of exact
power-gap order. The global class bound holds inside its generated subgroup. -/
theorem exists_power_gap_order_of_valid_doubling_closed
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (R : Fin n → Fin n) (hd : ∀ i, g (R i) = 2 • g i) :
    ∃ a, ∃ t < n, addOrderOf (g a) = 2 ^ n - 2 ^ t ∧
      globalBound n ≤ addOrderOf (g a) ∧ (2 ^ n - 2 ^ t) ∣ N := by
  classical
  obtain ⟨a, e, he⟩ := exists_doubling_orbit_equiv_of_valid_zmod (by omega) g hg R hd
  let last : Fin n := ⟨n - 1, by omega⟩
  obtain ⟨i, hi⟩ := e.surjective (R (e last))
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hperiod : 2 ^ n • g a = 2 ^ i.val • g a := by
    rw [hpow, mul_nsmul']
    change 2 • (2 ^ last.val • g a) = 2 ^ i.val • g a
    rw [← he last, ← hd, ← hi, he]
  have hle : 2 ^ i.val ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  have hkill : (2 ^ n - 2 ^ i.val) • g a = 0 := by
    rw [sub_nsmul _ hle, hperiod, add_neg_cancel]
  have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hkill
  let H := AddSubgroup.zmultiples (g a)
  have hmem : ∀ j, g j ∈ H := by
    intro j
    obtain ⟨k, rfl⟩ := e.surjective j
    rw [he]
    exact H.nsmul_mem (AddSubgroup.mem_zmultiples (g a)) _
  let x : Fin n → H := fun j ↦ ⟨g j, hmem j⟩
  have hx : ValidTuple x := by
    apply validTuple_of_comp H.subtype
    exact hg
  have hlower := two_pow_pred_le_card_of_validTuple x hx
  rw [← Nat.card_eq_fintype_card, Nat.card_zmultiples] at hlower
  have hpos : 0 < 2 ^ i.val := by positivity
  have ho : addOrderOf (g a) = 2 ^ n - 2 ^ i.val := by
    obtain ⟨k, hk⟩ := hdvd
    have hk1 : k = 1 := by
      have hgapPos : 0 < 2 ^ n - 2 ^ i.val := by
        apply Nat.sub_pos_of_lt
        exact Nat.pow_lt_pow_right (by omega) i.isLt
      have hordpos : 0 < addOrderOf (g a) := lt_of_lt_of_le (by positivity) hlower
      have hkpos : 0 < k := by nlinarith
      by_contra hkne
      have hk2 : 2 ≤ k := by omega
      have hgapAdd := Nat.sub_add_cancel hle
      nlinarith
    simpa [hk1] using hk.symm
  letI : IsAddCyclic H := AddSubgroup.isAddCyclic H
  letI : NeZero (Nat.card H) := ⟨ne_of_gt (Nat.card_pos)⟩
  let φ : H ≃+ ZMod (Nat.card H) := (zmodAddCyclicAddEquiv (G := H) inferInstance).symm
  have hz : ValidTuple (fun j ↦ φ (x j)) := validTuple_comp hx φ.toAddMonoidHom φ.injective
  have hdx : ∀ j, x (R j) = 2 • x j := by
    intro j
    apply Subtype.ext
    exact hd j
  have hbound := global_lower_bound_of_valid_affine_doubling_closed hn
    (fun j ↦ φ (x j)) hz 0 (fun j ↦ ⟨R j, by simp [hdx]⟩)
  have hbound' : globalBound n ≤ addOrderOf (g a) := by
    simpa only [H, Nat.card_zmultiples] using hbound
  refine ⟨a, i.val, i.isLt, ho, hbound', ?_⟩
  rw [← ho]
  simpa using (addOrderOf_dvd_card (x := g a))

/-- Every affine-doubling-closed valid tuple forces divisibility of its
modulus by an admissible power gap, with exponent at most `floor(log₂ n)`. -/
theorem exists_power_gap_dvd_of_valid_affine_doubling_closed
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hclosed : ∀ i, ∃ j, g j = 2 • g i + b) :
    ∃ t, t < n ∧ t ≤ Nat.log 2 n ∧ (2 ^ n - 2 ^ t) ∣ N := by
  classical
  let R : Fin n → Fin n := fun i ↦ Classical.choose (hclosed i)
  have hR : ∀ i, g (R i) = 2 • g i + b := fun i ↦ Classical.choose_spec (hclosed i)
  have hv : ValidTuple (fun i ↦ g i + b) := by
    simpa using validTuple_sub_const g hg (-b)
  have hd : ∀ i, g (R i) + b = 2 • (g i + b) := by
    intro i
    rw [hR]
    simp only [two_nsmul]
    abel
  obtain ⟨a, t, ht, horder, hbound, hdvd⟩ :=
    exists_power_gap_order_of_valid_doubling_closed hn (fun i ↦ g i + b) hv R hd
  have hpow : 2 ^ t ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  have hlogpow : 2 ^ Nat.log 2 n ≤ 2 ^ n :=
    (Nat.pow_log_le_self 2 (by omega)).trans (Nat.lt_two_pow_self.le)
  have hdelta : 2 ^ t ≤ 2 ^ Nat.log 2 n := by
    rw [horder] at hbound
    unfold globalBound at hbound
    omega
  exact ⟨t, ht, (pow_le_pow_iff_right₀ (by omega : 1 < (2 : ℕ))).mp hdelta, hdvd⟩

/-- The exact stratum lower bound holds for affine doubling closure:
gap divisibility also bounds the gap exponent by the ambient valuation. -/
theorem stratum_lower_bound_of_valid_affine_doubling_closed
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q)
    (g : Fin n → ZMod (2 ^ s * q)) (hg : ValidTuple g) (b : ZMod (2 ^ s * q))
    (hclosed : ∀ i, ∃ j, g j = 2 • g i + b) :
    stratumBound n s ≤ 2 ^ s * q := by
  have hqpos : 0 < q := hq.pos
  have hNpos : 0 < 2 ^ s * q := by positivity
  letI : NeZero (2 ^ s * q) := ⟨ne_of_gt hNpos⟩
  obtain ⟨t, ht, htlog, hdvd⟩ :=
    exists_power_gap_dvd_of_valid_affine_doubling_closed hn g hg b hclosed
  have htwodvd : 2 ^ t ∣ 2 ^ s * q := by
    apply dvd_trans _ hdvd
    exact Nat.dvd_sub (pow_dvd_pow 2 (by omega)) (dvd_refl _)
  have hts : t ≤ s := by
    by_contra hnot
    have hstep : 2 ^ s * 2 ∣ 2 ^ s * q := by
      rw [← pow_succ]
      exact (pow_dvd_pow 2 (by omega : s + 1 ≤ t)).trans htwodvd
    have htwo : 2 ∣ q := Nat.dvd_of_mul_dvd_mul_left (by positivity) hstep
    exact hq.not_two_dvd_nat htwo
  have htmin : t ≤ min s (Nat.log 2 n) := le_min hts htlog
  have hgap : stratumBound n s ≤ 2 ^ n - 2 ^ t :=
    Nat.sub_le_sub_left (Nat.pow_le_pow_right (by omega) htmin) _
  exact hgap.trans (Nat.le_of_dvd hNpos hdvd)

/-- No tuple in the affine-doubling-closed class can inhabit a critical
stratum. In particular, this class cannot supply an unresolved G1 input. -/
theorem not_validTuple_of_critical_affine_doubling_closed
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q)
    (hcritical : 2 ^ s * q < stratumBound n s)
    (g : Fin n → ZMod (2 ^ s * q)) (b : ZMod (2 ^ s * q))
    (hclosed : ∀ i, ∃ j, g j = 2 • g i + b) : ¬ ValidTuple g := by
  intro hg
  exact (not_lt_of_ge
    (stratum_lower_bound_of_valid_affine_doubling_closed hn hq g hg b hclosed)) hcritical

/-- The exact G2 numerical threshold holds for affine-doubling-closed
tuples in every dimension, including the two trivial dimensions. -/
theorem odd_lower_bound_of_valid_affine_doubling_closed
    {n N : ℕ} (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hclosed : ∀ i, ∃ j, g j = 2 • g i + b) : 2 ^ n - 1 ≤ N := by
  by_cases hn : 2 ≤ n
  · have h := stratum_lower_bound_of_valid_affine_doubling_closed
      (n := n) (s := 0) (q := N) hn hN
    rw [show (2 : ℕ) ^ 0 * N = N by simp] at h
    simpa [stratumBound] using h g hg b hclosed
  · have hpos := hN.pos
    interval_cases n <;> norm_num
    omega

/-- The G3 exceptional modulus admits no affine-doubling-closed valid
tuple. Closure is a genuine restriction; the unrestricted G3 stays open. -/
theorem not_validTuple_exceptional_of_affine_doubling_closed
    {n : ℕ} (hn : 2 ≤ n) (hnpow : 2 ^ Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2 * globalBound (n - 1)))
    (b : ZMod (2 * globalBound (n - 1)))
    (hclosed : ∀ i, ∃ j, g j = 2 • g i + b) : ¬ ValidTuple g := by
  intro hg
  have hnprev : 2 ≤ n - 1 := by
    by_contra hnot
    have hn2 : n = 2 := by omega
    subst n
    norm_num at hnpow
  have hlogprev : Nat.log 2 (n - 1) = Nat.log 2 n := by
    have hlog_adj : Nat.log 2 (n - 1) = Nat.log 2 n ↔ 2 ^ Nat.log 2 n ≠ n := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
        (Nat.log_eq_log_succ_iff (b := 2) (n := n - 1) (by omega) (by omega))
    exact hlog_adj.mpr hnpow
  have hB : 2 ≤ globalBound (n - 1) := (nmin_eq hnprev).1.1
  letI : NeZero (2 * globalBound (n - 1)) := ⟨by omega⟩
  have hbound := global_lower_bound_of_valid_affine_doubling_closed hn g hg b hclosed
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hlogle := Nat.pow_log_le_self 2 (by omega : n - 1 ≠ 0)
  rw [hlogprev] at hlogle
  have hpredpow := Nat.lt_two_pow_self (n := n - 1)
  have hpos : 0 < 2 ^ Nat.log 2 n := by positivity
  unfold globalBound at hbound
  rw [hlogprev] at hbound
  omega

end MinModulus
