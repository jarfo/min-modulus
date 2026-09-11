import MinModulus.G1OddPrimaryDyadicCharge
import MinModulus.G1DoublingCycleRigidity

namespace MinModulus

/-- The dyadic deficit of a nontrivial stratum is no larger than the
stratum itself. -/
theorem stratumDeficit_le_stratumBound {k t : ℕ} (hk : 2 ≤ k) :
    2 ^ min t (Nat.log 2 k) ≤ stratumBound k t := by
  have hlog : Nat.log 2 k ≤ k - 1 := by
    have hlt := Nat.log_lt_self 2 (by omega : k ≠ 0)
    omega
  exact (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ))
    ((min_le_right _ _).trans hlog)).trans (two_pow_pred_le_stratumBound hk)

/-- A Mersenne factor pays for a coordinate loss of one fewer than its
exponent, in every stratum. -/
theorem stratumBound_le_mersenne_mul_of_coordinate_loss
    {n b t : ℕ} (hb : b ≤ n) (hk : 2 ≤ n - b) :
    stratumBound n t ≤ (2 ^ (b + 1) - 1) * stratumBound (n - b) t := by
  let k := n - b
  let A := 2 ^ b
  let D := 2 ^ min t (Nat.log 2 k)
  let E := 2 ^ min t (Nat.log 2 n)
  have hk2 : 2 ≤ k := hk
  have hkn : k ≤ n := Nat.sub_le _ _
  have hlog : Nat.log 2 k ≤ Nat.log 2 n := Nat.log_mono_right hkn
  have hDE : D ≤ E := Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ))
    (min_le_min_left t hlog)
  have hDS : D ≤ stratumBound k t := stratumDeficit_le_stratumBound hk2
  have hDpow : D ≤ 2 ^ k := Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ))
    ((min_le_right _ _).trans (Nat.log_le_self 2 k))
  have hEpow : E ≤ 2 ^ n := Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ))
    ((min_le_right _ _).trans (Nat.log_le_self 2 n))
  have hKsum : stratumBound k t + D = 2 ^ k := Nat.sub_add_cancel hDpow
  have hNsum : stratumBound n t + E = 2 ^ n := Nat.sub_add_cancel hEpow
  have hApos : 1 ≤ A := Nat.one_le_two_pow
  have hApred : A - 1 + 1 = A := Nat.sub_add_cancel hApos
  have hpower : 2 ^ n = A * 2 ^ k := by
    dsimp [A, k]
    rw [← pow_add, Nat.add_sub_of_le hb]
  have hcharge : (A - 1) * D ≤ (A - 1) * stratumBound k t :=
    Nat.mul_le_mul_left _ hDS
  have hfactor : 2 ^ (b + 1) - 1 + 1 = 2 * A := by
    rw [Nat.sub_add_cancel (Nat.one_le_two_pow), pow_succ]
    dsimp [A]
    omega
  change stratumBound n t ≤ (2 ^ (b + 1) - 1) * stratumBound k t
  nlinarith

/-- The one-unit improvement over the half-cube charge is decisive at
exact Mersenne order. -/
theorem oddPrimaryStratumCharge_of_mersenne_card
    {n b t r : ℕ} (hb : b ≤ n) (hk : 2 ≤ n - b)
    (hr : 2 ^ (b + 1) - 1 ≤ r) :
    OddPrimaryStratumCharge n b t r := by
  exact (stratumBound_le_mersenne_mul_of_coordinate_loss hb hk).trans
    (Nat.mul_le_mul_right _ hr)

theorem order_lt_mersenne_of_oddPrimaryStratumChargeFailure
    {n b t r : ℕ} (hb : b ≤ n) (hk : 2 ≤ n - b)
    (hfail : ¬ OddPrimaryStratumCharge n b t r) :
    r < 2 ^ (b + 1) - 1 := by
  by_contra hnot
  exact hfail (oddPrimaryStratumCharge_of_mersenne_card hb hk (by omega))

/-- Exact cycle order forces at least as many deleted coordinates as
cycle entries whenever the quotient charge fails. -/
theorem cycle_length_le_card_of_mersenne_chargeFailure
    {n b t d r : ℕ} (hb : b ≤ n) (hk : 2 ≤ n - b)
    (hr : 2 ^ d - 1 ≤ r)
    (hfail : ¬ OddPrimaryStratumCharge n b t r) : d ≤ b := by
  by_contra hnot
  have hbd : b + 1 ≤ d := by omega
  have hp := Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hbd
  have hmersenne : 2 ^ (b + 1) - 1 ≤ r := (Nat.sub_le_sub_right hp 1).trans hr
  exact hfail (oddPrimaryStratumCharge_of_mersenne_card hb hk hmersenne)

/-- The sufficient factor cannot be lowered uniformly: retaining two
coordinates at valuation one attains it. -/
theorem oddPrimaryStratumCharge_two_retained_valuation_one_iff
    {b r : ℕ} :
    OddPrimaryStratumCharge (b + 2) b 1 r ↔ 2 ^ (b + 1) - 1 ≤ r := by
  have hlog : 1 ≤ Nat.log 2 (b + 2) := Nat.le_log_of_pow_le (by omega) (by simp)
  have hmin : min 1 (Nat.log 2 (b + 2)) = 1 := min_eq_left hlog
  have hpow : 2 ^ (b + 2) = 2 * 2 ^ (b + 1) := by
    rw [show b + 2 = (b + 1) + 1 by omega, pow_succ]
    omega
  have hpos : 1 ≤ 2 ^ (b + 1) := Nat.one_le_two_pow
  simp only [OddPrimaryStratumCharge, stratumBound, hmin,
    Nat.add_sub_cancel_left, show Nat.log 2 2 = 1 by decide,
    min_self, Nat.reducePow, Nat.reduceSub]
  omega

/-- Existing unconditional doubling rigidity feeds the sharper charge
directly, for a translated subtuple in any abelian group. -/
theorem leaf_cycle_length_le_card_of_kernel_chargeFailure
    {G : Type*} [AddCommGroup G] {n d t : ℕ} (hd : 2 ≤ d)
    (g : Fin n → G) (hg : ValidTuple g)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (base y : G) (R : Equiv.Perm (Fin d))
    (hdouble : ∀ i, g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hspan : AddSubgroup.closure (Set.range (fun i ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y)
    (B : Finset (Fin n)) (hkeep : 2 ≤ n - B.card)
    (hfail : ¬ OddPrimaryStratumCharge n B.card t (addOrderOf y)) :
    d ≤ B.card := by
  have horder := (leaf_isCycle_and_order_eq_mersenne_of_valid_doubling
    hd g hg leaf hleaf base y R hdouble hspan).2
  exact cycle_length_le_card_of_mersenne_chargeFailure
    (by simpa using Finset.card_le_univ B) hkeep (by omega) hfail

/-- The existing full-cycle descent package has a strictly stronger
deletion alternative when its generator has the known exact cycle order. -/
theorem OddPrimaryFullCycleMinimalTransversalChargeDescent.recursive_or_cycle_le_card
    {m t q d : ℕ} {g : Fin (m + 1) → ZMod (2 ^ t * q)}
    {y : ZMod (2 ^ t * q)} {B : Finset (Fin (m + 1))}
    (hdescent : OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d)
    (horder : 2 ^ d - 1 ≤ addOrderOf y) :
    OddPrimaryRecursiveCounterexample (m + 1) B.card t q (addOrderOf y) ∨
      d ≤ B.card := by
  rcases hdescent.2.2.2.2.2.2 with hrec | ⟨_, hfail, hkeep, _⟩
  · exact Or.inl hrec
  · exact Or.inr (cycle_length_le_card_of_mersenne_chargeFailure
      (by simpa using Finset.card_le_univ B) hkeep horder hfail)

end MinModulus
