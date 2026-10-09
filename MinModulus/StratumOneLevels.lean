import MinModulus.StratumOnePigeonhole

/-!
# Promotion levels at the first even stratum

Fix `d ≥ 1` and work modulo the Mersenne number `M = 2^d - 1`.  Because
`2^d = 1` in `ZMod M`, the assignment `x ↦ 2^x` descends to the cyclic
index group `ZMod d`; this is `pow2`.

The *promotion level* representation of `2^(t-1)` at level `ℓ` is

    rep(t, ℓ) = e_{t-1+ℓ} - ∑_{j < ℓ} e_{t-1+j},

a vector of integers indexed by `ZMod d`.  Its coordinate sum is `1 - ℓ`
and its value `∑ x, rep(t,ℓ)(x) • 2^x` is `2^(t-1)`, independently of `ℓ`:
the geometric sum `∑_{j<ℓ} 2^j = 2^ℓ - 1` telescopes against the leading
term `2^ℓ`.  Choosing levels summing to `s - 1` over a support of size `s`
therefore produces vectors of coordinate sum `1` and a prescribed value,
which is what the stratum-one triple needs.
-/

namespace MinModulus

open Finset

namespace StratumOne

variable {d : ℕ}

/-- `2 ^ x` for a cyclic index `x : ZMod d`, valued in `ZMod (2 ^ d - 1)`. -/
def pow2 (x : ZMod d) : ZMod (2 ^ d - 1) := (2 : ZMod (2 ^ d - 1)) ^ x.val

/-- `2 ^ d = 1` modulo the Mersenne number `2 ^ d - 1`. -/
theorem two_pow_self (d : ℕ) :
    (2 : ZMod (2 ^ d - 1)) ^ d = 1 := by
  have hmod : (1 : ℕ) ≡ 2 ^ d [MOD 2 ^ d - 1] :=
    (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr dvd_rfl
  have hcast : ((2 ^ d : ℕ) : ZMod (2 ^ d - 1)) = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod.symm
    simpa using h
  calc (2 : ZMod (2 ^ d - 1)) ^ d = ((2 ^ d : ℕ) : ZMod (2 ^ d - 1)) := by
        push_cast; ring
    _ = 1 := hcast

/-- Powers of two modulo `2 ^ d - 1` are periodic with period `d`. -/
theorem two_pow_mod (d : ℕ) (a : ℕ) :
    (2 : ZMod (2 ^ d - 1)) ^ (a % d) = (2 : ZMod (2 ^ d - 1)) ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a d]
  rw [pow_add, pow_mul, two_pow_self d, one_pow, one_mul]

/-- `pow2` on a natural index is the honest power of two. -/
theorem pow2_natCast (k : ℕ) :
    pow2 ((k : ZMod d)) = (2 : ZMod (2 ^ d - 1)) ^ k := by
  unfold pow2
  rw [ZMod.val_natCast, two_pow_mod]

/-- `pow2` turns the cyclic index addition into multiplication. -/
theorem pow2_add [NeZero d] (x y : ZMod d) :
    pow2 (x + y) = pow2 x * pow2 y := by
  unfold pow2
  rw [ZMod.val_add, two_pow_mod, pow_add]

/-- The cyclic run `{t - 1, t, …, t - 1 + (ℓ - 1)}` of `ℓ` consecutive
indices: the negative support of a level-`ℓ` representation. -/
def runSet (t : ZMod d) (ℓ : ℕ) : Finset (ZMod d) :=
  (Finset.range ℓ).image (fun j : ℕ => t - 1 + (j : ZMod d))

theorem natCast_injOn_range {ℓ : ℕ} (hℓ : ℓ ≤ d) :
    Set.InjOn (fun j : ℕ => (j : ZMod d)) (Finset.range ℓ) := by
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have hab' : (a : ZMod d) = (b : ZMod d) := hab
  have ha' : ((a : ZMod d)).val = a := by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
  have hb' : ((b : ZMod d)).val = b := by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
  rw [← ha', ← hb', hab']

/-- The run has exactly `ℓ` elements as long as `ℓ ≤ d`. -/
theorem card_runSet (t : ZMod d) {ℓ : ℕ} (hℓ : ℓ ≤ d) :
    (runSet t ℓ).card = ℓ := by
  rw [runSet, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  exact natCast_injOn_range hℓ ha hb (by simpa using hab)

/-- The geometric sum over a run: `∑_{j<ℓ} 2^(t-1+j) = 2^(t-1) (2^ℓ - 1)`. -/
theorem sum_pow2_runSet [NeZero d] (t : ZMod d) {ℓ : ℕ} (hℓ : ℓ ≤ d) :
    ∑ x ∈ runSet t ℓ, pow2 x
      = pow2 (t - 1) * ((2 : ZMod (2 ^ d - 1)) ^ ℓ - 1) := by
  have hinj : Set.InjOn (fun j : ℕ => t - 1 + (j : ZMod d)) (Finset.range ℓ) := by
    intro a ha b hb hab
    exact natCast_injOn_range hℓ ha hb (by simpa using hab)
  rw [runSet, Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
  have hterm : ∀ j ∈ Finset.range ℓ,
      pow2 (t - 1 + (j : ZMod d)) = pow2 (t - 1) * (2 : ZMod (2 ^ d - 1)) ^ j := by
    intro j _
    rw [pow2_add, pow2_natCast]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  have hg := geom_sum_mul (2 : ZMod (2 ^ d - 1)) ℓ
  have h21 : (2 : ZMod (2 ^ d - 1)) - 1 = 1 := by norm_num
  rw [h21, mul_one] at hg
  exact hg

variable [NeZero d]

/-- The coordinate-sum of an integer vector on the cyclic index group. -/
def coeffSum (v : ZMod d → ℤ) : ℤ := ∑ x, v x

/-- The value `∑ v x • 2^x` of an integer vector, in `ZMod (2^d - 1)`. -/
def value (v : ZMod d → ℤ) : ZMod (2 ^ d - 1) := ∑ x, v x • pow2 x

/-- The level-`ℓ` representation of `2^(t-1)`:
`e_{t-1+ℓ} - ∑_{j<ℓ} e_{t-1+j}`. -/
def levelVec (t : ZMod d) (ℓ : ℕ) : ZMod d → ℤ := fun x =>
  (if x = t - 1 + (ℓ : ZMod d) then 1 else 0) - (if x ∈ runSet t ℓ then 1 else 0)

/-- A level-`ℓ` representation has coordinate sum `1 - ℓ`. -/
theorem coeffSum_levelVec (t : ZMod d) {ℓ : ℕ} (hℓ : ℓ ≤ d) :
    coeffSum (levelVec t ℓ) = 1 - (ℓ : ℤ) := by
  classical
  unfold coeffSum levelVec
  rw [Finset.sum_sub_distrib]
  congr 1
  · simp
  · rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, card_runSet t hℓ]
    simp

/-- A level-`ℓ` representation has value `2^(t-1)`, for every `ℓ ≤ d`: the
geometric sum of the negatives telescopes against the leading term. -/
theorem value_levelVec (t : ZMod d) {ℓ : ℕ} (hℓ : ℓ ≤ d) :
    value (levelVec t ℓ) = pow2 (t - 1) := by
  classical
  unfold value levelVec
  have hsplit : ∀ x : ZMod d,
      ((if x = t - 1 + (ℓ : ZMod d) then (1 : ℤ) else 0)
          - (if x ∈ runSet t ℓ then (1 : ℤ) else 0)) • pow2 x
        = (if x = t - 1 + (ℓ : ZMod d) then (1 : ℤ) else 0) • pow2 x
          - (if x ∈ runSet t ℓ then (1 : ℤ) else 0) • pow2 x := by
    intro x; rw [sub_smul]
  rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_sub_distrib]
  have hlead : ∑ x : ZMod d, (if x = t - 1 + (ℓ : ZMod d) then (1 : ℤ) else 0) • pow2 x
      = pow2 (t - 1 + (ℓ : ZMod d)) := by
    simp only [ite_smul, one_smul, zero_smul]
    simp
  have hrun : ∑ x : ZMod d, (if x ∈ runSet t ℓ then (1 : ℤ) else 0) • pow2 x
      = ∑ x ∈ runSet t ℓ, pow2 x := by
    simp only [ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hlead, hrun, sum_pow2_runSet t hℓ, pow2_add, pow2_natCast]
  ring

end StratumOne

end MinModulus
