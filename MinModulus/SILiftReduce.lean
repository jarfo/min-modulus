import MinModulus.SILiftDigit
import MinModulus.RLiftBits

/-!
# The SI-lift reduction

The parent is the super-increasing child `SI_m` together with one extra
coordinate `e`, at the stratum modulus `2 ^ (m+1) - 2 ^ s`.  A coin family
with exactly `m + 1` coins on exponents `0 .. m - 1` is precisely a rival
that omits the extra, so `si_digit_cover` forces `e` to the top
super-increasing coordinate.
-/

namespace MinModulus

open Finset

/-- The SI parent: the super-increasing child `SI_m` plus an extra. -/
def siParent (m e : ℕ) : Fin (m + 1) → ℕ :=
  Fin.snoc (fun i : Fin m => 2 ^ i.val - 1) e

@[simp] lemma siParent_castSucc (m e : ℕ) (i : Fin m) :
    siParent m e (Fin.castSucc i) = 2 ^ i.val - 1 := by
  rw [siParent, Fin.snoc_castSucc]

@[simp] lemma siParent_last (m e : ℕ) : siParent m e (Fin.last m) = e := by
  rw [siParent, Fin.snoc_last]

lemma val_succ (m : ℕ) (k : ℕ → ℕ) :
    val (m + 1) k = val m k + k m * 2 ^ m := by
  unfold val; rw [Finset.sum_range_succ]

lemma dsum_succ (m : ℕ) (k : ℕ → ℕ) :
    dsum (m + 1) k = dsum m k + k m := by
  unfold dsum; rw [Finset.sum_range_succ]

lemma si_dsum_le_val (m : ℕ) (k : ℕ → ℕ) : dsum m k ≤ val m k := by
  unfold val dsum
  refine Finset.sum_le_sum ?_
  intro i _
  have : (1 : ℕ) ≤ 2 ^ i := Nat.one_le_pow _ _ (by norm_num)
  exact Nat.le_mul_of_pos_right _ (by omega)

/-- `∑_{i<m} k i * (2^i - 1) = val m k - dsum m k`. -/
lemma sum_mul_si (m : ℕ) (k : ℕ → ℕ) :
    ∑ i ∈ range m, k i * (2 ^ i - 1) = val m k - dsum m k := by
  induction m with
  | zero => simp [val, dsum]
  | succ m ih =>
    have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have hmono := si_dsum_le_val m k
    have hk : k m * (2 ^ m - 1) = k m * 2 ^ m - k m := by
      rw [Nat.mul_sub, Nat.mul_one]
    have hkm : k m ≤ k m * 2 ^ m := Nat.le_mul_of_pos_right _ (by omega)
    rw [Finset.sum_range_succ, ih, val_succ, dsum_succ]
    omega

/-- `∑_{i<m} (2^i - 1) = 2^m - 1 - m`. -/
lemma sum_si (m : ℕ) : ∑ i ∈ range m, (2 ^ i - 1) = 2 ^ m - 1 - m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have hm : m < 2 ^ m := Nat.lt_two_pow_self
    have hpow : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [Finset.sum_range_succ, ih]
    omega

/-- **The SI-lift reduction, unlifted child.**  If the super-increasing
child together with an extra `e` is a valid tuple at the stratum modulus,
then `e` is forced: `e + 2^m ≡ 2^s - 1`, i.e. `e ≡ 2^m - 1`. -/
theorem si_extra_eq_of_valid {m s e : ℕ} (hm : 4 ≤ m) (hs : 2 ≤ s)
    (hsn : 2 ^ s ≤ m + 1)
    (hv : ValidTuple (fun i => ((siParent m e i : ℕ) :
        ZMod (2 ^ (m + 1) - 2 ^ s)))) :
    (e + 2 ^ m) % (2 ^ (m + 1) - 2 ^ s) = 2 ^ s - 1 := by
  set NP := 2 ^ (m + 1) - 2 ^ s with hNP
  have hpow : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have hmlt : m < 2 ^ m := Nat.lt_two_pow_self
  have hsm : (2 : ℕ) ^ s ≤ 2 ^ m := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    by_contra hc
    have h2 : (2 : ℕ) ^ (m + 1) ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hNPpos : 0 < NP := by omega
  by_contra hne
  obtain ⟨k, hd, hvv⟩ := si_digit_cover (n := m + 1) (s := s)
    (r := (e + 2 ^ m) % NP) (by omega) hs (by omega)
    (Nat.mod_lt _ hNPpos) hne
  rw [show m + 1 - 1 = m from rfl] at hd hvv
  have hdv : m + 1 ≤ val m k := by
    have := si_dsum_le_val m k; omega
  -- the multiplicity vector: `k` on the child, nothing on the extra
  set K : Fin (m + 1) → ℕ := Fin.snoc (fun i : Fin m => k i.val) 0 with hKdef
  have hKsum : ∑ i, K i = m + 1 := by
    rw [hKdef, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, add_zero]
    rw [Fin.sum_univ_eq_sum_range (fun i => k i) m]
    exact hd
  have hKval : ∑ i, K i • ((siParent m e i : ℕ) : ZMod NP)
      = ∑ i, ((siParent m e i : ℕ) : ZMod NP) := by
    rw [hKdef, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, siParent_castSucc,
      siParent_last, zero_smul, add_zero]
    rw [Fin.sum_univ_eq_sum_range
        (fun i => k i • ((2 ^ i - 1 : ℕ) : ZMod NP)) m,
      Fin.sum_univ_eq_sum_range (fun i => ((2 ^ i - 1 : ℕ) : ZMod NP)) m]
    have hL : ∑ i ∈ range m, k i • ((2 ^ i - 1 : ℕ) : ZMod NP)
        = ((∑ i ∈ range m, k i * (2 ^ i - 1) : ℕ) : ZMod NP) := by
      push_cast
      exact Finset.sum_congr rfl (fun i _ => by rw [nsmul_eq_mul])
    have hR : ∑ i ∈ range m, ((2 ^ i - 1 : ℕ) : ZMod NP)
        = ((∑ i ∈ range m, (2 ^ i - 1) : ℕ) : ZMod NP) := by push_cast; ring
    rw [hL, hR, sum_mul_si, sum_si, hd]
    have hcast : ((val m k : ℕ) : ZMod NP) = ((e + 2 ^ m : ℕ) : ZMod NP) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hvv
    rw [Nat.cast_sub hdv, Nat.cast_sub (by omega : m ≤ 2 ^ m - 1),
      Nat.cast_sub h1, hcast]
    push_cast
    ring
  have hone := hv K hKsum hKval (Fin.last m)
  rw [hKdef] at hone
  simp only [Fin.snoc_last] at hone
  exact absurd hone (by norm_num)

/-- **The unlifted SI child forces the top coordinate.**  If the
super-increasing child `SI_m` together with an extra `e` is valid at the
stratum modulus `2 ^ (m+1) - 2 ^ s`, then `e = 2 ^ m - 1`: the tuple is
exactly `SI_(m+1)`. -/
theorem si_extra_eq_top_of_valid {m s e : ℕ} (hm : 4 ≤ m) (hs : 2 ≤ s)
    (hsn : 2 ^ s ≤ m + 1) (he : e < 2 ^ (m + 1) - 2 ^ s)
    (hv : ValidTuple (fun i => ((siParent m e i : ℕ) :
        ZMod (2 ^ (m + 1) - 2 ^ s)))) :
    e = 2 ^ m - 1 := by
  have hmod := si_extra_eq_of_valid hm hs hsn hv
  have hpow : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have hmlt : m < 2 ^ m := Nat.lt_two_pow_self
  have h2s : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_pow _ _ (by norm_num)
  have hsm : (2 : ℕ) ^ s ≤ 2 ^ m := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    by_contra hc
    have h2 : (2 : ℕ) ^ (m + 1) ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set NP := 2 ^ (m + 1) - 2 ^ s with hNP
  have hNPpos : 0 < NP := by omega
  have hlt : e + 2 ^ m < 2 * NP := by omega
  obtain ⟨q, hq⟩ : ∃ q, e + 2 ^ m = NP * q + (2 ^ s - 1) :=
    ⟨(e + 2 ^ m) / NP, by rw [← hmod]; exact (Nat.div_add_mod _ _).symm⟩
  have hq1 : q ≤ 1 := by
    by_contra hc
    have h2 : NP * 2 ≤ NP * q := Nat.mul_le_mul_left _ (by omega)
    omega
  have hNPval : NP = 2 * 2 ^ m - 2 ^ s := by omega
  have hq01 : q = 0 ∨ q = 1 := by omega
  rcases hq01 with rfl | rfl
  · rw [Nat.mul_zero] at hq; omega
  · rw [Nat.mul_one] at hq; omega

end MinModulus
