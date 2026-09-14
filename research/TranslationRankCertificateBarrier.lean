import research.NonuniformTranslationFractional
import Mathlib.Data.Nat.Choose.Central

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- If a rank can spend the whole fractional budget, every certificate
objective pays at least that rank's full weighted capacity. -/
theorem rank_certificate_objective_ge_single_rank
    (J : Finset ℕ) (r : ℕ) (hr : r ∈ J)
    (B C : ℕ → ℕ) (hB : 0<B r) (hC : B r≤C r)
    (α : ℚ) (β : ℕ → ℚ) (hβ : ∀ j ∈ J, 0≤β j)
    (w : ℚ) (hw : w≤α/(B r:ℚ)+β r) :
    (B r:ℚ)*w ≤ α+∑ j ∈ J, (C j:ℚ)*β j := by
  have hBr : (B r:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hB
  have hmul := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg (B r) : (0:ℚ)≤B r)
  have he : (B r:ℚ)*(α/(B r:ℚ)+β r)=α+(B r:ℚ)*β r := by
    field_simp [hBr]
  rw [he] at hmul
  have hcap : (B r:ℚ)*β r ≤ (C r:ℚ)*β r :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hC) (hβ r hr)
  have hterm : (C r:ℚ)*β r ≤ ∑ j ∈ J, (C j:ℚ)*β j :=
    Finset.single_le_sum (fun j hj ↦ mul_nonneg (Nat.cast_nonneg _) (hβ j hj)) hr
  linarith

/-- Two central-binomial steps increase by at most a factor sixteen. -/
theorem central_choose_le_sixteen_two_steps (m : ℕ) :
    (2*(m+2)).choose (m+2) ≤ 16*(2*m).choose m := by
  have hstep (r : ℕ) : Nat.centralBinom (r+1) ≤ 4*Nat.centralBinom r := by
    have he := Nat.succ_mul_centralBinom_succ r
    have hh : (r+1)*Nat.centralBinom (r+1) ≤ (r+1)*(4*Nat.centralBinom r) := by
      rw [he]
      nlinarith
    exact Nat.le_of_mul_le_mul_left hh (by omega)
  have h1 := hstep m
  have h2 := hstep (m+1)
  change Nat.centralBinom (m+2) ≤ 16*Nat.centralBinom m
  have hm : m+1+1=m+2 := by omega
  rw [hm] at h2
  omega

/-- In even support size at least six, the rank-two capacity is six.
Any certificate allowing rank two must pay its corresponding weight.
This is a statement about the relaxation, not an actual tuple. -/
theorem rank_two_translation_certificate_lower_bound
    (k : ℕ) (hk : 3≤k) (J : Finset ℕ) (hJ : 2 ∈ J)
    (α : ℚ) (β : ℕ → ℚ) (hβ : ∀ j ∈ J, 0≤β j)
    (hw : ((2*k-4).choose (k-2):ℚ) ≤ α/6+β 2) :
    6*((2*k-4).choose (k-2):ℚ) ≤ α+
      ∑ j ∈ J, (min ((2*j).choose j) ((2*k).choose (2*j)):ℚ)*β j := by
  have hcap : 6≤(2*k).choose 4 := by
    have hh := Nat.choose_le_choose 4 (show 6≤2*k by omega)
    rw [show Nat.choose 6 4=15 by decide] at hh
    omega
  have hh := rank_certificate_objective_ge_single_rank J 2 hJ
    (fun j ↦ (2*j).choose j)
    (fun j ↦ min ((2*j).choose j) ((2*k).choose (2*j)))
    (by decide)
    (by change 6 ≤ min 6 ((2*k).choose 4); exact le_min (le_refl _) hcap) α β hβ
    ((2*k-4).choose (k-2):ℚ) (by change _≤α/6+β 2; exact hw)
  simpa only [show (2*2).choose 2=6 by decide,Nat.cast_ofNat,Nat.cast_min] using hh

/-- The rank-two relaxation floor is at least three eighths of the
central squarefree layer, uniformly in every k>=3. -/
theorem rank_two_translation_certificate_central_fraction_lower_bound
    (k : ℕ) (hk : 3≤k) (J : Finset ℕ) (hJ : 2 ∈ J)
    (α : ℚ) (β : ℕ → ℚ) (hβ : ∀ j ∈ J, 0≤β j)
    (hw : ((2*k-4).choose (k-2):ℚ) ≤ α/6+β 2) :
    3*((2*k).choose k:ℚ) ≤ 8*(α+
      ∑ j ∈ J, (min ((2*j).choose j) ((2*k).choose (2*j)):ℚ)*β j) := by
  have hlo := rank_two_translation_certificate_lower_bound k hk J hJ α β hβ hw
  have hbin := central_choose_le_sixteen_two_steps (k-2)
  have hk' : k-2+2=k := by omega
  have hn' : 2*(k-2)=2*k-4 := by omega
  rw [hk',hn'] at hbin
  have hbinQ : ((2*k).choose k:ℚ) ≤ 16*((2*k-4).choose (k-2):ℚ) := by
    exact_mod_cast hbin
  linarith

end MinModulus.Research
