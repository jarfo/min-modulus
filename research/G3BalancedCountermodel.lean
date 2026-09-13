import MinModulus.G3ExceptionalStructure
import MinModulus.UniqueSums
import MinModulus.Descent

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- Crossing a binary power-gap modulus adds all the high bits, so it
strictly increases the subset cardinality. -/
theorem binary_power_gap_wrap_increases_card
    {n s : ℕ} (hs : s < n) (S T : Finset ℕ)
    (_hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (hwrap : (∑ i ∈ T, 2^i) = (∑ i ∈ S, 2^i)+(2^n-2^s)) :
    S.card < T.card := by
  classical
  have hp : 2^s < (2:ℕ)^n := Nat.pow_lt_pow_right (by decide) hs
  have hTlt : (∑ i ∈ T, 2^i) < (2:ℕ)^n := by
    have hh := Finset.sum_le_sum_of_subset hT (f := fun i ↦ (2:ℕ)^i)
    rw [sum_two_pow] at hh
    have := Nat.one_le_two_pow (n := n)
    omega
  have hSlt : (∑ i ∈ S, 2^i) < (2:ℕ)^s := by omega
  have hSlow : S ⊆ Finset.range s := by
    intro i hi
    have hiw : (2:ℕ)^i ≤ ∑ j ∈ S, 2^j :=
      Finset.single_le_sum (fun j _ ↦ Nat.zero_le _) hi
    apply Finset.mem_range.mpr
    by_contra hn
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (show s ≤ i by omega)
    omega
  let H := Finset.range n \ Finset.range s
  have hHweight : (∑ i ∈ H, 2^i) = (2:ℕ)^n-2^s := by
    have hh := Finset.sum_sdiff (f := fun i ↦ (2:ℕ)^i)
      (Finset.range_subset_range.mpr hs.le)
    rw [sum_two_pow,sum_two_pow] at hh
    change (∑ i ∈ H, 2^i)+(2^s-1)=2^n-1 at hh
    have := Nat.one_le_two_pow (n := s)
    omega
  have hd : Disjoint S H := by
    apply Finset.disjoint_left.mpr
    intro i hi hh
    exact (Finset.mem_sdiff.mp hh).2 (hSlow hi)
  have he : T=S ∪ H := by
    apply Finset.geomSum_injective (by decide : 2 ≤ (2:ℕ))
    dsimp only
    rw [Finset.sum_union hd,hHweight]
    exact hwrap
  have hHcard : H.card=n-s := by
    simpa only [H,Finset.card_range] using
      Finset.card_sdiff_of_subset (Finset.range_subset_range.mpr hs.le)
  rw [he,Finset.card_union_of_disjoint hd,hHcard]
  omega

/-- Binary subset sums of a fixed rank remain distinct modulo every
power-gap modulus, including gaps too large for multiset validity. -/
theorem binary_same_rank_mod_power_gap_injective
    {n s : ℕ} (hs : s < n) (S T : Finset ℕ)
    (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (hcard : S.card=T.card)
    (he : (∑ i ∈ S, 2^i : ℕ) % (2^n-2^s) =
      (∑ i ∈ T, 2^i : ℕ) % (2^n-2^s)) : S=T := by
  have hp : 2^s < (2:ℕ)^n := Nat.pow_lt_pow_right (by decide) hs
  have hhalf : 2*2^s ≤ (2:ℕ)^n := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (show s+1 ≤ n by omega)
    simpa only [pow_succ',pow_one] using hh
  let N := (2:ℕ)^n-2^s
  have hN : 0 < N := by dsimp [N]; omega
  have hsum_lt (U : Finset ℕ) (hU : U ⊆ Finset.range n) :
      (∑ i ∈ U, 2^i) < 2*N := by
    have hh := Finset.sum_le_sum_of_subset hU (f := fun i ↦ (2:ℕ)^i)
    rw [sum_two_pow] at hh
    dsimp [N]
    omega
  have ha := hsum_lt S hS
  have hb := hsum_lt T hT
  have cases : (∑ i ∈ S, 2^i)=(∑ i ∈ T, 2^i) ∨
      (∑ i ∈ S, 2^i)+N=(∑ i ∈ T, 2^i) ∨
      (∑ i ∈ T, 2^i)+N=(∑ i ∈ S, 2^i) := by
    change (∑ i ∈ S, 2^i) % N = (∑ i ∈ T, 2^i) % N at he
    by_cases hSN : (∑ i ∈ S, 2^i) < N
    · rw [Nat.mod_eq_of_lt hSN] at he
      by_cases hTN : (∑ i ∈ T, 2^i) < N
      · rw [Nat.mod_eq_of_lt hTN] at he
        exact Or.inl he
      · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)] at he
        exact Or.inr (Or.inl (by omega))
    · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)] at he
      by_cases hTN : (∑ i ∈ T, 2^i) < N
      · rw [Nat.mod_eq_of_lt hTN] at he
        exact Or.inr (Or.inr (by omega))
      · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)] at he
        exact Or.inl (by omega)
  rcases cases with hh | hh | hh
  · exact Finset.geomSum_injective (by decide : 2 ≤ (2:ℕ)) hh
  · have hc := binary_power_gap_wrap_increases_card hs S T hS hT hh.symm
    omega
  · have hc := binary_power_gap_wrap_increases_card hs T S hT hS hh.symm
    omega

/-- Finite-coordinate version of the fixed-rank binary injectivity theorem. -/
theorem binary_tuple_same_rank_injective
    {n s : ℕ} (hs : s < n) (S T : Finset (Fin n)) (hcard : S.card=T.card)
    (he : (∑ i ∈ S, (2 : ZMod (2^n-2^s))^i.val) =
      ∑ i ∈ T, (2 : ZMod (2^n-2^s))^i.val) : S=T := by
  classical
  have himage (U : Finset (Fin n)) : U.image Fin.val ⊆ Finset.range n := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr j.isLt
  have hz : ((∑ i ∈ S, 2^i.val : ℕ) : ZMod (2^n-2^s)) =
      ((∑ i ∈ T, 2^i.val : ℕ) : ZMod (2^n-2^s)) := by
    push_cast
    exact he
  have hmod : (∑ i ∈ S, 2^i.val : ℕ) ≡ (∑ i ∈ T, 2^i.val : ℕ) [MOD 2^n-2^s] := by
    rwa [ZMod.natCast_eq_natCast_iff] at hz
  have hm := binary_same_rank_mod_power_gap_injective hs
    (S.image Fin.val) (T.image Fin.val) (himage S) (himage T)
    (by simpa only [Finset.card_image_of_injective _ Fin.val_injective] using hcard)
    (by simpa only [Nat.ModEq,Finset.sum_image,Fin.val_injective.injOn] using hmod)
  exact Finset.image_injective Fin.val_injective hm

/-- The same binary tuple is invalid when the removed power exceeds n:
split its low binary coins until exactly n coins represent the low endpoint. -/
theorem binary_tuple_not_valid_of_large_power_gap
    {n s : ℕ} (hs : s < n) (hn : n < 2^s) :
    ¬ ValidTuple (fun i : Fin n ↦ (2 : ZMod (2^n-2^s))^i.val) := by
  intro hg
  have hp : 2^s < (2:ℕ)^n := Nat.pow_lt_pow_right (by decide) hs
  obtain ⟨a,ha,haval,hasum⟩ := ones_rep s
  have hseed : ∃ k, val n k=2^s-1 ∧ dsum n k ≤ n := by
    exact ⟨a,(val_pad hs.le ha).trans haval,by rw [dsum_pad hs.le ha,hasum]; omega⟩
  obtain ⟨k,hkval,hksum⟩ := exists_dsum_eq hseed (by omega : n ≤ 2^s-1)
  have hc : ∑ i : Fin n, k i.val=n := by
    simpa only [dsum,Fin.sum_univ_eq_sum_range] using hksum
  have hv : (∑ i : Fin n, k i.val*2^i.val)=2^s-1 := by
    unfold val at hkval
    rw [← Fin.sum_univ_eq_sum_range] at hkval
    exact hkval
  have htotal : (∑ i : Fin n, (2:ℕ)^i.val)=2^n-1 := by
    rw [Fin.sum_univ_eq_sum_range,sum_two_pow]
  have hrel : (2:ℕ)^n-1=(2^s-1)+(2^n-2^s) := by
    have := Nat.one_le_two_pow (n := s)
    omega
  have hz : ((∑ i : Fin n, k i.val*2^i.val : ℕ) : ZMod (2^n-2^s)) =
      ((∑ i : Fin n, (2:ℕ)^i.val : ℕ) : ZMod (2^n-2^s)) := by
    rw [hv,htotal,hrel]
    simp
  have hgval : (∑ i : Fin n, k i.val • (2 : ZMod (2^n-2^s))^i.val)=
      ∑ i : Fin n, (2 : ZMod (2^n-2^s))^i.val := by
    push_cast at hz
    simpa only [nsmul_eq_mul] using hz
  have hone := hg (fun i ↦ k i.val) hc hgval
  have hvall : (∑ i : Fin n, k i.val*2^i.val)=2^n-1 := by
    simpa only [hone,one_mul] using htotal
  omega

/-- Fixed-rank subset injectivity excludes zero relations with all coefficients
in {-1,0,1}. This implication does not require multiset validity. -/
theorem unit_zero_isolation_of_same_rank_injective
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (hsep : ∀ S T : Finset (Fin n), S.card=T.card →
      (∑ i ∈ S, g i)=(∑ i ∈ T, g i) → S=T)
    (c : Fin n → ℤ) (hunit : ∀ i, -1 ≤ c i ∧ c i ≤ 1)
    (hsum : ∑ i, c i=0) (hweight : ∑ i, c i • g i=0) : c=0 := by
  classical
  let P := Finset.univ.filter (fun i ↦ c i=1)
  let M := Finset.univ.filter (fun i ↦ c i= -1)
  have hform : ∀ i, c i=(if i ∈ P then 1 else 0)-(if i ∈ M then 1 else 0) := by
    intro i
    have hh := hunit i
    simp only [P,M,Finset.mem_filter,Finset.mem_univ,true_and]
    split_ifs <;> omega
  have hsumform : (∑ i, c i)=(P.card : ℤ)-(M.card : ℤ) := by
    simp_rw [hform]
    simp only [Finset.sum_sub_distrib]
    simp
  have hcard : P.card=M.card := by omega
  have hweightform : (∑ i, c i • g i)=(∑ i ∈ P, g i)-(∑ i ∈ M, g i) := by
    simp_rw [hform]
    simp only [sub_smul,ite_smul,one_zsmul,zero_smul,Finset.sum_sub_distrib,
      Finset.sum_ite_mem,Finset.univ_inter]
  have hPM := hsep P M hcard (sub_eq_zero.mp (hweightform.symm.trans hweight))
  funext i
  have hh := hunit i
  have he : c i=1 ↔ c i= -1 := by
    have hm := Finset.ext_iff.mp hPM i
    simpa only [P,M,Finset.mem_filter,Finset.mem_univ,true_and] using hm
  simp only [Pi.zero_apply]
  omega

/-- In every G3 dimension the actual exceptional cyclic group contains a tuple
which is invalid, but has no nonzero balanced unit-coefficient zero relation.
Thus that weaker isolation property alone cannot prove the G3 obstruction. -/
theorem exceptional_balanced_isolation_countermodel
    (n : ℕ) (hn : 3 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n) :
    ∃ g : Fin n → ZMod (2*globalBound (n-1)), ¬ ValidTuple g ∧
      ∀ c : Fin n → ℤ, (∀ i, -1 ≤ c i ∧ c i ≤ 1) →
        (∑ i, c i)=0 → (∑ i, c i • g i)=0 → c=0 := by
  have hln := log_add_two_le n hn
  have hlog := log_pred_eq_log_of_not_pow n hn hnpow
  have hgap : 2*globalBound (n-1)=(2:ℕ)^n-2^(Nat.log 2 n+1) := by
    have hp : (2:ℕ)*2^(n-1)=2^n := by
      rw [← pow_succ']
      congr 1
      omega
    unfold globalBound
    rw [hlog,Nat.mul_sub,hp,← pow_succ']
  rw [hgap]
  let g : Fin n → ZMod (2^n-2^(Nat.log 2 n+1)) := fun i ↦ 2^i.val
  refine ⟨g,binary_tuple_not_valid_of_large_power_gap (by omega)
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n),?_⟩
  intro c hc hsum hweight
  exact unit_zero_isolation_of_same_rank_injective g
    (fun S T hcard he ↦ binary_tuple_same_rank_injective (by omega) S T hcard he)
    c hc hsum hweight

end MinModulus.Research
