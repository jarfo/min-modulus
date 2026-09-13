import research.G3BalancedKernel
import Mathlib.Data.Nat.Choose.Central

set_option autoImplicit false
namespace MinModulus.Research

/-- In every sufficiently large dimension, a middle layer on all but one
coordinate is larger than the Mersenne odd factor of the exceptional modulus. -/
theorem exceptional_odd_part_lt_deleted_middle_layer_from_nine (n : ℕ) (hn : 9 ≤ n) :
    2^(n-Nat.log 2 n-1)-1 < (n-1).choose ((n-1)/2) := by
  let k := (n-1)/2
  have hkn : 2*k+1=n ∨ 2*k+2=n := by dsimp [k]; omega
  have hk : 4 ≤ k := by dsimp [k]; omega
  have hcentral := Nat.four_pow_lt_mul_centralBinom k hk
  have hlog := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  have hLn := log_add_two_le n (by omega)
  have hexp : 2^Nat.log 2 n * 2^(n-Nat.log 2 n-1) = (2:ℕ)^(n-1) := by
    rw [← pow_add]
    congr 1
    omega
  have hLpos : 0 < (2:ℕ)^Nat.log 2 n := by positivity
  have hfour : (4:ℕ)^k = 2^(2*k) := by rw [show (4:ℕ)=2^2 by norm_num,← pow_mul]
  rcases hkn with hkn | hkn
  · have hhalf : (n-1)/2=k := rfl
    have hchoose : (n-1).choose ((n-1)/2) = Nat.centralBinom k := by
      rw [hhalf,Nat.centralBinom]
      congr 1
      omega
    have hkl : k ≤ 2^Nat.log 2 n := by
      rw [pow_succ] at hlog
      omega
    have hpow : (2:ℕ)^(n-1) < 2^Nat.log 2 n*Nat.centralBinom k := by
      calc
        (2:ℕ)^(n-1) = 4^k := by rw [hfour]; congr 1; omega
        _ < k*Nat.centralBinom k := hcentral
        _ ≤ 2^Nat.log 2 n*Nat.centralBinom k := Nat.mul_le_mul_right _ hkl
    rw [← hexp] at hpow
    have hh := (Nat.mul_lt_mul_left hLpos).mp hpow
    rw [hchoose]
    exact (Nat.sub_le _ _).trans_lt hh
  · have hhalf : (n-1)/2=k := rfl
    have hchoose : (n-1).choose ((n-1)/2) = (2*k+1).choose k := by
      rw [hhalf]
      congr 1
      omega
    have hrel : (k+1)*((2*k+1).choose k) = (2*k+1)*Nat.centralBinom k := by
      have hh := Nat.choose_mul_succ_eq (2*k) k
      rw [Nat.centralBinom]
      have he : 2*k+1-k=k+1 := by omega
      rw [he] at hh
      nlinarith
    have hkl : k+1 ≤ 2^Nat.log 2 n := by rw [pow_succ] at hlog; omega
    have hpow : (2:ℕ)^(n-1) < 2^Nat.log 2 n*((2*k+1).choose k) := by
      calc
        (2:ℕ)^(n-1) = 2*4^k := by rw [hfour,← pow_succ']; congr 1; omega
        _ < 2*(k*Nat.centralBinom k) := by omega
        _ ≤ (2*k+1)*Nat.centralBinom k := by nlinarith
        _ = (k+1)*((2*k+1).choose k) := hrel.symm
        _ ≤ 2^Nat.log 2 n*((2*k+1).choose k) := Nat.mul_le_mul_right _ hkl
    rw [← hexp] at hpow
    have hh := (Nat.mul_lt_mul_left hLpos).mp hpow
    rw [hchoose]
    exact (Nat.sub_le _ _).trans_lt hh


/-- The deleted middle layer exceeds the odd factor in every dimension at least three. -/
theorem exceptional_odd_part_lt_deleted_middle_layer (n : ℕ) (hn : 3 ≤ n) :
    2^(n-Nat.log 2 n-1)-1 < (n-1).choose ((n-1)/2) := by
  by_cases h9 : 9 ≤ n
  · exact exceptional_odd_part_lt_deleted_middle_layer_from_nine n h9
  · have h8 : n ≤ 8 := by omega
    interval_cases n <;> decide

open Finset

/-- A fixed-rank family inside a coordinate set collides if it exceeds the target group. -/
theorem exists_equal_rank_collision_in_set
    {n k : ℕ} {H : Type*} [AddCommMonoid H] [Fintype H]
    (g : Fin n → H) (A : Finset (Fin n))
    (hlarge : Fintype.card H < A.card.choose k) :
    ∃ S T : Finset (Fin n), S ≠ T ∧ S ⊆ A ∧ T ⊆ A ∧
      S.card = T.card ∧ (∑ i ∈ S, g i) = ∑ i ∈ T, g i := by
  classical
  let F := A.powersetCard k
  let v : {S : Finset (Fin n) // S ∈ F} → H := fun S ↦ ∑ i ∈ S.val, g i
  have hni : ¬ Function.Injective v := by
    intro hi
    have hh := Fintype.card_le_of_injective v hi
    have hcard : Fintype.card {S : Finset (Fin n) // S ∈ F} = A.card.choose k := by
      rw [Fintype.card_coe]
      exact Finset.card_powersetCard k A
    rw [hcard] at hh
    omega
  obtain ⟨S,T,he,hne⟩ := Function.not_injective_iff.mp hni
  have hS := Finset.mem_powersetCard.mp S.property
  have hT := Finset.mem_powersetCard.mp T.property
  exact ⟨S.val,T.val,fun he ↦ hne (Subtype.ext he),hS.1,hT.1,
    hS.2.trans hT.2.symm,he⟩

/-- A large rank after deleting e forces a fully light kernel witness vanishing at e. -/
theorem exists_reversible_kernel_witness_avoiding_of_large_rank
    {n k : ℕ} {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype H]
    (f : G →+ H) (g : Fin n → G) (hg : ValidTuple g) (e : Fin n)
    (hlarge : Fintype.card H < (n-1).choose k) :
    ∃ h : G, ∃ c : Fin n → ℤ, h ≠ 0 ∧ f h = 0 ∧
      Witness g h c ∧ Witness g (-h) (-c) ∧ c e = 0 ∧
      (∀ i, -1 ≤ c i ∧ c i ≤ 1) := by
  classical
  let A : Finset (Fin n) := Finset.univ.erase e
  have hA : A.card=n-1 := by simp [A]
  obtain ⟨S,T,hne,hS,hT,hcard,hvalue⟩ := exists_equal_rank_collision_in_set
    (k := k) (fun i ↦ f (g i)) A (by rwa [hA])
  let c : Fin n → ℤ := fun i ↦ (if i ∈ S then 1 else 0)-(if i ∈ T then 1 else 0)
  have hcne : c ≠ 0 := by
    intro hc
    apply hne
    ext i
    have hi := congrFun hc i
    simp only [c,Pi.zero_apply] at hi
    by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;> simp_all
  have hfloor : ∀ i, -1 ≤ c i := by
    intro i
    dsimp [c]
    split_ifs <;> omega
  have hupper : ∀ i, c i ≤ 1 := by
    intro i
    dsimp [c]
    split_ifs <;> omega
  have hsum : ∑ i, c i = 0 := by simp [c,Finset.sum_sub_distrib,hcard]
  let h := ∑ i, c i • g i
  have hw : Witness g h c := ⟨hcne,hfloor,hsum,rfl⟩
  have hnz : h ≠ 0 := by
    intro hz
    exact (validTuple_iff_no_zero_witness g).mp hg c (hz ▸ hw)
  have hker : f h = 0 := by
    have hweight : h = (∑ i ∈ S, g i)-∑ i ∈ T, g i := by
      simp only [h,c,sub_smul,ite_smul,one_zsmul,zero_smul,
        Finset.sum_sub_distrib,Finset.sum_ite_mem,Finset.univ_inter]
    simp only [hweight,map_sub,map_sum,hvalue,sub_self]
  have heS : e ∉ S := fun hs ↦ Finset.notMem_erase e Finset.univ (hS hs)
  have heT : e ∉ T := fun ht ↦ Finset.notMem_erase e Finset.univ (hT ht)
  exact ⟨h,c,hnz,hker,hw,witness_neg_of_unit_coefficients g hw hupper,
    by simp [c,heS,heT],fun i ↦ ⟨hfloor i,hupper i⟩⟩

/-- No one coordinate meets all reversible odd-kernel witnesses of a hypothetical
exceptional tuple of length at least three. Targets may depend on the avoided coordinate. -/
theorem exists_exceptional_reversible_kernel_witness_avoiding
    (n : ℕ) (hn : 3 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1))) (hg : ValidTuple g) (e : Fin n) :
    ∃ h : ZMod (2*globalBound (n-1)), ∃ c : Fin n → ℤ,
      h ≠ 0 ∧
      ZMod.castHom (odd_part_dvd_exceptional n (by omega) hnpow)
        (ZMod (2^(n-Nat.log 2 n-1)-1)) h = 0 ∧
      Witness g h c ∧ Witness g (-h) (-c) ∧ c e = 0 ∧
      (∀ i, -1 ≤ c i ∧ c i ≤ 1) := by
  have hexp := one_le_mersenne_exponent n (by omega)
  have hqpos : 0 < 2^(n-Nat.log 2 n-1)-1 := by
    have hh : (2:ℕ)^1 ≤ 2^(n-Nat.log 2 n-1) := Nat.pow_le_pow_right (by norm_num) hexp
    norm_num only [pow_one] at hh
    omega
  let : NeZero (2^(n-Nat.log 2 n-1)-1) := ⟨hqpos.ne'⟩
  let f := (ZMod.castHom (odd_part_dvd_exceptional n (by omega) hnpow)
    (ZMod (2^(n-Nat.log 2 n-1)-1))).toAddMonoidHom
  exact exists_reversible_kernel_witness_avoiding_of_large_rank
    (k := (n-1)/2) f g hg e
    (by simpa only [ZMod.card] using exceptional_odd_part_lt_deleted_middle_layer n hn)

end MinModulus.Research
