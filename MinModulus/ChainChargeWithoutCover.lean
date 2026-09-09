import MinModulus.ChainFamilyProfile

/-! A single charged actual affine chain gives all original lower bounds,
with arbitrary endpoint and remaining coordinates. Maximal continuation
produces a cycle whose incoming tail has power bounded by the chain length.
The charge forces any cycle smaller than half into the existing exponential
deficit class, so below binary modulus the cycle must be half-sized.
No separate coverage premise is used. Unrestricted G1/G2/G3 remain open. -/

namespace MinModulus
open Finset

/-- A charged actual chain and its power-bounded incoming tail force
any below-half cycle into the existing exponential-deficit class. -/
theorem cycle_exponential_deficit_of_chain_charge
    {n p c : ℕ} (hp : 4 ≤ p) (hcp : c ≤ p) (hpn : p ≤ n)
    (htail : 2^(p-c) ≤ p) (hcharge : n*2^(n-p) ≤ 2^(p-3))
    (hdef : 2*c+2 ≤ n) : 3*2^(n-2*c) ≤ c := by
  have hn : 0 < n := by omega
  have hp3 : 8*2^(p-3)=2^p := by
    rw [show p=3+(p-3) by omega,pow_add]
    norm_num
  have hnp : 2^(n-p)*2^p=2^n := by rw [← pow_add,Nat.sub_add_cancel hpn]
  have hbig : 8*n*2^n=(8*2^p)*(n*2^(n-p)) := by rw [← hnp]; ring
  have hbound : 8*n*2^n ≤ (2^p)^2 := by
    calc
      _ = (8*2^p)*(n*2^(n-p)) := hbig
      _ ≤ (8*2^p)*2^(p-3) := Nat.mul_le_mul_left _ hcharge
      _ = 2^p*(8*2^(p-3)) := by ring
      _ = (2^p)^2 := by rw [hp3,pow_two]
  have hpowN : 2^n=2^(2*c)*2^(n-2*c) := by rw [← pow_add,Nat.add_sub_of_le (by omega : 2*c ≤ n)]
  have hpowP : (2^p)^2=2^(2*c)*(2^(p-c))^2 := by
    have hp' : 2^p=2^c*2^(p-c) := by rw [← pow_add,Nat.add_sub_of_le hcp]
    rw [hp',mul_pow,← pow_mul,Nat.mul_comm c 2]
  rw [hpowN,hpowP] at hbound
  have hcancel : 8*n*2^(n-2*c) ≤ (2^(p-c))^2 := by
    have hb : 0 < (2 : ℕ)^(2*c) := by positivity
    nlinarith
  have htail2 : (2^(p-c))^2 ≤ p^2 := Nat.pow_le_pow_left htail 2
  have hpN : p^2 ≤ n*p := by nlinarith
  have hsmall : 8*2^(n-2*c) ≤ p := by nlinarith
  have hK := two_mul_le_two_pow (p-c)
  have hpc : p ≤ 2*c := by omega
  omega

/-- A rejoining charged singleton family yields an actual half-sized
cycle below binary modulus. Smaller cycles violate the existing
all-modulus exponential-deficit bound. -/
theorem exists_half_sized_cycle_of_charged_singleton_rejoin
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b : ZMod N) (x : Fin 1 → ZMod N) (M : Fin 1 → ℕ) (V : Fin 1 → ℕ → Fin n)
    (hMV : ActualAffineChainFamily g b x M V) (hp : 4 ≤ M 0)
    (hcharge : n*2^(n-M 0) ≤ 2^(M 0-3)) (j : ℕ) (hj : j < M 0)
    (hjoin : g (V 0 j)=2 • g (V 0 (M 0-1))+b) :
    ∃ c : ℕ, 2 ≤ c ∧ n ≤ 2*c+1 ∧ ∃ C : Fin c ↪ Fin n,
      ∃ R : Equiv.Perm (Fin c), ∀ i, g (C (R i))=2 • g (C i)+b := by
  obtain ⟨c,hc,hcp,C,R,hC,hbudget⟩ := exists_cycle_with_joint_family_budget_of_rejoin
    g hg b x M V hMV 0 j hj hjoin
  simp only [Fin.sum_univ_one,Fintype.card_fin,one_mul] at hcp hbudget
  have hpn : M 0 ≤ n := by simpa only [Fin.sum_univ_one] using actual_affine_chain_family_length_le g b x M V hMV
  let K := M 0-c
  have hD : 2^K-1 ≤ K*2^K := by
    by_cases hK : K=0
    · simp [hK]
    · have hK1 : 1 ≤ K := by omega
      exact (Nat.sub_le _ _).trans (by simpa only [one_mul] using Nat.mul_le_mul_right (2^K) hK1)
  have htail : 2^(M 0-c) ≤ M 0 := by
    have h := hbudget K
    have hs := Nat.sub_add_cancel hD
    change 2^K ≤ M 0
    change 2^K*K < M 0+(K*2^K-(2^K-1)) at h
    have he : 2^K*K=K*2^K := Nat.mul_comm _ _
    omega
  have hK := two_mul_le_two_pow (M 0-c)
  have hpc : M 0 ≤ 2*c := by omega
  have hc2 : 2 ≤ c := by omega
  have hhalf : n ≤ 2*c+1 := by
    by_contra hh
    have hdef : 2*c+2 ≤ n := by omega
    have hlarge := cycle_exponential_deficit_of_chain_charge hp hcp hpn htail hcharge hdef
    have hcn : c ≤ n := by omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    cases k with
    | zero => omega
    | succ k =>
      obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd (k+1)) C
        (Fin.castAdd_injective c (k+1)) C.injective
      have hbound := binary_lower_bound_of_valid_affine_cycle_of_exponential_deficit
        (by omega : 2 ≤ c+(k+1)-2*c) hlarge (by omega : k+1=c+(c+(k+1)-2*c))
        g hg P b R (by simpa only [hP] using hC)
      omega
  exact ⟨c,hc2,hhalf,C,R,hC⟩

/-- Any actual chain paying the original single-arm continuation
charge has a half-sized cycle below binary modulus. No additional
coverage or logarithmic length assumption is needed. -/
theorem exists_half_sized_cycle_of_charged_affine_chain
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x : ZMod N) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hcharge : n*2^(n-m) ≤ 2^(m-3)) :
    ∃ c : ℕ, 2 ≤ c ∧ n ≤ 2*c+1 ∧ ∃ C : Fin c ↪ Fin n,
      ∃ R : Equiv.Perm (Fin c), ∀ i, g (C (R i))=2 • g (C i)+b := by
  classical
  let L : Fin 1 → ℕ := fun _ ↦ m
  let y : Fin 1 → ZMod N := fun _ ↦ x
  let v : Fin 1 → ℕ → Fin n := fun _ i ↦ if hi : i < m then e ⟨i,hi⟩ else e ⟨0,by omega⟩
  have hv : ActualAffineChainFamily g b y L v := by
    constructor
    · intro a i hi
      change i < m at hi
      simpa only [v,dif_pos hi,y] using hchain ⟨i,hi⟩
    · intro a c i j hi hj heq
      change i < m at hi
      change j < m at hj
      have ha : a=c := Subsingleton.elim _ _
      have hh : e ⟨i,hi⟩=e ⟨j,hj⟩ := by simpa only [v,dif_pos hi,dif_pos hj] using heq
      exact ⟨ha,congrArg Fin.val (e.injective hh)⟩
  obtain ⟨M,V,hMV,hgrow,hsize,j,hj,hjoin⟩ := exists_actual_affine_chain_family_internal_rejoin
    g hg hsub b y L v hv 0 hm (by simpa only [Fintype.card_fin,Fin.sum_univ_one,L,pow_one] using hcharge)
  have hp : 4 ≤ M 0 := by change m ≤ M 0 at hgrow; omega
  have hcharge' : n*2^(n-M 0) ≤ 2^(M 0-3) := by
    change m ≤ M 0 at hgrow
    calc
      _ ≤ n*2^(n-m) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega))
      _ ≤ 2^(m-3) := hcharge
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)
  exact exists_half_sized_cycle_of_charged_singleton_rejoin g hg hsub b y M V hMV hp hcharge' j hj hjoin

/-- Original global bound for any actual affine chain paying the
single-arm charge, with arbitrary endpoint and remaining coordinates. -/
theorem global_lower_bound_of_charged_affine_chain
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b x : ZMod N) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hcharge : n*2^(n-m) ≤ 2^(m-3)) : globalBound n ≤ N := by
  by_cases hsub : N < 2^n
  · obtain ⟨c,hc,hhalf,C,R,hR⟩ := exists_half_sized_cycle_of_charged_affine_chain hm g hg hsub b x e hchain hcharge
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact global_lower_bound_of_valid_half_sized_affine_doubling_cycle hc (by omega) g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Every original exact stratum for the same charged-chain class. -/
theorem stratum_lower_bound_of_charged_affine_chain
    {n m s d : ℕ} (hd : Odd d) (hm : 4 ≤ m)
    (g : Fin n → ZMod (2^s*d)) (hg : ValidTuple g) (b x : ZMod (2^s*d)) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hcharge : n*2^(n-m) ≤ 2^(m-3)) : stratumBound n s ≤ 2^s*d := by
  letI : NeZero (2^s*d) := ⟨(mul_pos (by positivity) hd.pos).ne'⟩
  by_cases hsub : 2^s*d < 2^n
  · obtain ⟨c,hc,hhalf,C,R,hR⟩ := exists_half_sized_cycle_of_charged_affine_chain hm g hg hsub b x e hchain hcharge
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact stratum_lower_bound_of_valid_half_sized_affine_doubling_cycle hc (by omega) hd g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Direct original G3 exclusion from the single-chain charge alone. -/
theorem not_validTuple_exceptional_of_charged_affine_chain
    {n m : ℕ} (hm : 4 ≤ m) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b x : ZMod (2*globalBound (n-1))) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hcharge : n*2^(n-m) ≤ 2^(m-3)) : ¬ ValidTuple g := by
  intro hg
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  have hb := global_lower_bound_of_charged_affine_chain hm g hg b x e hchain hcharge
  omega

/-- Explicit single-logarithm cutoff for an arbitrary-endpoint chain. -/
theorem global_lower_bound_of_single_log_affine_chain
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b x : ZMod N) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hlong : n+Nat.log 2 n+4 ≤ 2*m) : globalBound n ≤ N := by
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  exact global_lower_bound_of_charged_affine_chain hm g hg b x e hchain
    (long_chain_charge_of_logarithmic_length hm hmn hlong)

/-- The single-logarithm cutoff gives every original exact stratum. -/
theorem stratum_lower_bound_of_single_log_affine_chain
    {n m s d : ℕ} (hd : Odd d) (hm : 4 ≤ m)
    (g : Fin n → ZMod (2^s*d)) (hg : ValidTuple g) (b x : ZMod (2^s*d)) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hlong : n+Nat.log 2 n+4 ≤ 2*m) : stratumBound n s ≤ 2^s*d := by
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  exact stratum_lower_bound_of_charged_affine_chain hd hm g hg b x e hchain
    (long_chain_charge_of_logarithmic_length hm hmn hlong)

/-- The explicit cutoff also excludes original G3 tuples. -/
theorem not_validTuple_exceptional_of_single_log_affine_chain
    {n m : ℕ} (hm : 4 ≤ m) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b x : ZMod (2*globalBound (n-1))) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hlong : n+Nat.log 2 n+4 ≤ 2*m) : ¬ ValidTuple g := by
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  exact not_validTuple_exceptional_of_charged_affine_chain hm hnpow g b x e hchain
    (long_chain_charge_of_logarithmic_length hm hmn hlong)

end MinModulus
