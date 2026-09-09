import MinModulus.ChainProfileGates

/-! A rejoining actual chain tolerates twice the original error charge:
n*2^(n-p) <= 2^(p-2). The sharper tail arithmetic still forces a
half-sized cycle below binary modulus, yielding the original global,
every exact-stratum and direct G3 bounds. The actual internal rejoin is
an explicit premise. Unrestricted conjecture gates remain open. -/

namespace MinModulus
open Finset

/-- A rejoining actual chain tolerates twice the original scalar error
allowance to force an actual half-sized cycle below binary modulus. -/
theorem exists_half_sized_cycle_of_rejoining_chain_with_double_charge
    {n p N : ℕ} [NeZero N] (hp : 4 ≤ p)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x : ZMod N) (e : Fin p ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hjoin : ∃ i, g (e i)=2 • g (e ⟨p-1,by omega⟩)+b)
    (hcharge : n*2^(n-p) ≤ 2^(p-2)) :
    ∃ c : ℕ, 2 ≤ c ∧ n ≤ 2*c+1 ∧ ∃ C : Fin c ↪ Fin n,
      ∃ R : Equiv.Perm (Fin c), ∀ i, g (C (R i))=2 • g (C i)+b := by
  obtain ⟨c,hc,ht,C,R,hC⟩ := exists_cycle_of_affine_chain_internal_rejoin (by omega : 0 < p)
    (fun j ↦ g (e j)) (validTuple_embedding e g hg) b x (Function.Embedding.refl _) hchain hjoin
  have hcp : c ≤ p := by simpa using Fintype.card_le_of_injective _ C.injective
  have hpn : p ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  have htail : 2^(p-c) ≤ p :=
    (Nat.le_log_iff_pow_le (by decide : 1 < (2 : ℕ)) (by omega : p ≠ 0)).mp (by omega)
  have hK := two_mul_le_two_pow (p-c)
  have hc2 : 2 ≤ c := by omega
  let F : Fin c ↪ Fin n := C.trans e
  have hF : ∀ i, g (F (R i))=2 • g (F i)+b := hC
  have hhalf : n ≤ 2*c+1 := by
    by_contra hh
    have hdef : 2*c+2 ≤ n := by omega
    have hlarge := cycle_exponential_deficit_of_doubled_chain_charge hp hcp hpn htail hcharge hdef
    have hcn : c ≤ n := by omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    cases k with
    | zero => omega
    | succ k =>
      obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd (k+1)) F
        (Fin.castAdd_injective c (k+1)) F.injective
      have hbound := binary_lower_bound_of_valid_affine_cycle_of_exponential_deficit
        (by omega : 2 ≤ c+(k+1)-2*c) hlarge (by omega : k+1=c+(c+(k+1)-2*c))
        g hg P b R (by simpa only [hP] using hF)
      omega
  exact ⟨c,hc2,hhalf,F,R,hF⟩

/-- Original global lower bound for a rejoining chain with doubled error allowance. -/
theorem global_lower_bound_of_rejoining_chain_with_double_charge
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b x : ZMod N) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hjoin : ∃ i, g (e i)=2 • g (e ⟨m-1,by omega⟩)+b)
    (hcharge : n*2^(n-m) ≤ 2^(m-2)) : globalBound n ≤ N := by
  by_cases hsub : N < 2^n
  · obtain ⟨c,hc,hhalf,C,R,hR⟩ := exists_half_sized_cycle_of_rejoining_chain_with_double_charge hm g hg hsub b x e hchain hjoin hcharge
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact global_lower_bound_of_valid_half_sized_affine_doubling_cycle hc (by omega) g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Original stratum lower bound for a rejoining chain with doubled error allowance. -/
theorem stratum_lower_bound_of_rejoining_chain_with_double_charge
    {n m s d : ℕ} (hd : Odd d) (hm : 4 ≤ m)
    (g : Fin n → ZMod (2^s*d)) (hg : ValidTuple g) (b x : ZMod (2^s*d)) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hjoin : ∃ i, g (e i)=2 • g (e ⟨m-1,by omega⟩)+b)
    (hcharge : n*2^(n-m) ≤ 2^(m-2)) : stratumBound n s ≤ 2^s*d := by
  letI : NeZero (2^s*d) := ⟨(mul_pos (by positivity) hd.pos).ne'⟩
  by_cases hsub : 2^s*d < 2^n
  · obtain ⟨c,hc,hhalf,C,R,hR⟩ := exists_half_sized_cycle_of_rejoining_chain_with_double_charge hm g hg hsub b x e hchain hjoin hcharge
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact stratum_lower_bound_of_valid_half_sized_affine_doubling_cycle hc (by omega) hd g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Original not validTuple exceptional for a rejoining chain with doubled error allowance. -/
theorem not_validTuple_exceptional_of_rejoining_chain_with_double_charge
    {n m : ℕ} (hm : 4 ≤ m) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b x : ZMod (2*globalBound (n-1))) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hjoin : ∃ i, g (e i)=2 • g (e ⟨m-1,by omega⟩)+b)
    (hcharge : n*2^(n-m) ≤ 2^(m-2)) : ¬ ValidTuple g := by
  intro hg
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  have hb := global_lower_bound_of_rejoining_chain_with_double_charge hm g hg b x e hchain hjoin hcharge
  omega

end MinModulus
