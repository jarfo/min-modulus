import MinModulus.ChainChargeWithoutCover

/-! Exact truncated-profile charge alone gives every original lower bound.
The charge implies the selected width condition. Maximal continuation
preserves the actual error. Once the selected member rejoins internally,
all disjoint members have unsaturated sides; the error therefore equals
the selected single-chain charge. The single-chain theorem gives the
global, every exact-stratum and direct G3 bounds without separate width
or coverage assumptions. All unrestricted gates remain open. -/

namespace MinModulus
open Finset

/-- A saturated selected side and unsaturated remaining sides collapse
exactly to the single-chain charge, including empty members. -/
theorem chain_family_truncated_error_eq_single_charge
    {β : Type*} [Fintype β] [DecidableEq β] {n : ℕ}
    (L : β → ℕ) (a : β) (hwide : n ≤ 2^(L a))
    (hother : ∀ d, d ≠ a → 2^(L d) ≤ n) (hsize : (∑ d, L d) ≤ n) :
    chainFamilyTruncatedError n L=n*2^(n-L a) := by
  classical
  have hsplit := Finset.sum_erase_add Finset.univ L (Finset.mem_univ a)
  have hprod : (∏ d ∈ Finset.univ.erase a, min n (2^(L d)))=2^(∑ d ∈ Finset.univ.erase a, L d) := by
    calc
      _ = ∏ d ∈ Finset.univ.erase a, 2^(L d) := Finset.prod_congr rfl
        (fun d hd ↦ min_eq_right (hother d (Finset.mem_erase.mp hd).1))
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  unfold chainFamilyTruncatedError
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a),hprod,min_eq_left hwide]
  calc
    _ = n*(2^(∑ d ∈ Finset.univ.erase a, L d)*2^(n-∑ d, L d)) := by ring
    _ = _ := by rw [← pow_add]; congr 2; omega

/-- After an internal rejoin, every other actual member is short enough
that the family's exact error equals the selected single-chain charge. -/
theorem truncated_family_error_eq_single_charge_of_rejoin
    {β : Type*} [Fintype β] [DecidableEq β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (b : ZMod N) (x : β → ZMod N) (M : β → ℕ) (V : β → ℕ → Fin n)
    (hMV : ActualAffineChainFamily g b x M V) (a : β) (ha : 0 < M a)
    (hwide : n ≤ 2^(M a)) (i : ℕ) (hi : i < M a)
    (hjoin : g (V a i)=2 • g (V a (M a-1))+b) :
    chainFamilyTruncatedError n M=n*2^(n-M a) := by
  classical
  let E (d : β) : Fin (M d) ↪ Fin n :=
    ⟨fun j ↦ V d j.val,by intro j k h; exact Fin.ext (hMV.2 d d j.val k.val j.isLt k.isLt h).2⟩
  have hpow (d : β) : ∀ j : Fin (M d), g (E d j)+b=2^j.val • x d := fun j ↦ hMV.1 d j.val j.isLt
  obtain ⟨c,hc,_,C,R,hC⟩ := exists_cycle_of_affine_chain_internal_rejoin ha
    (fun j ↦ g (E a j)) (validTuple_embedding (E a) g hg) b (x a) (Function.Embedding.refl _) (hpow a)
    ⟨⟨i,hi⟩,hjoin⟩
  have hn : n ≠ 0 := by have := (E a ⟨0,ha⟩).isLt; omega
  apply chain_family_truncated_error_eq_single_charge M a hwide ?_
    (actual_affine_chain_family_length_le g b x M V hMV)
  intro d hda
  have hlog : M d ≤ Nat.log 2 n := by
    apply logarithmic_chain_disjoint_from_affine_cycle hc g hg b (x d) (C.trans (E a)) (E d) R
    · intro j k heq
      have had := (hMV.2 a d (C j).val k.val (C j).isLt k.isLt heq).1
      exact hda had.symm
    · exact hC
    · exact hpow d
  exact (Nat.le_log_iff_pow_le (by decide : 1 < (2 : ℕ)) hn).mp hlog

/-- Paying the exact profile charge already forces the selected side
to be wide enough for continuation. -/
theorem chain_family_width_of_truncated_charge
    {β : Type*} [Fintype β] {n : ℕ} (hn : 0 < n)
    (L : β → ℕ) (a : β) (ha : 4 ≤ L a)
    (hcharge : chainFamilyTruncatedError n L ≤ 2^(L a-3)) :
    2*n+1 ≤ 2^(L a) := by
  classical
  have hrest : 1 ≤ ∏ d ∈ Finset.univ.erase a, min n (2^(L d)) := by
    apply Finset.one_le_prod
    intro d _
    exact le_min (by omega) (Nat.one_le_two_pow)
  have hfactor : min n (2^(L a)) ≤ chainFamilyTruncatedError n L := by
    unfold chainFamilyTruncatedError
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
    calc
      _ = 1*min n (2^(L a))*1 := by simp
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ hrest) (Nat.one_le_two_pow)
  have hpow : 2^(L a)=8*2^(L a-3) := by
    rw [show L a=3+(L a-3) by omega,pow_add]
    norm_num
  have hbase : 0 < (2 : ℕ)^(L a-3) := by positivity
  have hwide : n ≤ 2^(L a) := by
    by_contra hh
    rw [min_eq_right (by omega : 2^(L a) ≤ n)] at hfactor
    nlinarith [hfactor.trans hcharge]
  rw [min_eq_left hwide] at hfactor
  have hncharge := hfactor.trans hcharge
  omega

/-- A charged truncated profile supplies an actual charged single chain
below binary modulus, without any additional coverage premise. -/
theorem exists_charged_chain_of_truncated_family
    {β : Type*} [Fintype β] [DecidableEq β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a : β) (ha : 4 ≤ L a)
    (hcharge : chainFamilyTruncatedError n L ≤ 2^(L a-3)) :
    ∃ p : ℕ, L a ≤ p ∧ ∃ e : Fin p ↪ Fin n,
      (∀ i, g (e i)+b=2^i.val • x a) ∧ n*2^(n-p) ≤ 2^(p-3) := by
  have hn : 0 < n := by have := (v a 0).isLt; omega
  have hwide := chain_family_width_of_truncated_charge hn L a ha hcharge
  obtain ⟨M,V,hMV,hgrow,_,herr,i,hi,hjoin⟩ :=
    exists_truncated_chain_family_internal_rejoin_controlled g hg hsub b x L v hv a ha hwide hcharge
  have hwide' : n ≤ 2^(M a) := (by omega : n ≤ 2^(L a)).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hgrow)
  have heq := truncated_family_error_eq_single_charge_of_rejoin g hg b x M V hMV a (by omega)
    hwide' i hi hjoin
  let E : Fin (M a) ↪ Fin n :=
    ⟨fun j ↦ V a j.val,by intro j k h; exact Fin.ext (hMV.2 a a j.val k.val j.isLt k.isLt h).2⟩
  refine ⟨M a,hgrow,E,(fun j ↦ hMV.1 a j.val j.isLt),?_⟩
  calc
    _ = chainFamilyTruncatedError n M := heq.symm
    _ ≤ chainFamilyTruncatedError n L := herr
    _ ≤ 2^(L a-3) := hcharge
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)

/-- Original global lower bound for a charged exact profile, without a coverage premise. -/
theorem global_lower_bound_of_truncated_family_without_cover
    {β : Type*} [Fintype β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : chainFamilyTruncatedError n L ≤ 2^(L a-3)) :
    globalBound n ≤ N := by
  classical
  by_cases hsub : N < 2^n
  · have hn : 0 < n := by have := (e ⟨a,⟨0,by omega⟩⟩).isLt; omega
    obtain ⟨v,hv⟩ := exists_actual_affine_chain_family_of_embedding hn g b x L e hchain
    obtain ⟨p,hp,E,hE,hch⟩ := exists_charged_chain_of_truncated_family g hg hsub b x L v hv a ha hcharge
    exact global_lower_bound_of_charged_affine_chain (by omega) g hg b (x a) E hE hch
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Original stratum lower bound for a charged exact profile, without a coverage premise. -/
theorem stratum_lower_bound_of_truncated_family_without_cover
    {β : Type*} [Fintype β] {n s d : ℕ} (hd : Odd d)
    (g : Fin n → ZMod (2^s*d)) (hg : ValidTuple g)
    (b : ZMod (2^s*d)) (x : β → ZMod (2^s*d)) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : chainFamilyTruncatedError n L ≤ 2^(L a-3)) :
    stratumBound n s ≤ 2^s*d := by
  classical
  letI : NeZero (2^s*d) := ⟨(mul_pos (by positivity) hd.pos).ne'⟩
  by_cases hsub : 2^s*d < 2^n
  · have hn : 0 < n := by have := (e ⟨a,⟨0,by omega⟩⟩).isLt; omega
    obtain ⟨v,hv⟩ := exists_actual_affine_chain_family_of_embedding hn g b x L e hchain
    obtain ⟨p,hp,E,hE,hch⟩ := exists_charged_chain_of_truncated_family g hg hsub b x L v hv a ha hcharge
    exact stratum_lower_bound_of_charged_affine_chain hd (by omega) g hg b (x a) E hE hch
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Original not validTuple exceptional for a charged exact profile, without a coverage premise. -/
theorem not_validTuple_exceptional_of_truncated_family_without_cover
    {β : Type*} [Fintype β] {n : ℕ} (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b : ZMod (2*globalBound (n-1))) (x : β → ZMod (2*globalBound (n-1))) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : chainFamilyTruncatedError n L ≤ 2^(L a-3)) :
    ¬ ValidTuple g := by
  intro hg
  have han : L a ≤ n := by
    have h := Fintype.card_le_of_injective (fun i : Fin (L a) ↦ e ⟨a,i⟩)
      (by intro i j h; have hh := e.injective h; cases hh; rfl)
    simpa only [Fintype.card_fin] using h
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  have h := global_lower_bound_of_truncated_family_without_cover g hg b x L e hchain a ha hcharge
  omega

end MinModulus
