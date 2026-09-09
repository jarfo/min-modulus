import MinModulus.FamilyAggregateCycle

/-! The exact truncated corner error is preserved through maximal
continuation: the wide designated arm stays saturated, other members
only shorten, and total coverage never decreases. Empty members change
neither the product nor coverage. Combined with collective cycle growth,
this yields original global, every exact-stratum and G3 bounds for
actual embedded families beyond the full-factor-per-member charge.
All endpoints and unselected coordinates are arbitrary. Unrestricted
G1/G2/G3 remain open. -/

namespace MinModulus
open Finset
open scoped Classical

/-- The actual rectangular corner error of a selected partial family,
including the full cube on its unselected coordinates. -/
def chainFamilyTruncatedError {β : Type*} [Fintype β] (n : ℕ) (L : β → ℕ) : ℕ :=
  (∏ i, min n (2^(L i)))*2^(n-∑ i, L i)

/-- Once the designated arm's corner side is saturated, extending it
and shortening other members can only improve the actual error.
Uncovered coordinates decrease as total coverage grows. -/
theorem chain_family_truncated_error_mono
    {β : Type*} [Fintype β] {n : ℕ} (L M : β → ℕ) (a : β)
    (hwide : n ≤ 2^(L a)) (ha : L a ≤ M a)
    (hother : ∀ d, d ≠ a → M d ≤ L d) (hcover : (∑ d, L d) ≤ (∑ d, M d)) :
    chainFamilyTruncatedError n M ≤ chainFamilyTruncatedError n L := by
  classical
  have hprod : (∏ i, min n (2^(M i))) ≤ ∏ i, min n (2^(L i)) := by
    apply Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
    intro d _
    by_cases hda : d=a
    · subst d
      have hM : n ≤ 2^(M a) := hwide.trans (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) ha)
      rw [min_eq_left hM,min_eq_left hwide]
    · exact min_le_min_left n (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (hother d hda))
  exact Nat.mul_le_mul hprod (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega))

/-- The sharper actual error still forces continuation when empty
members are present: removing them changes neither coverage nor product. -/
theorem exists_target_of_truncated_family_below_binary
    {β : Type*} [Fintype β] {n N : ℕ} [NeZero N] (hn : 0 < n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a : β) (ha : 4 ≤ L a)
    (hwide : 2*n+1 ≤ 2^(L a))
    (hcharge : chainFamilyTruncatedError n L ≤ 2^(L a-3)) :
    ∃ w, g w=2 • g (v a (L a-1))+b := by
  classical
  let B := {i : β // 0 < L i}
  let M : B → ℕ := fun i ↦ L i.val
  let E : (Σ i, Fin (M i)) → Fin n := fun i ↦ v i.1.val i.2.val
  have hE : Function.Injective E := by
    rintro ⟨a,i⟩ ⟨c,j⟩ h
    obtain ⟨hac,hij⟩ := hv.2 a.val c.val i.val j.val i.isLt j.isLt h
    have hac' : a=c := Subtype.ext hac
    subst c
    have hi : i=j := Fin.ext hij
    subst j
    rfl
  have hsum : (∑ i : B, M i)=∑ i : β, L i := by
    have h := Fintype.sum_subtype_add_sum_subtype (fun i ↦ 0 < L i) L
    have hz : (∑ i : {i : β // ¬ 0 < L i}, L i.val)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      have := i.property
      omega
    rw [hz,add_zero] at h
    exact h
  have hprod : (∏ i : B, min n (2^(M i)))=∏ i : β, min n (2^(L i)) := by
    have h := Fintype.prod_subtype_mul_prod_subtype (fun i ↦ 0 < L i) (fun i ↦ min n (2^(L i)))
    have hz : (∏ i : {i : β // ¬ 0 < L i}, min n (2^(L i.val)))=1 := by
      apply Finset.prod_eq_one
      intro i _
      have hi : L i.val=0 := by have := i.property; omega
      simp only [hi,pow_zero,min_eq_right (by omega : 1 ≤ n)]
    rw [hz,mul_one] at h
    exact h
  have hch : (∏ i : B, min n (2^(M i)))*2^(n-∑ i : B, M i) ≤ 2^(L a-3) := by
    rw [hsum,hprod]
    exact hcharge
  by_contra hnone
  have hbound := binary_card_bound_of_partial_genuine_chain_forest hn M (fun i ↦ i.property)
    g hg b (fun i : B ↦ x i.val) ⟨E,hE⟩ (fun i j ↦ hv.1 i.val j.val j.isLt)
    ⟨a,by omega⟩ ha hwide hch (by intro w hw; exact hnone ⟨w,hw⟩)
  simp only [ZMod.card] at hbound
  omega

/-- The actual truncated product is retained throughout maximal
continuation. It never increases under controlled extension or splicing. -/
theorem exists_truncated_chain_family_internal_rejoin_controlled
    {β : Type*} [Fintype β] [DecidableEq β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a : β) (ha : 4 ≤ L a)
    (hwide : 2*n+1 ≤ 2^(L a))
    (hcharge : chainFamilyTruncatedError n L ≤ 2^(L a-3)) :
    ∃ M : β → ℕ, ∃ V : β → ℕ → Fin n,
      ActualAffineChainFamily g b x M V ∧ L a ≤ M a ∧ (∑ c, L c) ≤ (∑ c, M c) ∧
        chainFamilyTruncatedError n M ≤ chainFamilyTruncatedError n L ∧
        ∃ i : ℕ, i < M a ∧ g (V a i)=2 • g (V a (M a-1))+b := by
  classical
  let P : ℕ → Prop := fun l ↦ ∃ M : β → ℕ, ∃ V : β → ℕ → Fin n,
    ActualAffineChainFamily g b x M V ∧ M a=l ∧ (∑ c, L c) ≤ (∑ c, M c) ∧
      chainFamilyTruncatedError n M ≤ chainFamilyTruncatedError n L
  let T := (Finset.range (n+1)).filter P
  have hlength (M : β → ℕ) (V : β → ℕ → Fin n)
      (hMV : ActualAffineChainFamily g b x M V) : M a ≤ n :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)).trans
      (actual_affine_chain_family_length_le g b x M V hMV)
  have hLa : L a ≤ n := hlength L v hv
  have haT : L a ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
    ⟨L,v,hv,rfl,le_refl _,le_refl _⟩⟩
  obtain ⟨l,hlT,hmax⟩ := Finset.exists_max_image T id ⟨L a,haT⟩
  have hal : L a ≤ l := hmax (L a) haT
  obtain ⟨M,V,hMV,hMa,hcover,herr⟩ := (Finset.mem_filter.mp hlT).2
  have hwide' : 2*n+1 ≤ 2^(M a) := hwide.trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega))
  have hcharge' : chainFamilyTruncatedError n M ≤ 2^(M a-3) := by
    calc
      _ ≤ chainFamilyTruncatedError n L := herr
      _ ≤ 2^(L a-3) := hcharge
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)
  obtain ⟨w,hw⟩ := exists_target_of_truncated_family_below_binary (by omega)
    g hg hsub b x M V hMV a (by omega) hwide' hcharge'
  have hown : ∃ i, i < M a ∧ V a i=w := by
    by_contra hh
    by_cases hother : ∃ c i, i < M c ∧ V c i=w
    · obtain ⟨c,i,hi,hci⟩ := hother
      have hac : a ≠ c := by
        intro heq
        subst c
        exact hh ⟨i,hi,hci⟩
      obtain ⟨MM,VV,hnew,hgrow,hsame,hothers⟩ := actual_affine_chain_family_splice_controlled g b x M V hMV a c hac
        (by omega) i hi (by rw [hci]; exact hw)
      have herrnew : chainFamilyTruncatedError n MM ≤ chainFamilyTruncatedError n L :=
        (chain_family_truncated_error_mono M MM a (by omega) (by omega) hothers (by omega)).trans herr
      have hlen := hlength MM VV hnew
      have hmem : MM a ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        ⟨MM,VV,hnew,rfl,by omega,herrnew⟩⟩
      have hm := hmax (MM a) hmem
      change MM a ≤ l at hm
      omega
    · obtain ⟨MM,VV,hnew,hgrow,hmore,hothers⟩ := actual_affine_chain_family_extend_controlled g b x M V hMV a
        (by omega) w (by intro c i hi heq; exact hother ⟨c,i,hi,heq⟩) hw
      have herrnew : chainFamilyTruncatedError n MM ≤ chainFamilyTruncatedError n L :=
        (chain_family_truncated_error_mono M MM a (by omega) (by omega) hothers (by omega)).trans herr
      have hlen := hlength MM VV hnew
      have hmem : MM a ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        ⟨MM,VV,hnew,rfl,by omega,herrnew⟩⟩
      have hm := hmax (MM a) hmem
      change MM a ≤ l at hm
      omega
  obtain ⟨i,hi,hwi⟩ := hown
  exact ⟨M,V,hMV,by omega,hcover,herr,i,hi,by rw [hwi]; exact hw⟩

/-- Compatibility interface for maximal truncated-profile continuation. -/
theorem exists_truncated_chain_family_internal_rejoin
    {β : Type*} [Fintype β] [DecidableEq β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a : β) (ha : 4 ≤ L a)
    (hwide : 2*n+1 ≤ 2^(L a))
    (hcharge : chainFamilyTruncatedError n L ≤ 2^(L a-3)) :
    ∃ M : β → ℕ, ∃ V : β → ℕ → Fin n,
      ActualAffineChainFamily g b x M V ∧ L a ≤ M a ∧ (∑ c, L c) ≤ (∑ c, M c) ∧
        ∃ i : ℕ, i < M a ∧ g (V a i)=2 • g (V a (M a-1))+b := by
  obtain ⟨M,V,hMV,hgrow,hcover,_,hjoin⟩ :=
    exists_truncated_chain_family_internal_rejoin_controlled g hg hsub b x L v hv a ha hwide hcharge
  exact ⟨M,V,hMV,hgrow,hcover,hjoin⟩

/-- Exact truncated-profile continuation and collective outside growth
yield an actual majority cycle with arbitrary endpoints and outsiders. -/
theorem exists_majority_cycle_of_truncated_family
    {β : Type*} [Fintype β] [DecidableEq β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a : β) (ha : 4 ≤ L a)
    (hwide : 2*n+1 ≤ 2^(L a))
    (hcharge : chainFamilyTruncatedError n L ≤ 2^(L a-3)) (t : ℕ)
    (hcover : 2^t*n+2*(Fintype.card β)*(t*2^t-(2^t-1)) ≤ 2*(2^t-1)*(∑ i, L i)) :
    ∃ c : ℕ, 2 ≤ c ∧ n ≤ 2*c ∧ ∃ C : Fin c ↪ Fin n,
      ∃ R : Equiv.Perm (Fin c), ∀ i, g (C (R i))=2 • g (C i)+b := by
  obtain ⟨M,V,hMV,hgrow,hsize,i,hi,hjoin⟩ :=
    exists_truncated_chain_family_internal_rejoin g hg hsub b x L v hv a ha hwide hcharge
  obtain ⟨c,hc,hcp,C,R,hC,hbudget⟩ := exists_cycle_with_joint_family_budget_of_rejoin
    g hg b x M V hMV a i hi hjoin
  have hmajor := majority_of_joint_family_layer_budget hcp hsize (hbudget t) hcover
  have hLa : L a ≤ n :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)).trans
      (actual_affine_chain_family_length_le g b x L v hv)
  exact ⟨c,by omega,hmajor,C,R,hC⟩

/-- Original global bound with collective, depth-parameterized coverage
for arbitrary embedded families of actual affine chains. -/
theorem global_lower_bound_of_truncated_chain_family
    {β : Type*} [Fintype β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hwide : 2*n+1 ≤ 2^(L a))
    (hcharge : chainFamilyTruncatedError n L ≤ 2^(L a-3)) (t : ℕ)
    (hcover : 2^t*n+2*(Fintype.card β)*(t*2^t-(2^t-1)) ≤ 2*(2^t-1)*(∑ i, L i)) :
    globalBound n ≤ N := by
  classical
  by_cases hsub : N < 2^n
  · have hn : 0 < n := by have := (e ⟨a,⟨0,by omega⟩⟩).isLt; omega
    obtain ⟨v,hv⟩ := exists_actual_affine_chain_family_of_embedding hn g b x L e hchain
    obtain ⟨c,hc,hmajor,C,R,hR⟩ := exists_majority_cycle_of_truncated_family
      g hg hsub b x L v hv a ha hwide hcharge t hcover
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact global_lower_bound_of_valid_majority_affine_doubling_cycle hc (by omega) g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Every original exact stratum at the same collective coverage bound. -/
theorem stratum_lower_bound_of_truncated_chain_family
    {β : Type*} [Fintype β] {n s d : ℕ} (hd : Odd d)
    (g : Fin n → ZMod (2^s*d)) (hg : ValidTuple g)
    (b : ZMod (2^s*d)) (x : β → ZMod (2^s*d)) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hwide : 2*n+1 ≤ 2^(L a))
    (hcharge : chainFamilyTruncatedError n L ≤ 2^(L a-3)) (t : ℕ)
    (hcover : 2^t*n+2*(Fintype.card β)*(t*2^t-(2^t-1)) ≤ 2*(2^t-1)*(∑ i, L i)) :
    stratumBound n s ≤ 2^s*d := by
  classical
  letI : NeZero (2^s*d) := ⟨(mul_pos (by positivity) hd.pos).ne'⟩
  by_cases hsub : 2^s*d < 2^n
  · have hn : 0 < n := by have := (e ⟨a,⟨0,by omega⟩⟩).isLt; omega
    obtain ⟨v,hv⟩ := exists_actual_affine_chain_family_of_embedding hn g b x L e hchain
    obtain ⟨c,hc,hmajor,C,R,hR⟩ := exists_majority_cycle_of_truncated_family
      g hg hsub b x L v hv a ha hwide hcharge t hcover
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact stratum_lower_bound_of_valid_majority_affine_doubling_cycle hc (by omega) hd g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Original G3 exclusion with collective family coverage. -/
theorem not_validTuple_exceptional_of_truncated_chain_family
    {β : Type*} [Fintype β] {n : ℕ} (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b : ZMod (2*globalBound (n-1))) (x : β → ZMod (2*globalBound (n-1))) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hwide : 2*n+1 ≤ 2^(L a))
    (hcharge : chainFamilyTruncatedError n L ≤ 2^(L a-3)) (t : ℕ)
    (hcover : 2^t*n+2*(Fintype.card β)*(t*2^t-(2^t-1)) ≤ 2*(2^t-1)*(∑ i, L i)) :
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
  have h := global_lower_bound_of_truncated_chain_family g hg b x L e hchain a ha hwide hcharge t hcover
  omega

end MinModulus
