import MinModulus.ChainForestTruncatedInterval

/-! Long actual affine chains force the original global and every
exact-stratum bound, with arbitrary endpoints and remaining coordinates.
Below binary size, maximal continuation rejoins internally. The actual
cycle suffix loses only a logarithmic incoming tail, so a chain longer
than half the tuple plus its logarithm yields a majority cycle. Original
G3 and counterexample chain-length restrictions follow; all unrestricted
global gates remain open. -/

namespace MinModulus
open Finset
open scoped Classical

/-- An actual new target extends a chain embedding by one coordinate. -/
theorem exists_affine_chain_extension_of_new_target
    {n m : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (b x : G) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (v : Fin n) (hnew : ∀ i, e i ≠ v)
    (htarget : g v=2 • g (e ⟨m-1,by omega⟩)+b) :
    ∃ f : Fin (m+1) ↪ Fin n, ∀ i, g (f i)+b=2^i.val • x := by
  let F : Fin (m+1) → Fin n := Fin.lastCases v e
  have hF : Function.Injective F := by
    intro a
    refine Fin.lastCases ?_ (fun i ↦ ?_) a
    · intro b
      refine Fin.lastCases (fun _ ↦ rfl) (fun j he ↦ ?_) b
      exact (hnew j (by simpa only [F,Fin.lastCases_last,Fin.lastCases_castSucc] using he.symm)).elim
    · intro b
      refine Fin.lastCases (fun he ↦ ?_) (fun j he ↦ ?_) b
      · exact (hnew i (by simpa only [F,Fin.lastCases_last,Fin.lastCases_castSucc] using he)).elim
      · exact congrArg Fin.castSucc (e.injective (by simpa only [F,Fin.lastCases_castSucc] using he))
  refine ⟨⟨F,hF⟩,?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [Function.Embedding.coeFn_mk,F,Fin.lastCases_last,Fin.val_last]
    calc
      _=2 • (g (e ⟨m-1,by omega⟩)+b) := by rw [htarget]; simp only [two_nsmul]; abel
      _=2 • (2^(m-1) • x) := by rw [hchain]
      _=2^m • x := by rw [← mul_smul,← pow_succ',Nat.sub_add_cancel (by omega : 1 ≤ m)]
  · simpa only [Function.Embedding.coeFn_mk,F,Fin.lastCases_castSucc,Fin.val_castSucc] using hchain j

/-- Below binary size, any sufficiently long affine chain extends to
an actual maximal chain whose final target rejoins that same chain. -/
theorem exists_long_affine_chain_with_internal_rejoin_below_binary
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x : ZMod N) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hlong : n+Nat.log 2 n+4 ≤ 2*m) :
    ∃ p : ℕ, m ≤ p ∧ ∃ f : Fin p ↪ Fin n,
      (∀ i, g (f i)+b=2^i.val • x) ∧
        ∀ i : Fin p, i.val+1=p → ∃ t, g (f t)=2 • g (f i)+b := by
  classical
  let P : ℕ → Prop := fun p ↦ ∃ f : Fin p ↪ Fin n, ∀ i, g (f i)+b=2^i.val • x
  let S := (Finset.range (n+1)).filter P
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  have hmS : m ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),⟨e,hchain⟩⟩
  obtain ⟨p,hpS,hmax⟩ := Finset.exists_max_image S id ⟨m,hmS⟩
  have hmp : m ≤ p := hmax m hmS
  obtain ⟨f,hf⟩ := (Finset.mem_filter.mp hpS).2
  obtain ⟨v,hv⟩ := exists_target_of_logarithmically_long_chain_below_binary (by omega : 4 ≤ p)
    g hg hsub b x f hf (by omega)
  have hmem : ∃ t, f t=v := by
    by_contra hh
    obtain ⟨F,hF⟩ := exists_affine_chain_extension_of_new_target (by omega : 0 < p) g b x f hf v
      (by intro i hi; exact hh ⟨i,hi⟩) hv
    have hpn : p+1 ≤ n := by simpa using Fintype.card_le_of_injective _ F.injective
    have hnew : p+1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),⟨F,hF⟩⟩
    have hm := hmax (p+1) hnew
    change p+1 ≤ p at hm
    omega
  obtain ⟨t,ht⟩ := hmem
  refine ⟨p,hmp,f,hf,?_⟩
  intro i hi
  refine ⟨t,?_⟩
  have hei : (⟨p-1,by omega⟩ : Fin p)=i := by
    apply Fin.ext
    change p-1=i.val
    omega
  simpa only [ht,hei] using hv

/-- An internal rejoin turns the suffix of an actual power chain into
an actual doubling-permuted cycle. -/
theorem doubling_cycle_of_chain_suffix_rejoin
    {t c : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (u : Fin (t+c) → G) (x : G) (hchain : ∀ i, u i=2^i.val • x)
    (hjoin : u (Fin.natAdd t ⟨0,hc⟩)=2 • u ⟨t+c-1,by omega⟩) :
    ∀ i, u (Fin.natAdd t (finRotate c i))=2 • u (Fin.natAdd t i) := by
  cases c with
  | zero => omega
  | succ c =>
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · have hlast : Fin.natAdd t (Fin.last c)=(⟨t+(c+1)-1,by omega⟩ : Fin (t+(c+1))) := by
        apply Fin.ext
        simp only [Fin.val_natAdd,Fin.val_last]
        omega
      rw [finRotate_last,hlast]
      exact hjoin
    · have hrot : finRotate (c+1) j.castSucc=j.succ := finRotate_of_lt j.isLt
      rw [hrot,hchain,hchain]
      simp only [Fin.val_natAdd,Fin.val_succ,Fin.val_castSucc]
      rw [show t+(j.val+1)=(t+j.val)+1 by omega,pow_succ',mul_smul]

/-- The incoming part of a valid chain with an internal rejoin has
logarithmic length; the cyclic suffix and its zero sum are extracted. -/
theorem tail_le_log_of_valid_chain_suffix_rejoin
    {t c : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (u : Fin (t+c) → G) (hu : ValidTuple u) (x : G)
    (hchain : ∀ i, u i=2^i.val • x)
    (hjoin : u (Fin.natAdd t ⟨0,hc⟩)=2 • u ⟨t+c-1,by omega⟩) :
    t ≤ Nat.log 2 (t+c) := by
  let F : Fin (c+t) ≃ Fin (t+c) := finSumFinEquiv.symm.trans
    ((Equiv.sumComm (Fin c) (Fin t)).trans finSumFinEquiv)
  have hleft (i : Fin c) : F (Fin.castAdd t i)=Fin.natAdd t i := by simp [F]
  have hright (i : Fin t) : F (Fin.natAdd c i)=Fin.castAdd c i := by simp [F]
  have hd := doubling_cycle_of_chain_suffix_rejoin hc u x hchain hjoin
  have hh := logarithmic_chain_of_valid_affine_cycle_chain hc (fun i ↦ u (F i))
    (validTuple_embedding F.toEmbedding u hu) (Equiv.refl _) 0 x (finRotate c)
    (by intro i; simpa only [Equiv.refl_apply,hleft,add_zero] using hd i)
    (by intro i; simp only [Equiv.refl_apply,hright,add_zero,hchain,Fin.val_castAdd])
  simpa only [Nat.add_comm c t] using hh

/-- A valid actual chain with an internal rejoin contains a cycle
losing at most logarithmically many chain coordinates. -/
theorem exists_cycle_of_affine_chain_internal_rejoin
    {n p : ℕ} (hp : 0 < p) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b x : G) (e : Fin p ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hjoin : ∃ a, g (e a)=2 • g (e ⟨p-1,by omega⟩)+b) :
    ∃ c : ℕ, 0 < c ∧ p ≤ c+Nat.log 2 n ∧ ∃ f : Fin c ↪ Fin n,
      ∃ R : Equiv.Perm (Fin c), ∀ i, g (f (R i))=2 • g (f i)+b := by
  obtain ⟨a,ha⟩ := hjoin
  have hap := a.isLt
  generalize hqa : a.val=q at *
  obtain ⟨c,hpc⟩ := Nat.exists_eq_add_of_le (by omega : q ≤ p)
  have hc : 0 < c := by omega
  subst p
  let u : Fin (q+c) → G := fun i ↦ g (e i)+b
  have hu : ValidTuple u := by
    simpa only [u,sub_neg_eq_add] using validTuple_sub_const (fun i ↦ g (e i))
      (validTuple_embedding e g hg) (-b)
  have hui : ∀ i, u i=2^i.val • x := hchain
  have hea : a=Fin.natAdd q ⟨0,hc⟩ := by
    apply Fin.ext
    simp only [Fin.val_natAdd,add_zero]
    exact hqa
  have hj : u (Fin.natAdd q ⟨0,hc⟩)=2 • u ⟨q+c-1,by omega⟩ := by
    dsimp only [u]
    rw [← hea,ha]
    simp only [two_nsmul]
    abel
  have hpn : q+c ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  have hqlog : q ≤ Nat.log 2 n := (tail_le_log_of_valid_chain_suffix_rejoin hc u hu x hui hj).trans
    (Nat.log_mono_right hpn)
  have hd := doubling_cycle_of_chain_suffix_rejoin hc u x hui hj
  let f : Fin c ↪ Fin n := ⟨fun i ↦ e (Fin.natAdd q i),by
    intro i j he
    have hv := congrArg Fin.val (e.injective he)
    simp only [Fin.val_natAdd] at hv
    exact Fin.ext (by omega)⟩
  refine ⟨c,hc,by omega,f,finRotate c,?_⟩
  intro i
  have he := hd i
  change g (e (Fin.natAdd q (finRotate c i)))+b=2 • (g (e (Fin.natAdd q i))+b) at he
  change g (e (Fin.natAdd q (finRotate c i)))=2 • g (e (Fin.natAdd q i))+b
  apply add_right_cancel (b := b)
  calc
    _=2 • (g (e (Fin.natAdd q i))+b) := he
    _=(2 • g (e (Fin.natAdd q i))+b)+b := by simp only [two_nsmul]; abel

/-- Every actual chain longer than half the tuple plus its logarithm
forces a majority cycle below binary modulus. Its continuation, rejoin,
cycle and incoming-tail bound are all extracted from the original tuple. -/
theorem exists_majority_cycle_of_long_affine_chain_below_binary
    {n m N : ℕ} [NeZero N] (hn : 16 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x : ZMod N) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hlong : n+2*Nat.log 2 n ≤ 2*m) :
    ∃ c : ℕ, 2 ≤ c ∧ n ≤ 2*c ∧ ∃ f : Fin c ↪ Fin n,
      ∃ R : Equiv.Perm (Fin c), ∀ i, g (f (R i))=2 • g (f i)+b := by
  have hlog : 4 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide : 1 < (2 : ℕ)) (by omega : n ≠ 0)).mpr (by norm_num; omega)
  obtain ⟨p,hmp,f,hf,hjoin⟩ := exists_long_affine_chain_with_internal_rejoin_below_binary (by omega : 4 ≤ m)
    g hg hsub b x e hchain (by omega)
  obtain ⟨c,hc,hpc,F,R,hR⟩ := exists_cycle_of_affine_chain_internal_rejoin (by omega : 0 < p)
    g hg b x f hf (hjoin ⟨p-1,by omega⟩ (by simp only; omega))
  exact ⟨c,by omega,by omega,F,R,hR⟩

/-- The full global bound for any actual affine chain longer than half
the tuple plus its logarithm. Its endpoint and all outsiders are arbitrary. -/
theorem global_lower_bound_of_logarithmically_long_affine_chain
    {n m N : ℕ} [NeZero N] (hn : 16 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (b x : ZMod N) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hlong : n+2*Nat.log 2 n ≤ 2*m) : globalBound n ≤ N := by
  by_cases hsub : N < 2^n
  · obtain ⟨c,hc,hmajor,F,R,hR⟩ := exists_majority_cycle_of_long_affine_chain_below_binary hn g hg hsub b x e hchain hlong
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ F.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) F
      (Fin.castAdd_injective c k) F.injective
    exact global_lower_bound_of_valid_majority_affine_doubling_cycle hc (by omega) g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Every original exact-stratum bound for the same whole long-chain
class, including arbitrary opposite pairs and rejoining endpoints. -/
theorem stratum_lower_bound_of_logarithmically_long_affine_chain
    {n m s q : ℕ} (hq : Odd q) (hn : 16 ≤ n)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (b x : ZMod (2^s*q)) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hlong : n+2*Nat.log 2 n ≤ 2*m) : stratumBound n s ≤ 2^s*q := by
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  by_cases hsub : 2^s*q < 2^n
  · obtain ⟨c,hc,hmajor,F,R,hR⟩ := exists_majority_cycle_of_long_affine_chain_below_binary hn g hg hsub b x e hchain hlong
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ F.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) F
      (Fin.castAdd_injective c k) F.injective
    exact stratum_lower_bound_of_valid_majority_affine_doubling_cycle hc (by omega) hq g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Original G3 excludes every tuple containing a chain past the
logarithmic half-length cutoff; the endpoint need not be genuine. -/
theorem not_validTuple_exceptional_of_logarithmically_long_affine_chain
    {n m : ℕ} (hn : 16 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b x : ZMod (2*globalBound (n-1))) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hlong : n+2*Nat.log 2 n ≤ 2*m) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  have hb := global_lower_bound_of_logarithmically_long_affine_chain hn g hg b x e hchain hlong
  omega

/-- Every actual affine chain in a global counterexample stays below
the explicit half-length cutoff, with no restriction on its escape count. -/
theorem chain_length_lt_of_global_counterexample
    {n m N : ℕ} [NeZero N] (hn : 16 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < globalBound n)
    (b x : ZMod N) (e : Fin m ↪ Fin n) (hchain : ∀ i, g (e i)+b=2^i.val • x) :
    2*m < n+2*Nat.log 2 n := by
  by_contra hh
  have hb := global_lower_bound_of_logarithmically_long_affine_chain hn g hg b x e hchain (by omega)
  omega

/-- Every actual affine chain in an original exact-stratum
counterexample obeys the same cutoff, without a half-descent premise. -/
theorem chain_length_lt_of_stratum_counterexample
    {n m s q : ℕ} (hq : Odd q) (hn : 16 ≤ n)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g) (hsmall : 2^s*q < stratumBound n s)
    (b x : ZMod (2^s*q)) (e : Fin m ↪ Fin n) (hchain : ∀ i, g (e i)+b=2^i.val • x) :
    2*m < n+2*Nat.log 2 n := by
  by_contra hh
  have hb := stratum_lower_bound_of_logarithmically_long_affine_chain hq hn g hg b x e hchain (by omega)
  omega

end MinModulus
