import MinModulus.PartialChainForest

/-! Two disjoint actual affine chains give the original global and every
exact-stratum lower bound beyond an explicit logarithmic one-third
cutoff. Maximality forces the first chain to rejoin itself: new targets
extend it, and targets in the other member splice a suffix while
preserving total coverage. The disjoint remaining chain and incoming
tail are logarithmic, leaving an actual majority cycle. All endpoints,
seeds and remaining coordinates are arbitrary. Original G3 is excluded
in this class; the unrestricted G1/G2/G3 obligations remain open. -/

namespace MinModulus
open Finset
open scoped Classical

/-- Two selected disjoint chains pay by their joint covered length.
Their endpoints and all other coordinates remain actual. -/
theorem exists_target_of_two_chain_cover_below_binary
    {n p q N : ℕ} [NeZero N] (hp : 4 ≤ p)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x y : ZMod N) (e : Fin p ↪ Fin n) (f : Fin q ↪ Fin n)
    (hdisj : ∀ i j, e i ≠ f j)
    (he : ∀ i, g (e i)+b=2^i.val • x)
    (hf : ∀ j, g (f j)+b=2^j.val • y)
    (hcharge : n^2*2^(n-(p+q)) ≤ 2^(p-3)) :
    ∃ v, g v=2 • g (e ⟨p-1,by omega⟩)+b := by
  have hpn : p ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  by_cases hq : 0 < q
  · let L : Bool → ℕ := fun a ↦ bif a then q else p
    let E : (Σ a, Fin (L a)) → Fin n := fun z ↦ match z with
      | ⟨false,i⟩ => e i
      | ⟨true,j⟩ => f j
    have hE : Function.Injective E := by
      rintro ⟨a,i⟩ ⟨c,j⟩ h
      cases a <;> cases c
      · have hij := e.injective h; subst j; rfl
      · exact (hdisj i j h).elim
      · exact (hdisj j i h.symm).elim
      · have hij := f.injective h; subst j; rfl
    let z : Bool → ZMod N := fun a ↦ bif a then y else x
    have hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • z a := by
      intro a i
      cases a
      · exact he i
      · exact hf i
    have h := exists_target_of_partial_chain_forest_below_binary (by omega) L
      (by intro a; cases a <;> simp [L] <;> omega) g hg hsub b z ⟨E,hE⟩ hchain false hp
      (by simpa [L,add_comm] using hcharge)
    exact h
  · have hq0 : q=0 := by omega
    have hn : n ≤ n^2 := by nlinarith
    apply exists_target_of_embedded_long_chain_below_binary hp g hg hsub b x e he
    exact (Nat.mul_le_mul_right _ hn).trans (by simpa only [hq0,Nat.add_zero] using hcharge)

/-- A new actual target extends one member while preserving disjointness
from every coordinate of the other member. -/
theorem exists_disjoint_affine_chain_extension
    {n p q : ℕ} (hp : 0 < p) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (b x : G) (e : Fin p ↪ Fin n) (f : Fin q ↪ Fin n)
    (hdisj : ∀ i j, e i ≠ f j) (he : ∀ i, g (e i)+b=2^i.val • x)
    (v : Fin n) (hnew : ∀ i, e i ≠ v) (haway : ∀ j, v ≠ f j)
    (htarget : g v=2 • g (e ⟨p-1,by omega⟩)+b) :
    ∃ E : Fin (p+1) ↪ Fin n,
      (∀ i, g (E i)+b=2^i.val • x) ∧ ∀ i j, E i ≠ f j := by
  let F : Fin (p+1) → Fin n := Fin.lastCases v e
  have hF : Function.Injective F := by
    intro a
    refine Fin.lastCases ?_ (fun i ↦ ?_) a
    · intro c
      refine Fin.lastCases (fun _ ↦ rfl) (fun j hj ↦ ?_) c
      exact (hnew j (by simpa only [F,Fin.lastCases_last,Fin.lastCases_castSucc] using hj.symm)).elim
    · intro c
      refine Fin.lastCases (fun hj ↦ ?_) (fun j hj ↦ ?_) c
      · exact (hnew i (by simpa only [F,Fin.lastCases_last,Fin.lastCases_castSucc] using hj)).elim
      · exact congrArg Fin.castSucc (e.injective (by simpa only [F,Fin.lastCases_castSucc] using hj))
  refine ⟨⟨F,hF⟩,?_,?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [Function.Embedding.coeFn_mk,F,Fin.lastCases_last,Fin.val_last]
      calc
        _=2 • (g (e ⟨p-1,by omega⟩)+b) := by rw [htarget]; simp only [two_nsmul]; abel
        _=2 • (2^(p-1) • x) := by rw [he]
        _=2^p • x := by rw [← mul_smul,← pow_succ',Nat.sub_add_cancel hp]
    · simpa only [Function.Embedding.coeFn_mk,F,Fin.lastCases_castSucc,Fin.val_castSucc] using he j
  · intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [Function.Embedding.coeFn_mk,F,Fin.lastCases_last] using haway
    · simpa only [Function.Embedding.coeFn_mk,F,Fin.lastCases_castSucc] using hdisj j

/-- A target in the other chain moves its entire suffix onto the first
chain. The prefix remains disjoint, and total coverage is unchanged. -/
theorem exists_disjoint_affine_chain_suffix_splice
    {n p q : ℕ} (hp : 0 < p) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (b x y : G) (e : Fin p ↪ Fin n) (f : Fin q ↪ Fin n)
    (hdisj : ∀ i j, e i ≠ f j)
    (he : ∀ i, g (e i)+b=2^i.val • x) (hf : ∀ j, g (f j)+b=2^j.val • y)
    (a : Fin q) (htarget : g (f a)=2 • g (e ⟨p-1,by omega⟩)+b) :
    ∃ E : Fin (p+(q-a.val)) ↪ Fin n, ∃ F : Fin a.val ↪ Fin n,
      (∀ i j, E i ≠ F j) ∧
      (∀ i, g (E i)+b=2^i.val • x) ∧ (∀ j, g (F j)+b=2^j.val • y) := by
  let tail : Fin (q-a.val) ↪ Fin q :=
    ⟨fun i ↦ ⟨a.val+i.val,by have := i.isLt; omega⟩,by
      intro i j h; apply Fin.ext; have := congrArg Fin.val h; simpa using this⟩
  let pref : Fin a.val ↪ Fin q :=
    ⟨fun i ↦ ⟨i.val,by have := i.isLt; have := a.isLt; omega⟩,by
      intro i j h; exact Fin.ext (congrArg (fun z : Fin q ↦ z.val) h)⟩
  let A : Fin p ⊕ Fin (q-a.val) → Fin n := Sum.elim e (fun i ↦ f (tail i))
  have hA : Function.Injective A := by
    rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (e.injective h)
    · exact (hdisj i (tail j) h).elim
    · exact (hdisj j (tail i) h.symm).elim
    · exact congrArg Sum.inr (tail.injective (f.injective h))
  let E : Fin (p+(q-a.val)) ↪ Fin n := ⟨fun i ↦ A (finSumFinEquiv.symm i),hA.comp finSumFinEquiv.symm.injective⟩
  let F : Fin a.val ↪ Fin n := pref.trans f
  have hleft (i : Fin p) : E (Fin.castAdd (q-a.val) i)=e i := by simp [E,A]
  have hright (i : Fin (q-a.val)) : E (Fin.natAdd p i)=f (tail i) := by simp [E,A]
  have hjoin : 2^a.val • y=2^p • x := by
    calc
      _=g (f a)+b := (hf a).symm
      _=2 • (g (e ⟨p-1,by omega⟩)+b) := by rw [htarget]; simp only [two_nsmul]; abel
      _=2 • (2^(p-1) • x) := by rw [he]
      _=2^p • x := by rw [← mul_smul,← pow_succ',Nat.sub_add_cancel hp]
  refine ⟨E,F,?_,?_,?_⟩
  · intro i j
    refine Fin.addCases ?_ ?_ i
    · intro i
      rw [hleft]
      exact hdisj i (pref j)
    · intro i
      rw [hright]
      intro hh
      have hv := congrArg Fin.val (f.injective hh)
      change a.val+i.val=j.val at hv
      have := j.isLt
      omega
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa only [hleft,Fin.val_castAdd] using he i
    · intro i
      rw [hright,hf]
      change 2^(a.val+i.val) • y=2^(p+i.val) • x
      rw [Nat.add_comm a.val i.val,Nat.add_comm p i.val,pow_add,pow_add,mul_smul,mul_smul,hjoin]
  · intro j
    exact hf (pref j)

/-- A maximal two-chain family cannot end outside its first chain:
new targets extend it and targets in the other chain splice a suffix.
Combined coverage, both actual seeds and disjointness are preserved. -/
theorem exists_two_chain_cover_internal_rejoin_below_binary
    {n p q N : ℕ} [NeZero N] (hp : 4 ≤ p)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x y : ZMod N) (e : Fin p ↪ Fin n) (f : Fin q ↪ Fin n)
    (hdisj : ∀ i j, e i ≠ f j)
    (he : ∀ i, g (e i)+b=2^i.val • x) (hf : ∀ j, g (f j)+b=2^j.val • y)
    (hcharge : n^2*2^(n-(p+q)) ≤ 2^(p-3)) :
    ∃ l t : ℕ, p ≤ l ∧ p+q ≤ l+t ∧
      ∃ E : Fin l ↪ Fin n, ∃ F : Fin t ↪ Fin n,
        (∀ i j, E i ≠ F j) ∧
        (∀ i, g (E i)+b=2^i.val • x) ∧ (∀ j, g (F j)+b=2^j.val • y) ∧
        ∀ i : Fin l, i.val+1=l → ∃ a, g (E a)=2 • g (E i)+b := by
  classical
  let P : ℕ → Prop := fun l ↦ ∃ t : ℕ, ∃ E : Fin l ↪ Fin n, ∃ F : Fin t ↪ Fin n,
    (∀ i j, E i ≠ F j) ∧ (∀ i, g (E i)+b=2^i.val • x) ∧
      (∀ j, g (F j)+b=2^j.val • y) ∧ p+q ≤ l+t
  let T := (Finset.range (n+1)).filter P
  have hpn : p ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  have hpT : p ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
    ⟨q,e,f,hdisj,he,hf,le_refl _⟩⟩
  obtain ⟨l,hlT,hmax⟩ := Finset.exists_max_image T id ⟨p,hpT⟩
  have hpl : p ≤ l := hmax p hpT
  obtain ⟨t,E,F,hd,hE,hF,hcover⟩ := (Finset.mem_filter.mp hlT).2
  have hcharge' : n^2*2^(n-(l+t)) ≤ 2^(l-3) := by
    calc
      _ ≤ n^2*2^(n-(p+q)) := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega))
      _ ≤ 2^(p-3) := hcharge
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)
  obtain ⟨v,hv⟩ := exists_target_of_two_chain_cover_below_binary (by omega : 4 ≤ l)
    g hg hsub b x y E F hd hE hF hcharge'
  have hown : ∃ a, E a=v := by
    by_contra hh
    have hnew : ∀ i, E i ≠ v := by intro i hi; exact hh ⟨i,hi⟩
    by_cases hother : ∃ j, F j=v
    · obtain ⟨a,ha⟩ := hother
      obtain ⟨EE,FF,hdd,hee,hff⟩ := exists_disjoint_affine_chain_suffix_splice (by omega : 0 < l)
        g b x y E F hd hE hF a (by rw [ha]; exact hv)
      have hlen : l+(t-a.val) ≤ n := by simpa using Fintype.card_le_of_injective _ EE.injective
      have hmem : l+(t-a.val) ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        ⟨a.val,EE,FF,hdd,hee,hff,by have := a.isLt; omega⟩⟩
      have hm := hmax _ hmem
      change l+(t-a.val) ≤ l at hm
      have := a.isLt
      omega
    · obtain ⟨EE,hee,hdd⟩ := exists_disjoint_affine_chain_extension (by omega : 0 < l)
        g b x E F hd hE v hnew (by intro j hj; exact hother ⟨j,hj.symm⟩) hv
      have hlen : l+1 ≤ n := by simpa using Fintype.card_le_of_injective _ EE.injective
      have hmem : l+1 ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        ⟨t,EE,F,hdd,hee,hF,by omega⟩⟩
      have hm := hmax _ hmem
      change l+1 ≤ l at hm
      omega
  obtain ⟨a,ha⟩ := hown
  refine ⟨l,t,hpl,hcover,E,F,hd,hE,hF,?_⟩
  intro i hi
  refine ⟨a,?_⟩
  have hei : (⟨l-1,by omega⟩ : Fin l)=i := by apply Fin.ext; change l-1=i.val; omega
  simpa only [ha,hei] using hv

/-- Any actual chain disjoint from a nonempty affine cycle has
logarithmic length, regardless of all other coordinates. -/
theorem logarithmic_chain_disjoint_from_affine_cycle
    {n c t : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b y : G)
    (e : Fin c ↪ Fin n) (f : Fin t ↪ Fin n) (R : Equiv.Perm (Fin c))
    (hdisj : ∀ i j, e i ≠ f j)
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b)
    (hchain : ∀ j, g (f j)+b=2^j.val • y) : t ≤ Nat.log 2 n := by
  let A : Fin c ⊕ Fin t → Fin n := Sum.elim e f
  have hA : Function.Injective A := by
    rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (e.injective h)
    · exact (hdisj i j h).elim
    · exact (hdisj j i h.symm).elim
    · exact congrArg Sum.inr (f.injective h)
  let E : Fin (c+t) ↪ Fin n := ⟨fun i ↦ A (finSumFinEquiv.symm i),hA.comp finSumFinEquiv.symm.injective⟩
  have hleft (i : Fin c) : E (Fin.castAdd t i)=e i := by simp [E,A]
  have hright (i : Fin t) : E (Fin.natAdd c i)=f i := by simp [E,A]
  have hn : c+t ≤ n := by simpa using Fintype.card_le_of_injective _ E.injective
  have h := logarithmic_chain_of_valid_affine_cycle_chain hc (fun i ↦ g (E i))
    (validTuple_embedding E g hg) (Equiv.refl _) b y R
    (by simpa only [Equiv.refl_apply,hleft] using hcycle)
    (by simpa only [Equiv.refl_apply,hright] using hchain)
  exact h.trans (Nat.log_mono_right hn)

/-- Combined coverage of two chains yields an ACTUAL majority cycle.
Neither endpoint is assumed genuine, and the remaining coordinates
have no shape or escape-count restriction. -/
theorem exists_majority_cycle_of_two_chain_cover_below_binary
    {n p q N : ℕ} [NeZero N] (hp : 4 ≤ p)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x y : ZMod N) (e : Fin p ↪ Fin n) (f : Fin q ↪ Fin n)
    (hdisj : ∀ i j, e i ≠ f j)
    (he : ∀ i, g (e i)+b=2^i.val • x) (hf : ∀ j, g (f j)+b=2^j.val • y)
    (hcharge : n^2*2^(n-(p+q)) ≤ 2^(p-3))
    (hcover : n+4*Nat.log 2 n ≤ 2*(p+q)) :
    ∃ c : ℕ, 2 ≤ c ∧ n ≤ 2*c ∧ ∃ C : Fin c ↪ Fin n,
      ∃ R : Equiv.Perm (Fin c), ∀ i, g (C (R i))=2 • g (C i)+b := by
  obtain ⟨l,t,hpl,hsize,E,F,hd,hE,hF,hjoin⟩ :=
    exists_two_chain_cover_internal_rejoin_below_binary hp g hg hsub b x y e f hdisj he hf hcharge
  obtain ⟨c,hc,hlc,C,R,hC⟩ := exists_cycle_of_affine_chain_internal_rejoin (by omega : 0 < l)
    (fun i ↦ g (E i)) (validTuple_embedding E g hg) b x (Function.Embedding.refl _) hE
    (hjoin ⟨l-1,by omega⟩ (by change l-1+1=l; omega))
  have hn : l ≤ n := by simpa using Fintype.card_le_of_injective _ E.injective
  have hlog := Nat.log_mono_right (b := 2) hn
  have ht := logarithmic_chain_disjoint_from_affine_cycle hc g hg b y (C.trans E) F R
    (fun i j ↦ hd (C i) j) hC hF
  have hcn : n ≤ 2*c := by omega
  have hpn : p ≤ n := by omega
  exact ⟨c,by omega,hcn,C.trans E,R,hC⟩

/-- Original global lower bound for the combined two-chain class. -/
theorem global_lower_bound_of_two_chain_cover
    {n p q N : ℕ} [NeZero N] (hp : 4 ≤ p)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (b x y : ZMod N) (e : Fin p ↪ Fin n) (f : Fin q ↪ Fin n)
    (hdisj : ∀ i j, e i ≠ f j)
    (he : ∀ i, g (e i)+b=2^i.val • x) (hf : ∀ j, g (f j)+b=2^j.val • y)
    (hcharge : n^2*2^(n-(p+q)) ≤ 2^(p-3))
    (hcover : n+4*Nat.log 2 n ≤ 2*(p+q)) : globalBound n ≤ N := by
  by_cases hsub : N < 2^n
  · obtain ⟨c,hc,hmajor,C,R,hR⟩ := exists_majority_cycle_of_two_chain_cover_below_binary
      hp g hg hsub b x y e f hdisj he hf hcharge hcover
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact global_lower_bound_of_valid_majority_affine_doubling_cycle hc (by omega) g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Every exact-stratum bound for the same arbitrary-endpoint class. -/
theorem stratum_lower_bound_of_two_chain_cover
    {n p q s d : ℕ} (hd : Odd d) (hp : 4 ≤ p)
    (g : Fin n → ZMod (2^s*d)) (hg : ValidTuple g)
    (b x y : ZMod (2^s*d)) (e : Fin p ↪ Fin n) (f : Fin q ↪ Fin n)
    (hdisj : ∀ i j, e i ≠ f j)
    (he : ∀ i, g (e i)+b=2^i.val • x) (hf : ∀ j, g (f j)+b=2^j.val • y)
    (hcharge : n^2*2^(n-(p+q)) ≤ 2^(p-3))
    (hcover : n+4*Nat.log 2 n ≤ 2*(p+q)) : stratumBound n s ≤ 2^s*d := by
  letI : NeZero (2^s*d) := ⟨(mul_pos (by positivity) hd.pos).ne'⟩
  by_cases hsub : 2^s*d < 2^n
  · obtain ⟨c,hc,hmajor,C,R,hR⟩ := exists_majority_cycle_of_two_chain_cover_below_binary
      hp g hg hsub b x y e f hdisj he hf hcharge hcover
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact stratum_lower_bound_of_valid_majority_affine_doubling_cycle hc (by omega) hd g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Direct original G3 exclusion for the combined two-chain class. -/
theorem not_validTuple_exceptional_of_two_chain_cover
    {n p q : ℕ} (hn : 4 ≤ n) (hp : 4 ≤ p) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b x y : ZMod (2*globalBound (n-1))) (e : Fin p ↪ Fin n) (f : Fin q ↪ Fin n)
    (hdisj : ∀ i j, e i ≠ f j)
    (he : ∀ i, g (e i)+b=2^i.val • x) (hf : ∀ j, g (f j)+b=2^j.val • y)
    (hcharge : n^2*2^(n-(p+q)) ≤ 2^(p-3))
    (hcover : n+4*Nat.log 2 n ≤ 2*(p+q)) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  have h := global_lower_bound_of_two_chain_cover hp g hg b x y e f hdisj he hf hcharge hcover
  omega

/-- A uniform elementary comparison used to turn the one-third cutoff
into enough total coverage for a majority cycle. -/
theorem four_mul_log_two_le_add_four {n : ℕ} (hn : 0 < n) :
    4*Nat.log 2 n ≤ n+4 := by
  have hpow : ∀ t : ℕ, 4*t ≤ 2^t+4 := by
    intro t
    induction t using Nat.twoStepInduction with
    | zero => norm_num
    | one => norm_num
    | more t h0 h1 =>
      by_cases ht : t=0
      · subst t; norm_num
      have hp : 2 ≤ 2^t := Nat.one_lt_two_pow (by omega)
      rw [pow_succ',pow_succ']
      rw [pow_succ'] at h1
      omega
  exact (hpow (Nat.log 2 n)).trans (Nat.add_le_add_right (Nat.pow_log_le_self 2 (by omega : n ≠ 0)) 4)

/-- Two disjoint equal chains at the explicit one-third cutoff pay
the joint error and cover enough coordinates to force a majority cycle. -/
theorem two_chain_cover_conditions_of_logarithmic_third
    {n m : ℕ} (hm : 4 ≤ m) (hsize : 2*m ≤ n)
    (hlong : n+2*Nat.log 2 n+5 ≤ 3*m) :
    n^2*2^(n-(m+m)) ≤ 2^(m-3) ∧ n+4*Nat.log 2 n ≤ 2*(m+m) := by
  have hlog := four_mul_log_two_le_add_four (by omega : 0 < n)
  refine ⟨partial_chain_forest_charge_of_logarithmic_cover (by omega) ?_,by omega⟩
  omega

/-- Any two actual disjoint affine chains beyond the logarithmic
one-third cutoff imply the original global bound, with arbitrary endpoints. -/
theorem global_lower_bound_of_two_logarithmically_long_affine_chains
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (b x y : ZMod N) (e f : Fin m ↪ Fin n)
    (hdisj : ∀ i j, e i ≠ f j)
    (he : ∀ i, g (e i)+b=2^i.val • x) (hf : ∀ j, g (f j)+b=2^j.val • y)
    (hlong : n+2*Nat.log 2 n+5 ≤ 3*m) : globalBound n ≤ N := by
  have hsize : 2*m ≤ n := by
    let E : Fin m ⊕ Fin m → Fin n := Sum.elim e f
    have hE : Function.Injective E := by
      rintro (i | i) (j | j) h
      · exact congrArg Sum.inl (e.injective h)
      · exact (hdisj i j h).elim
      · exact (hdisj j i h.symm).elim
      · exact congrArg Sum.inr (f.injective h)
    have h := Fintype.card_le_of_injective E hE
    simpa only [Fintype.card_sum,Fintype.card_fin,two_mul] using h
  obtain ⟨hcharge,hcover⟩ := two_chain_cover_conditions_of_logarithmic_third hm hsize hlong
  exact global_lower_bound_of_two_chain_cover hm g hg b x y e f hdisj he hf hcharge hcover

/-- Every original exact stratum is covered by the same two-chain
one-third cutoff, without any restriction on the other coordinates. -/
theorem stratum_lower_bound_of_two_logarithmically_long_affine_chains
    {n m s d : ℕ} (hd : Odd d) (hm : 4 ≤ m)
    (g : Fin n → ZMod (2^s*d)) (hg : ValidTuple g)
    (b x y : ZMod (2^s*d)) (e f : Fin m ↪ Fin n)
    (hdisj : ∀ i j, e i ≠ f j)
    (he : ∀ i, g (e i)+b=2^i.val • x) (hf : ∀ j, g (f j)+b=2^j.val • y)
    (hlong : n+2*Nat.log 2 n+5 ≤ 3*m) : stratumBound n s ≤ 2^s*d := by
  have hsize : 2*m ≤ n := by
    let E : Fin m ⊕ Fin m → Fin n := Sum.elim e f
    have hE : Function.Injective E := by
      rintro (i | i) (j | j) h
      · exact congrArg Sum.inl (e.injective h)
      · exact (hdisj i j h).elim
      · exact (hdisj j i h.symm).elim
      · exact congrArg Sum.inr (f.injective h)
    have h := Fintype.card_le_of_injective E hE
    simpa only [Fintype.card_sum,Fintype.card_fin,two_mul] using h
  obtain ⟨hcharge,hcover⟩ := two_chain_cover_conditions_of_logarithmic_third hm hsize hlong
  exact stratum_lower_bound_of_two_chain_cover hd hm g hg b x y e f hdisj he hf hcharge hcover

/-- Direct original G3 exclusion at the explicit two-chain cutoff. -/
theorem not_validTuple_exceptional_of_two_logarithmically_long_affine_chains
    {n m : ℕ} (hm : 4 ≤ m) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b x y : ZMod (2*globalBound (n-1))) (e f : Fin m ↪ Fin n)
    (hdisj : ∀ i j, e i ≠ f j)
    (he : ∀ i, g (e i)+b=2^i.val • x) (hf : ∀ j, g (f j)+b=2^j.val • y)
    (hlong : n+2*Nat.log 2 n+5 ≤ 3*m) : ¬ ValidTuple g := by
  intro hg
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  have h := global_lower_bound_of_two_logarithmically_long_affine_chains hm g hg b x y e f hdisj he hf hlong
  omega

end MinModulus
