import MinModulus.TwoChainPacking

/-! Boundary-coefficient rigidity extracts an actual one-escape map
when the complementary rival has enough weight capacity. This gives
full global and exact-stratum bounds for that class. Every deep positive
boundary relation has this capacity; arbitrary extraction remains open. -/

namespace MinModulus
open Finset

/-- A bounded positive endpoint relation has a dyadic coefficient
whenever its explicit complementary weights can be refined to full
length. A non-power complement saves the two extra top coins. -/
theorem power_coefficient_of_valid_two_chain_boundary
    {A L c : ℕ} (hA : 0 < A) (hc : 0 < c) (hcL : c < 2^L)
    (hcap : A+L ≤ (2^A-1+2^A)+(2^L-1-c))
    {G : Type*} [AddCommGroup G] (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hrel : 2^A • x=c • y) : ∃ e : ℕ, c=2^e := by
  by_contra hpow
  have hL2 : 2 ≤ L := by
    by_contra h
    have hle : 2^L ≤ 2^1 := Nat.pow_le_pow_right (by omega) (by omega)
    have hc1 : c=1 := by norm_num at hle; omega
    exact hpow ⟨0,by simp [hc1]⟩
  have hAp : 0 < 2^A := by positivity
  obtain ⟨p,hps,hp,hdp⟩ := exists_rep_le A (2^A-1) (by omega)
  obtain ⟨p',_,hp',hdp'⟩ := exists_binary_rep_add_two_top_coins hA p hps
  obtain ⟨q,_,hq,hdq⟩ := exists_rep_compl L c hcL (by omega) hpow
  have hsum : (2^A-1+2^A) • x+(2^L-1-c) • y=(2^A-1) • x+(2^L-1) • y := by
    rw [add_nsmul,hrel,add_assoc,← add_nsmul,Nat.add_sub_of_le (by omega)]
  exact not_validTuple_of_two_chain_integer_weights g x y hleft hright p' q
    (by rw [hp',hp]) hq (by omega) hcap (by omega) hsum hg

/-- If a left chain endpoint doubles to an actual right-chain entry,
the whole tuple has at most one escape. No arm-ordering premise is
needed; the prior geometry theorem handles the extracted actual map. -/
theorem one_escape_of_actual_two_chain_boundary
    {A L e : ℕ} (_hA : 0 < A) (hL : 0 < L) (he : e < L)
    {G : Type*} [AddCommGroup G] (g : Fin (A+L) → G) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hrel : 2^A • x=2^e • y) :
    ∃ a : Fin (A+L), ∀ i, i ≠ a → ∃ j, g j=2 • g i := by
  let a : Fin (A+L) := Fin.natAdd A ⟨L-1,by omega⟩
  refine ⟨a,?_⟩
  intro i hi
  refine Fin.addCases (fun i hi ↦ ?_) (fun i hi ↦ ?_) i hi
  · by_cases hn : i.val+1 < A
    · refine ⟨Fin.castAdd L ⟨i.val+1,hn⟩,?_⟩
      rw [hleft,hleft,← mul_nsmul,← pow_succ]
    · refine ⟨Fin.natAdd A ⟨e,he⟩,?_⟩
      rw [hright,hleft,← mul_nsmul,← pow_succ,show i.val+1=A by omega,hrel]
  · have hn : i.val+1 < L := by
      by_contra hnot
      apply hi
      apply congrArg (Fin.natAdd A)
      apply Fin.ext
      change i.val=L-1
      omega
    refine ⟨Fin.natAdd A ⟨i.val+1,hn⟩,?_⟩
    rw [hright,hright,← mul_nsmul,← pow_succ]

/-- A bounded boundary relation with sufficient explicit weight
capacity extracts actual one-escape closure, without assuming that
its coefficient is a power of two. -/
theorem one_escape_of_valid_two_chain_boundary_capacity
    {A L c : ℕ} (hA : 0 < A) (hL : 0 < L) (hc : 0 < c) (hcL : c < 2^L)
    (hcap : A+L ≤ (2^A-1+2^A)+(2^L-1-c))
    {G : Type*} [AddCommGroup G] (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hrel : 2^A • x=c • y) :
    ∃ a : Fin (A+L), ∀ i, i ≠ a → ∃ j, g j=2 • g i := by
  obtain ⟨e,he⟩ := power_coefficient_of_valid_two_chain_boundary hA hc hcL hcap g hg x y hleft hright hrel
  have heL : e < L := by
    by_contra h
    have hp : 2^L ≤ 2^e := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  exact one_escape_of_actual_two_chain_boundary hA hL heL g x y hleft hright (by simpa only [← he] using hrel)

/-- Full global closure of the boundary-capacity class, at every
positive cyclic modulus and without a unit or dyadic-coefficient input. -/
theorem global_lower_bound_of_valid_two_chain_boundary_capacity
    {A L c N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hc : 0 < c) (hcL : c < 2^L)
    (hcap : A+L ≤ (2^A-1+2^A)+(2^L-1-c))
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hrel : 2^A • x=c • y) : globalBound (A+L) ≤ N := by
  obtain ⟨a,ha⟩ := one_escape_of_valid_two_chain_boundary_capacity hA hL hc hcL hcap g hg x y hleft hright hrel
  exact global_lower_bound_of_valid_one_escape_affine_doubling (by omega) g hg a 0 (by simpa using ha)

/-- Every exact stratum also closes for the same actual boundary data. -/
theorem stratum_lower_bound_of_valid_two_chain_boundary_capacity
    {A L c s q : ℕ} (hq : Odd q) (hA : 0 < A) (hL : 0 < L) (hc : 0 < c) (hcL : c < 2^L)
    (hcap : A+L ≤ (2^A-1+2^A)+(2^L-1-c))
    (g : Fin (A+L) → ZMod (2^s*q)) (hg : ValidTuple g) (x y : ZMod (2^s*q))
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hrel : 2^A • x=c • y) : stratumBound (A+L) s ≤ 2^s*q := by
  obtain ⟨a,ha⟩ := one_escape_of_valid_two_chain_boundary_capacity hA hL hc hcL hcap g hg x y hleft hright hrel
  exact stratum_lower_bound_of_valid_one_escape_affine_doubling (by omega) hq g hg a 0 (by simpa using ha)

/-- A deep enough boundary arm pays the explicit weight capacity
automatically. This closes every bounded positive endpoint relation in
this range, not just already-dyadic coefficients. -/
theorem global_lower_bound_of_valid_deep_two_chain_boundary
    {A L c N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hc : 0 < c) (hcL : c < 2^L)
    (hdeep : A+L ≤ 2^A)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hrel : 2^A • x=c • y) : globalBound (A+L) ≤ N :=
  global_lower_bound_of_valid_two_chain_boundary_capacity hA hL hc hcL (by omega) g hg x y hleft hright hrel

/-- Affine/reindexed boundary data retain the full global and
every-stratum conclusions through the actual one-escape consumer. -/
theorem global_lower_bound_of_valid_affine_two_chain_boundary_capacity
    {A L c N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hc : 0 < c) (hcL : c < 2^L)
    (hcap : A+L ≤ (2^A-1+2^A)+(2^L-1-c))
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (A+L))) (b x y : ZMod N)
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hrel : 2^A • x=c • y) : globalBound (A+L) ≤ N := by
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  exact global_lower_bound_of_valid_two_chain_boundary_capacity hA hL hc hcL hcap _ hv x y hleft hright hrel

/-- The exact-stratum boundary theorem also retains arbitrary affine
offsets and permutations of the original tuple. -/
theorem stratum_lower_bound_of_valid_affine_two_chain_boundary_capacity
    {A L c s q : ℕ} (hq : Odd q) (hA : 0 < A) (hL : 0 < L) (hc : 0 < c) (hcL : c < 2^L)
    (hcap : A+L ≤ (2^A-1+2^A)+(2^L-1-c))
    (g : Fin (A+L) → ZMod (2^s*q)) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (A+L))) (b x y : ZMod (2^s*q))
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hrel : 2^A • x=c • y) : stratumBound (A+L) s ≤ 2^s*q := by
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  exact stratum_lower_bound_of_valid_two_chain_boundary_capacity hq hA hL hc hcL hcap _ hv x y hleft hright hrel

/-- Any bounded positive boundary relation in a hypothetical global
counterexample must have genuinely insufficient weight capacity. In
particular its boundary arm lies strictly below full dyadic depth. -/
theorem shallow_boundary_capacity_of_valid_below_globalBound
    {A L c N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hc : 0 < c) (hcL : c < 2^L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hrel : 2^A • x=c • y) (hsmall : N < globalBound (A+L)) :
    (2^A-1+2^A)+(2^L-1-c) < A+L ∧ 2^A < A+L := by
  have hcapa : (2^A-1+2^A)+(2^L-1-c) < A+L := by
    by_contra h
    have hb := global_lower_bound_of_valid_two_chain_boundary_capacity hA hL hc hcL (by omega) g hg x y hleft hright hrel
    omega
  exact ⟨hcapa,by omega⟩

end MinModulus
