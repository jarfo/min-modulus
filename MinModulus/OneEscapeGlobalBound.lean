import MinModulus.OneEscapeGeometry

/-!
# Full global and exact-stratum bounds for all one-escape tuples

Induction follows the actual half deletion supplied by a doubled pair,
retaining the exception and affine closure. Low strata and injective
doubling already satisfy the bound. Above the cutoff, the child bound
and the completed class-specific exceptional obstruction close the
numerical induction. No unrestricted conjectural input is assumed.

Consequently any counterexample to the global or exact-stratum bound
must have at least two escaping doubles for EVERY affine offset. This
is a necessary residual condition, not a proof that the residual is empty.
The same three unrestricted global gates remain open.
-/

namespace MinModulus

/-- Above the logarithmic cutoff, a half-child global bound lifts unless
the parent is the exceptional non-power boundary. This is numerical and
does not assume any unrestricted G1, G2, or G3 statement. -/
theorem globalBound_succ_le_of_high_stratum_half_bound
    {n s q : ℕ} (hn : 2 ≤ n) (hs : Nat.log 2 (n+1) < s+1)
    (hchild : globalBound n ≤ 2^s*q)
    (hboundary : 2^Nat.log 2 (n+1) ≠ n+1 → 2^s*q ≠ globalBound n) :
    globalBound (n+1) ≤ 2^(s+1)*q := by
  let m := Nat.log 2 (n+1)
  have hmle : m ≤ n := by have := Nat.log_lt_self 2 (by omega : n+1 ≠ 0); omega
  have hpow : 2^(n+1)=2*2^n := by rw [pow_succ']
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  by_cases hp : 2^m=n+1
  · have hmpos : 0 < m := by
      by_contra h
      have hm0 : m=0 := by omega
      simp only [hm0,pow_zero] at hp
      omega
    have hmform : m-1+1=m := by omega
    have hsplit : 2^m=2*2^(m-1) := by
      calc
        2^m=2^((m-1)+1) := congrArg (fun t ↦ 2^t) hmform.symm
        _=2*2^(m-1) := pow_succ' 2 (m-1)
    have hlow : 2^(m-1) ≤ n := by
      have ht : 0 < 2^(m-1) := by positivity
      omega
    have hhigh : n < 2^((m-1)+1) := by rw [hmform,hp]; omega
    have hlog : Nat.log 2 n=m-1 := Nat.log_eq_of_pow_le_of_lt_pow hlow hhigh
    have hstep : globalBound (n+1)=2*globalBound n := by
      unfold globalBound
      change 2^(n+1)-2^m=2*(2^n-2^Nat.log 2 n)
      rw [hlog,hpow,hsplit,Nat.mul_sub_left_distrib]
    rw [hstep,hN]
    exact Nat.mul_le_mul_left 2 hchild
  · have hlog : Nat.log 2 n=m :=
      (Nat.log_eq_log_succ_iff (b := 2) (n := n) (by omega) (by omega)).mpr hp
    have hstrict : globalBound n < 2^s*q := lt_of_le_of_ne hchild (Ne.symm (hboundary hp))
    have hms : m ≤ s := by dsimp [m]; omega
    have hdvdM : 2^m ∣ 2^s*q := dvd_mul_of_dvd_left (pow_dvd_pow 2 hms) q
    have hdvdC : 2^m ∣ globalBound n := by
      unfold globalBound
      rw [hlog]
      exact Nat.dvd_sub (pow_dvd_pow 2 hmle) (dvd_refl _)
    have hdiff : 2^m ≤ 2^s*q-globalBound n :=
      Nat.le_of_dvd (by omega) (Nat.dvd_sub hdvdM hdvdC)
    have hsum : globalBound n+2^m=2^n := by
      unfold globalBound
      rw [hlog]
      exact Nat.sub_add_cancel (Nat.pow_le_pow_right (by omega) hmle)
    have hb : 2^n ≤ 2^s*q := by omega
    have hdouble := Nat.mul_le_mul_left 2 hb
    unfold globalBound
    rw [hN,hpow]
    exact (Nat.sub_le _ _).trans hdouble

/-- Full global bound for EVERY one-escape tuple in every dyadic stratum.
Induction follows the actual half child and retains its closure; the
completed one-escape G3 theorem excludes the only exceptional boundary. -/
theorem global_lower_bound_of_valid_one_escape_all_strata
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (a : Fin n) (b : ZMod (2^s*q))
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b) : globalBound n ≤ 2^s*q := by
  induction s generalizing n with
  | zero =>
    exact global_lower_bound_of_valid_one_escape_low_stratum hq (by omega) g hg a b hclosed
  | succ s ih =>
    have hM : 0 < 2^s*q := mul_pos (by positivity) hq.pos
    letI : NeZero (2^s*q) := ⟨hM.ne'⟩
    letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
    by_cases hn2 : n=2
    · subst n
      have hi := Fintype.card_le_of_injective _ (validTuple_injective g hg)
      simpa [globalBound,ZMod.card,show Nat.log 2 2=1 by decide] using hi
    by_cases hs : s+1 ≤ Nat.log 2 n
    · exact global_lower_bound_of_valid_one_escape_low_stratum hq hs g hg a b hclosed
    by_cases hinj : Function.Injective (fun i ↦ 2 • g i)
    · exact global_lower_bound_of_valid_one_escape_doubling hn g hg a b
        (fun i _ j _ heq ↦ hinj heq) hclosed
    obtain ⟨u,v,heq,huv⟩ : ∃ u v, 2 • g u=2 • g v ∧ u ≠ v := by
      simpa [Function.Injective] using hinj
    cases n with
    | zero => omega
    | succ n =>
      have hnprev : 2 ≤ n := by omega
      have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
      obtain ⟨j,_,a',_,hv,hc⟩ :=
        exists_actual_one_escape_half_of_doubling_collision hN g hg a b hclosed u v huv heq
      have hb := ih hnprev _ hv a' _ hc
      apply globalBound_succ_le_of_high_stratum_half_bound hnprev (by omega) hb
      intro hp he
      have hactual : ∃ v : Fin (n+1) → ZMod (2^(s+1)*q), ∃ c : Fin (n+1),
          ∃ d : ZMod (2^(s+1)*q), ValidTuple v ∧ ∀ i, i ≠ c → ∃ j, v j=2 • v i+d :=
        ⟨g,a,b,hg,hclosed⟩
      rw [hN,he] at hactual
      obtain ⟨v,c,d,hv,hc⟩ := hactual
      exact not_validTuple_exceptional_of_one_escape_affine_doubling (by omega) hp v c d hc hv

/-- Unconditional global min-modulus bound for the full one-escape
affine-doubling class, at every positive cyclic modulus. -/
theorem global_lower_bound_of_valid_one_escape_affine_doubling
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (a : Fin n) (b : ZMod N)
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b) : globalBound n ≤ N := by
  obtain ⟨s,q,hq,rfl⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne N)
  exact global_lower_bound_of_valid_one_escape_all_strata hn hq g hg a b hclosed

/-- Every exact-stratum threshold now holds for ALL one-escape tuples,
with no cutoff, rank, geometry, or doubling-injectivity hypothesis. -/
theorem stratum_lower_bound_of_valid_one_escape_affine_doubling
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (a : Fin n) (b : ZMod (2^s*q))
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b) : stratumBound n s ≤ 2^s*q := by
  by_cases hs : s ≤ Nat.log 2 n
  · exact stratum_lower_bound_of_valid_one_escape_low_stratum hq hs g hg a b hclosed
  · have hb := global_lower_bound_of_valid_one_escape_all_strata hn hq g hg a b hclosed
    simpa only [stratumBound,min_eq_right (by omega : Nat.log 2 n ≤ s),globalBound] using hb

/-- Failing one-escape closure forces two genuinely distinct escaping
coordinates. The target relation is arbitrary; no group is needed. -/
theorem exists_two_escapes_of_no_one_escape
    {α : Type*} (a : α) (target : α → α → Prop)
    (hnot : ∀ c, ¬ (∀ i, i ≠ c → ∃ j, target i j)) :
    ∃ i j, i ≠ j ∧ (∀ k, ¬ target i k) ∧ ∀ k, ¬ target j k := by
  classical
  obtain ⟨i,_,hi⟩ : ∃ i, i ≠ a ∧ ∀ k, ¬ target i k := by simpa using hnot a
  obtain ⟨j,hji,hj⟩ : ∃ j, j ≠ i ∧ ∀ k, ¬ target j k := by simpa using hnot i
  exact ⟨i,j,hji.symm,hi,hj⟩

/-- Every hypothetical global counterexample has at least TWO actual
escaping doubles at EVERY affine offset. One-escape cases are removed
uniformly from the global frontier, not only at selected moduli. -/
theorem two_affine_doubling_escapes_of_valid_below_globalBound
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < globalBound n)
    (b : ZMod N) :
    ∃ i j, i ≠ j ∧ (∀ k, g k ≠ 2 • g i+b) ∧ ∀ k, g k ≠ 2 • g j+b := by
  apply exists_two_escapes_of_no_one_escape (⟨0,by omega⟩ : Fin n) (fun i j ↦ g j=2 • g i+b)
  intro a hc
  exact (not_lt_of_ge (global_lower_bound_of_valid_one_escape_affine_doubling hn g hg a b hc)) hsmall

/-- The same two-escape residual condition holds below EVERY exact
stratum threshold, including the sharper odd-stratum G2 threshold. -/
theorem two_affine_doubling_escapes_of_valid_below_stratumBound
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (hsmall : 2^s*q < stratumBound n s) (b : ZMod (2^s*q)) :
    ∃ i j, i ≠ j ∧ (∀ k, g k ≠ 2 • g i+b) ∧ ∀ k, g k ≠ 2 • g j+b := by
  apply exists_two_escapes_of_no_one_escape (⟨0,by omega⟩ : Fin n) (fun i j ↦ g j=2 • g i+b)
  intro a hc
  exact (not_lt_of_ge (stratum_lower_bound_of_valid_one_escape_affine_doubling hn hq g hg a b hc)) hsmall

end MinModulus
