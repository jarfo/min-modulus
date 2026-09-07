import MinModulus.TwoChainSlackClosure

/-! Complete actual two-escape G1 closure in every dimension. General
parity/deficit arithmetic closes the transition, tuple-local cube packing
closes the four-coordinate base, and an actual embedded multiplier chain
closes length five. The equivalent all-offset three-escape G1 frontier
feeds the existing global induction with exactly the same G2/G3 gates. -/

namespace MinModulus

open Finset

/-- Exact even-stratum criticality leaves a strict four-unit binary
gap. The lowest stratum also uses its odd cofactor, not merely N even. -/
theorem four_lt_binary_deficit_of_critical_even_stratum
    {n s q : ℕ} (hn : 4 ≤ n) (hq : Odd q)
    (hc : 2^(s+1)*q < stratumBound n (s+1)) : 2^(s+1)*q+4 < 2^n := by
  have hlog : 2 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) (by simpa using hn)
  by_cases hs : s=0
  · subst s
    have hc' : 2*q < 2^n-2 := by simpa [stratumBound,min_eq_left (by omega : 1 ≤ Nat.log 2 n)] using hc
    have hd : 4 ∣ 2^n := by
      change 2^2 ∣ 2^n
      exact pow_dvd_pow (2 : ℕ) (by omega : 2 ≤ n)
    obtain ⟨v,hv⟩ := hd
    obtain ⟨r,hr⟩ := hq
    norm_num only [Nat.reduceAdd,Nat.reducePow]
    omega
  · have hm : 2 ≤ min (s+1) (Nat.log 2 n) := by omega
    have hp : 4 ≤ 2^min (s+1) (Nat.log 2 n) := by
      simpa using (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm)
    unfold stratumBound at hc
    omega

/-- The bounded transition dimensions use parity, not a tuple census:
an even small corner exceeds a relation side by at most four. -/
theorem small_even_corner_area_le_max_add_four_of_le_eight
    {A L a b : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 6 ≤ A+L) (hn8 : A+L ≤ 8)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (hs : a+b ≤ A+L+1) (he : Even (a+b)) :
    a*b ≤ max (2^A-a) (2^L-b)+4 := by
  have aux : ∀ A L a b : ℕ, 0 < A → 0 < L → 6 ≤ A+L → A+L ≤ 8 → A ≤ L →
      0 < a → a < 2^A → 0 < b → b < 2^L → a+b ≤ A+L+1 → Even (a+b) →
      a*b ≤ max (2^A-a) (2^L-b)+4 := by
    intro A L a b hA hL hn hn8 hAL ha0 ha hb0 hb hs he
    by_cases hL5 : 5 ≤ L
    · have hp : 32 ≤ 2^L := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hL5
      have hsum : (a+b+1)^2 ≤ 10^2 := Nat.pow_le_pow_left (by omega) 2
      have hh : a*b+b ≤ 25 := by nlinarith only [hsum,sq_nonneg ((a : ℤ)+1-b)]
      have hle : a*b ≤ 2^L-b+4 := by omega
      exact hle.trans (Nat.add_le_add_right (le_max_right _ _) 4)
    · by_cases hlt : A < L
      · have hL4 : L=4 := by omega
        subst L
        have hsum : (a+b+1)^2 ≤ 9^2 := Nat.pow_le_pow_left (by omega) 2
        have hh : a*b+b ≤ 20 := by nlinarith only [hsum,sq_nonneg ((a : ℤ)+1-b)]
        have hle : a*b ≤ 2^4-b+4 := by norm_num; omega
        exact hle.trans (Nat.add_le_add_right (le_max_right _ _) 4)
      · have hEq : A=L := by omega
        subst L
        have hAb : A=3 ∨ A=4 := by omega
        obtain ⟨t,ht⟩ := he
        have hsum : a+b ≤ 2*A := by omega
        have hsq : (a+b)^2 ≤ (2*A)^2 := Nat.pow_le_pow_left hsum 2
        have hab : a*b ≤ A^2 := by nlinarith only [hsq,sq_nonneg ((a : ℤ)-b)]
        have hm1 := min_le_left a b
        have hm2 := min_le_right a b
        have hm : min a b ≤ A := by omega
        have hmax : max (2^A-a) (2^A-b)=2^A-min a b := by omega
        rw [hmax]
        rcases hAb with rfl | rfl <;> norm_num at ha hb hab ⊢ <;> omega
  rcases le_total A L with hAL | hLA
  · exact aux A L a b hA hL hn hn8 hAL ha0 ha hb0 hb hs he
  · have hh := aux L A b a hL hA (by omega) (by omega) hLA hb0 hb ha0 ha
      (by omega) (by simpa only [Nat.add_comm] using he)
    simpa only [Nat.mul_comm,max_comm] using hh

/-- The parity-controlled transition and the dyadic tail combine into
one uniform four-unit area estimate in all dimensions at least six. -/
theorem small_even_dyadic_corner_area_le_max_add_four
    {A L a b : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 6 ≤ A+L)
    (ha0 : 0 < a) (ha : a < 2^A) (hb0 : 0 < b) (hb : b < 2^L)
    (hs : a+b ≤ A+L+1) (he : Even (a+b))
    (hp : (∃ e, a=2^e) ∨ ∃ e, b=2^e) : a*b ≤ max (2^A-a) (2^L-b)+4 := by
  by_cases hn9 : 9 ≤ A+L
  · have hh := small_dyadic_corner_area_le_max_relation hA hL hn9 ha0 ha hb0 hb hs hp
    omega
  · exact small_even_corner_area_le_max_add_four_of_le_eight hA hL hn (by omega)
      ha0 ha hb0 hb hs he

/-- DIRECT G1 half descent for every critical actual two-escape tuple
in parent dimension at least SIX. The bounded transition uses extracted
corner parity and a general exact-stratum gap, with no finite census. -/
theorem admitsValidTuple_half_of_critical_two_escape_six_le
    {n s q : ℕ} (hq : Odd q) (hn : 5 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (B : Finset (Fin (n+1))) (hB : B.card ≤ 2) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ B → ∃ j, g j=2 • g i+b) : AdmitsValidTuple n (2^s*q) := by
  by_contra hnohalf
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨A,L,hA,hL,hsize,E,x,y,_,_,hleft,hright,a,c,ha0,ha,hc0,hc,hs,he,_,hp,hzero⟩ :=
    exists_interior_odd_seed_corner_of_critical_two_escape_without_half hq hn
      g hg hcritical B hB b hclosed hnohalf
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  have hgap := four_lt_binary_deficit_of_critical_even_stratum (by omega : 4 ≤ n+1) hq hcritical
  have harea := small_even_dyadic_corner_area_le_max_add_four hA hL (by omega)
    ha0 ha hc0 hc (by omega) he hp
  have hmax : 0 < max (2^A-a) (2^L-c) := lt_of_lt_of_le (by omega : 0 < 2^A-a) (le_max_left _ _)
  have hN : 2^(s+1)*q < 2^(A+L) := by rw [hsize]; omega
  have hslack : 2^(s+1)*q+a*c-2^(A+L) < max (2^A-a) (2^L-c) := by rw [hsize]; omega
  obtain ⟨z,hz⟩ := one_escape_of_valid_two_chain_slack_lt_max_relation hA hL (by omega)
    ha0 ha hc0 hc _ hv x y hleft hright hN hzero hslack
  have hb := stratum_lower_bound_of_valid_one_escape_affine_doubling (by omega) hq _ hv z 0
    (by simpa only [add_zero] using hz)
  rw [hsize] at hb
  omega

/-- A double of an anchored difference stays outside the subset cube
under injectivity only on the ACTUAL tuple doubles, not on the group. -/
theorem ssum_ne_double_diff_of_tuple_doubling_injective
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m+1) → G) (hg : ValidTuple g)
    (hi : Function.Injective (fun i ↦ 2 • g i)) (T : Finset (Fin m)) (i : Fin m) :
    ssum g T ≠ (2 : ℤ) • diff g i := by
  classical
  intro h
  rcases T.eq_empty_or_nonempty with rfl | hT
  · rw [ssum,sum_empty] at h
    have hz : 2 • g i.succ=2 • g 0 := by
      have hh : (2 : ℤ) • g i.succ=(2 : ℤ) • g 0 := by
        apply sub_eq_zero.mp
        simpa only [diff,smul_sub] using h.symm
      simpa only [two_zsmul,two_nsmul] using hh
    exact Fin.succ_ne_zero i (hi hz)
  · refine validTuple_no_diff_relation g hg
      (d := fun j => (if j=i then 2 else 0)-(if j ∈ T then 1 else 0)) ?_ ?_ ?_ ?_
    · intro h0
      have hh := congrFun h0 i
      by_cases hiT : i ∈ T <;> simp [hiT] at hh
    · intro j
      show (-1 : ℤ) ≤ (if j=i then 2 else 0)-(if j ∈ T then 1 else 0)
      split_ifs <;> omega
    · have hh : (∑ j, ((if j=i then (2 : ℤ) else 0)-(if j ∈ T then 1 else 0)))=2-T.card := by
        rw [sum_sub_distrib,sum_ite_eq' univ i fun _ ↦ (2 : ℤ)]
        simp
      rw [hh]
      have hc : 1 ≤ T.card := card_pos.mpr hT
      omega
    · have hh : ∀ j, ((if j=i then (2 : ℤ) else 0)-(if j ∈ T then 1 else 0)) • diff g j=
          (if j=i then (2 : ℤ) else 0) • diff g j-(if j ∈ T then (1 : ℤ) else 0) • diff g j :=
        fun j ↦ sub_smul _ _ _
      rw [sum_congr rfl fun j _ ↦ hh j,sum_sub_distrib,sum_single_smul,sum_indicator_smul]
      rw [← ssum,← h,sub_self]

/-- A local doubling hypothesis already supplies a full m-element layer
outside the anchored cube, in any finite abelian group. -/
theorem card_ge_cube_add_doubles_of_tuple_doubling_injective
    {m : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin (m+1) → G) (hg : ValidTuple g)
    (hi : Function.Injective (fun i ↦ 2 • g i)) : 2^m+m ≤ Fintype.card G := by
  classical
  let φ : Finset (Fin m) ⊕ Fin m → G := Sum.elim (ssum g) (fun i ↦ (2 : ℤ) • diff g i)
  have hφ : Function.Injective φ := by
    intro p q hpq
    rcases p with T | i <;> rcases q with U | j <;>
      simp only [φ,Sum.elim_inl,Sum.elim_inr] at hpq
    · exact congrArg Sum.inl (ssum_injective g hg hpq)
    · exact (ssum_ne_double_diff_of_tuple_doubling_injective g hg hi T j hpq).elim
    · exact (ssum_ne_double_diff_of_tuple_doubling_injective g hg hi U i hpq.symm).elim
    · have hh : 2 • g i.succ=2 • g j.succ := by
        have hz : (2 : ℤ) • g i.succ=(2 : ℤ) • g j.succ := by
          apply add_right_cancel (b := -((2 : ℤ) • g 0))
          simpa only [diff,smul_sub,sub_eq_add_neg,smul_add,smul_neg] using hpq
        simpa only [two_zsmul,two_nsmul] using hz
      exact congrArg Sum.inr (Fin.succ_injective _ (hi hh))
  have hh := Fintype.card_le_of_injective φ hφ
  simpa only [Fintype.card_sum,Fintype.card_finset,Fintype.card_fin] using hh

/-- The four-coordinate G1 base is unconditional, with no escape-count
assumption: a failed half deletion would supply eleven distinct residues
but exact criticality permits fewer than twelve in an even group. -/
theorem admitsValidTuple_half_of_critical_length_four
    {s q : ℕ} (hq : Odd q)
    (g : Fin 4 → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound 4 (s+1)) : AdmitsValidTuple 3 (2^s*q) := by
  by_contra hnohalf
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hM : 0 < 2^s*q := mul_pos (by positivity) hq.pos
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  have hi : Function.Injective (fun i ↦ 2 • g i) := by
    apply doubling_injective_of_no_common_touched_witness g hg (half_add_half hN)
      (half_ne_zero hN hM) (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hN u hu)
    rintro ⟨j,hj⟩
    exact hnohalf (exists_validTuple_half_of_delete hN hM hg j hj)
  have hb := card_ge_cube_add_doubles_of_tuple_doubling_injective g hg hi
  have hgap := four_lt_binary_deficit_of_critical_even_stratum (by decide : 4 ≤ 4) hq hc
  norm_num only [Nat.reducePow,ZMod.card] at hb hgap
  omega

/-- An ACTUAL chain covering all but two coordinates has the completed
exact-stratum bound, for any seed multiplier including nonunits. -/
theorem stratum_lower_bound_of_valid_embedded_two_extra_chain
    {m s q : ℕ} (hm : 3 ≤ m) (hq : Odd q)
    (g : Fin (m+2) → ZMod (2^s*q)) (hg : ValidTuple g)
    (e : Fin m ↪ Fin (m+2)) (x b : ZMod (2^s*q))
    (hchain : ∀ i : Fin m, g (e i)+b=2^i.val • x) : stratumBound (m+2) s ≤ 2^s*q := by
  obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin m ↦ i.castSucc.castSucc) e
    (by
      intro i j he
      have hv := congrArg (fun k : Fin (m+2) ↦ k.val) he
      exact Fin.ext hv) e.injective
  apply stratum_lower_bound_of_valid_scaled_fixed_short_prefix hm hq g hg P x (x-b)
  intro i
  rw [hP]
  have hpos : 0 < 2^i.val := by positivity
  have hp : (a i.val : ZMod (2^s*q))=(2 : ZMod (2^s*q))^i.val-1 := by
    rw [a,Nat.cast_sub (by omega : 1 ≤ 2^i.val)]
    simp
  calc
    g (e i)=2^i.val • x-b := eq_sub_of_add_eq (hchain i)
    _=x*(a i.val : ZMod (2^s*q))+(x-b) := by rw [nsmul_eq_mul,hp]; push_cast; ring

/-- Five-coordinate two-escape G1 closure. Failure of half descent
extracts two actual chains; one has at least three terms and is consumed
by the already proved two-extra multiplier theorem. -/
theorem admitsValidTuple_half_of_critical_two_escape_length_five
    {s q : ℕ} (hq : Odd q)
    (g : Fin 5 → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound 5 (s+1))
    (B : Finset (Fin 5)) (hB : B.card ≤ 2) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ B → ∃ j, g j=2 • g i+b) : AdmitsValidTuple 4 (2^s*q) := by
  by_contra hnohalf
  obtain ⟨A,L,hA,hL,hsize,E,x,y,hleft,hright,_,_⟩ :=
    exists_two_affine_chains_of_critical_two_escape_without_half hq (by decide : 3 ≤ 4)
      g hg hc B hB b hclosed hnohalf
  have hlong : 3 ≤ A ∨ 3 ≤ L := by omega
  rcases hlong with hA3 | hL3
  · let e : Fin 3 ↪ Fin 5 :=
      ⟨fun i ↦ E (Fin.castAdd L ⟨i.val,by omega⟩),by
        intro i j he
        have hh := congrArg Fin.val (E.injective he)
        exact Fin.ext hh⟩
    have hchain : ∀ i : Fin 3, g (e i)+b=2^i.val • x := by
      intro i; exact hleft ⟨i.val,by omega⟩
    have hb := stratum_lower_bound_of_valid_embedded_two_extra_chain (by decide : 3 ≤ 3)
      hq g hg e x b hchain
    norm_num only [Nat.reduceAdd] at hb
    omega
  · let e : Fin 3 ↪ Fin 5 :=
      ⟨fun i ↦ E (Fin.natAdd A ⟨i.val,by omega⟩),by
        intro i j he
        have hh := congrArg Fin.val (E.injective he)
        apply Fin.ext
        change A+i.val=A+j.val at hh
        omega⟩
    have hchain : ∀ i : Fin 3, g (e i)+b=2^i.val • y := by
      intro i; exact hright ⟨i.val,by omega⟩
    have hb := stratum_lower_bound_of_valid_embedded_two_extra_chain (by decide : 3 ≤ 3)
      hq g hg e y b hchain
    norm_num only [Nat.reduceAdd] at hb
    omega

/-- COMPLETE actual two-escape G1 closure in EVERY parent dimension.
No corner, seed parity, generation, child induction or G2/G3 hypothesis
is supplied. Only the original critical tuple and actual affine closure
off at most two coordinates remain. -/
theorem admitsValidTuple_half_of_critical_two_escape
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (B : Finset (Fin (n+1))) (hB : B.card ≤ 2) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ B → ∃ j, g j=2 • g i+b) : AdmitsValidTuple n (2^s*q) := by
  by_cases hn5 : 5 ≤ n
  · exact admitsValidTuple_half_of_critical_two_escape_six_le hq hn5 g hg hc B hB b hclosed
  · by_cases hn3 : n ≤ 2
    · letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
      have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
      have small : ∀ N : ℕ, N=2*(2^s*q) → ∀ v : Fin (n+1) → ZMod N,
          ValidTuple v → AdmitsValidTuple n (2^s*q) := by
        intro N hN v hv
        subst N
        exact admitsValidTuple_half_of_length_le_three hn3 v hv
      exact small _ hN g hg
    · have hcases : n=3 ∨ n=4 := by omega
      rcases hcases with rfl | rfl
      · exact admitsValidTuple_half_of_critical_length_four hq g hg hc
      · exact admitsValidTuple_half_of_critical_two_escape_length_five hq g hg hc B hB b hclosed

/-- The new original-G1 frontier: failure of half descent forces at
least THREE genuine escaping doubles at EVERY affine offset. -/
theorem three_le_affine_escape_card_of_critical_without_half
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    ∀ b : ZMod (2^(s+1)*q),
      3 ≤ (Finset.univ.filter (fun i ↦ ∀ j, g j ≠ 2 • g i+b)).card := by
  classical
  intro b
  by_contra hnot
  let B := Finset.univ.filter (fun i ↦ ∀ j, g j ≠ 2 • g i+b)
  change ¬ 3 ≤ B.card at hnot
  have hB : B.card ≤ 2 := by omega
  apply hnohalf
  apply admitsValidTuple_half_of_critical_two_escape hq g hg hc B hB b
  intro i hi
  have hh : ¬ ∀ j, g j ≠ 2 • g i+b := by
    intro h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i,h⟩)
  push Not at hh
  exact hh

/-- The SAME remaining primitive G1 gate, restricted to parents of
length at least five with at least three ACTUAL affine escapes at every
offset. Equivalence below consumes all excluded cases unconditionally. -/
def PrimitiveThreeEscapeDeleteStep : Prop :=
  ∀ {n s q : ℕ}, 4 ≤ n → Odd q →
    ∀ g : Fin (n+1) → ZMod (2^(s+1)*q), ValidTuple g →
      2^(s+1)*q < stratumBound (n+1) (s+1) →
      WitnessThreeDistinctOmissions g ((2^s*q : ℕ) : ZMod (2^(s+1)*q)) →
      (∀ (j : Fin (n+1)) (a : Fin n), AddSubgroup.closure
        (Set.range (fun i : Fin n ↦ g (j.succAbove i)-g (j.succAbove a)))=⊤) →
      (∀ b : ZMod (2^(s+1)*q),
        3 ≤ (Finset.univ.filter (fun i ↦ ∀ j, g j ≠ 2 • g i+b)).card) →
      AdmitsValidTuple n (2^s*q)

/-- No new global gate is introduced: the three-escape restriction is
equivalent to the existing primitive three-omission G1 input. -/
theorem primitiveThreeOmissionDeleteStep_iff_threeEscape :
    PrimitiveThreeOmissionDeleteStep ↔ PrimitiveThreeEscapeDeleteStep := by
  constructor
  · intro h n s q hn hq g hg hc hthree hfull _
    exact h (by omega) hq g hg hc hthree hfull
  · intro h n s q hn hq g hg hc hthree hfull
    by_cases hn4 : 4 ≤ n
    · by_contra hnohalf
      exact hnohalf (h hn4 hq g hg hc hthree hfull
        (three_le_affine_escape_card_of_critical_without_half hq g hg hc hnohalf))
    · have hn3 : n=3 := by omega
      subst n
      exact admitsValidTuple_half_of_critical_length_four hq g hg hc

/-- The refined G1 frontier feeds the EXISTING strong-dimension
induction with exactly the same G2/G3 inputs and no child-bound premise. -/
theorem stratum_lower_bound_of_primitive_threeEscapeDeleteStep
    (hG1 : PrimitiveThreeEscapeDeleteStep) (hG2 : OddStratumLowerBound)
    (hG3 : ExceptionalLiftObstruction)
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q) (hv : AdmitsValidTuple n (2^s*q)) :
    stratumBound n s ≤ 2^s*q :=
  stratum_lower_bound_of_primitive_threeOmissionDeleteStep
    (primitiveThreeOmissionDeleteStep_iff_threeEscape.mpr hG1) hG2 hG3 hn hq hv

/-- The direct Conjecture-1 route now needs only the all-offset
three-escape primitive G1 residual, plus the SAME two remaining gates. -/
theorem global_lower_bound_of_primitive_threeEscapeDeleteStep
    (hG1 : PrimitiveThreeEscapeDeleteStep) (hG2 : OddStratumLowerBound)
    (hG3 : ExceptionalLiftObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) : globalBound n ≤ N :=
  global_lower_bound_of_primitive_threeOmissionDeleteStep
    (primitiveThreeOmissionDeleteStep_iff_threeEscape.mpr hG1) hG2 hG3 hn hN hv

end MinModulus

