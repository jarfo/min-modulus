import MinModulus.ChainForestProfileEndpoints

/-! Repeated small boundary relations exclude strictly lower axis bases
above length 24. A coexisting strip must have zero boundary and a
length-one arm. In even cyclic groups, two compatible strips cannot
coexist with a no-overflow profile. The global conjecture remains open. -/

namespace MinModulus
open Finset

/-- A binary interval fitting below two widths has a representation
with the smaller width's coin budget, padded to the requested chain. -/
theorem exists_rep_with_smaller_coin_budget (L w z : ℕ)
    (hzL : z < 2^L) (hzw : z < 2^w) :
    ∃ u, val L u=z ∧ dsum L u ≤ w := by
  obtain ⟨u,hu,hv,hc⟩ := exists_rep_le (min L w) z (by
    rcases le_total L w with h | h
    · simpa only [Nat.min_eq_left h] using hzL
    · simpa only [Nat.min_eq_right h] using hzw)
  refine ⟨u,?_,?_⟩
  · rw [val_pad (Nat.min_le_left _ _) hu,hv]
  · rw [dsum_pad (Nat.min_le_left _ _) hu]
    exact hc.trans (Nat.min_le_right _ _)

/-- Above length 24, one third of the length minus two binary digits
can represent every weight below twice the length. -/
theorem twice_length_lt_third_budget_pow {n : ℕ} (hn : 24 ≤ n) :
    2*n < 2^(n/3-2) := by
  have haux : ∀ q, 8 ≤ q → 6*(q+1) < 2^(q-2) := by
    intro q hq
    induction q, hq using Nat.le_induction with
    | base => norm_num
    | succ q hq ih =>
      have hp : 2^(q+1-2)=2*2^(q-2) := by
        rw [show q+1-2=(q-2)+1 by omega,pow_succ']
      rw [hp]
      nlinarith
  have hq : 8 ≤ n/3 := by omega
  have hh := haux (n/3) hq
  omega

/-- Multiples of a chain boundary cost exactly twice the multiplier. -/
theorem exists_rep_boundary_multiple {L : ℕ} (hL : 0 < L) (m : ℕ) :
    ∃ u, val L u=m*2^L ∧ dsum L u=2*m := by
  let u : ℕ → ℕ := fun i ↦ if i=L-1 then 2*m else 0
  refine ⟨u,?_,?_⟩
  · simp only [val,u,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_range,show L-1<L by omega,if_true]
    have hp : 2^L=2*2^(L-1) := by
      calc
        _=2^((L-1)+1) := by congr 1; omega
        _=_ := pow_succ' _ _
    rw [hp]
    ring
  · simp only [dsum,u,Finset.sum_ite_eq',Finset.mem_range,show L-1<L by omega,if_true]

/-- A small axis target and a zero relation of weight at least three
force a rival, allowing the dominant coefficient to be zero. -/
theorem not_validTuple_of_small_axis_target_and_boundary_step
    {n : ℕ} (hn : 24 ≤ n) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a : β) (haj : a ≠ j) (hwidth : 2*n ≤ 2^(L j))
    (c h : ℕ) (hstep : 3 ≤ 2^(L a)+c) (hh : 0 < h) (hsmall : 2^(L a)+c+h ≤ n)
    (hzero : 2^(L a) • x a+c • x j=0)
    (htarget : (∑ i, (2^(L i)-1) • x i)=(h-1) • x j) :
    ¬ ValidTuple g := by
  classical
  let D := 2^(L a)+c
  let m := n/D+1
  let t := m*c+(h-1)
  have hKa : 2 ≤ 2^(L a) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) (hL a)
  have hD : 3 ≤ D := by dsimp [D]; omega
  have hmp : 0 < m := Nat.zero_lt_succ _
  have hdiv := Nat.div_add_mod n D
  have hmod := Nat.mod_lt n (by omega : 0 < D)
  have hmul : n < m*D ∧ m*D ≤ n+D := by
    constructor
    · dsimp only [m]; nlinarith
    · calc
        _=(n/D)*D+D := by dsimp only [m]; ring
        _≤n+D := Nat.add_le_add_right (Nat.div_mul_le_self n D) D
  have hthird : m ≤ n/3+1 := by
    have hprod := Nat.div_mul_le_self n D
    have hh : 3*(n/D) ≤ n := by nlinarith
    dsimp [m]
    omega
  have htotal : n ≤ m*2^(L a)+t ∧ m*2^(L a)+t < 2*n := by
    have hiden : m*2^(L a)+t=m*D+(h-1) := by dsimp [t,D]; ring
    rw [hiden]
    dsimp only [D] at hmul
    dsimp only [D]
    omega
  have ht : t < 2*n := by omega
  obtain ⟨uj,huj,hcj⟩ := exists_rep_with_smaller_coin_budget (L j) (n/3-2) t
    (by omega) (ht.trans (twice_length_lt_third_budget_pow hn))
  obtain ⟨ua,hua,hca⟩ := exists_rep_boundary_multiple (hL a) m
  let X : β → ℕ := fun i ↦ if i=j then t else if i=a then m*2^(L a) else 0
  let u : β → ℕ → ℕ := fun i ↦ if i=j then uj else if i=a then ua else fun _ ↦ 0
  have hu : ∀ i, val (L i) (u i)=X i := by
    intro i
    by_cases hij : i=j
    · subst i; simpa only [u,X,if_true] using huj
    · by_cases hia : i=a
      · subst i; simpa only [u,X,if_neg haj,if_true] using hua
      · simp [u,X,hij,hia,val]
  have hcost : (∑ i, dsum (L i) (u i)) ≤ n := by
    have he : (∑ i, dsum (L i) (u i))=dsum (L j) uj+dsum (L a) ua := by
      calc
        _ = ∑ i, ((if i=j then dsum (L j) uj else 0)+(if i=a then dsum (L a) ua else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hij : i=j
          · subst i; simp [u,Ne.symm haj]
          · by_cases hia : i=a
            · subst i; simp [u,haj]
            · simp [u,hij,hia,dsum]
        _ = _ := by simp [Finset.sum_add_distrib]
    rw [he,hca]
    omega
  have hpoint : ∀ i, X i=(if i=j then t else 0)+(if i=a then m*2^(L a) else 0) := by
    intro i
    by_cases hij : i=j
    · subst i; simp [X,Ne.symm haj]
    · by_cases hia : i=a
      · subst i; simp [X,haj]
      · simp [X,hij,hia]
  have hhigh : n ≤ ∑ i, X i := by
    simpa [hpoint,Finset.sum_add_distrib,add_comm] using htotal.1
  have hneq : ∃ i, X i ≠ 2^(L i)-1 := by
    refine ⟨a,?_⟩
    simp only [X,if_neg haj,if_true]
    have hh : 2^(L a) ≤ m*2^(L a) := by nlinarith
    omega
  have hsum : (∑ i, X i • x i)=∑ i, (2^(L i)-1) • x i := by
    rw [htarget]
    have he : m • (2^(L a) • x a+c • x j)=0 := by rw [hzero,smul_zero]
    calc
      _=t • x j+(m*2^(L a)) • x a := by simp [hpoint,add_nsmul,ite_smul,Finset.sum_add_distrib]
      _=m • (2^(L a) • x a+c • x j)+(h-1) • x j := by
        simp only [t,add_nsmul,smul_add,smul_smul]; abel
      _=_ := by rw [he,zero_add]
  exact not_validTuple_of_chain_forest_integer_weights L X g E x b hchain u hu hcost hhigh hneq hsum

/-- The positive dominant-coefficient case of the repeated boundary step. -/
theorem not_validTuple_of_small_axis_target_and_negative_boundary
    {n : ℕ} (hn : 24 ≤ n) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a : β) (haj : a ≠ j) (hwidth : 2*n ≤ 2^(L j))
    (c h : ℕ) (hc : 0 < c) (hh : 0 < h) (hsmall : 2^(L a)+c+h ≤ n)
    (hzero : 2^(L a) • x a+c • x j=0)
    (htarget : (∑ i, (2^(L i)-1) • x i)=(h-1) • x j) :
    ¬ ValidTuple g := by
  have hKa : 2 ≤ 2^(L a) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) (hL a)
  exact not_validTuple_of_small_axis_target_and_boundary_step hn L hL g E x b hchain j a haj hwidth c h
    (by omega) hh hsmall hzero htarget

/-- At length at least 24, an actual axis profile cannot lie strictly
below a compatible strip when the dominant width is at least twice n. -/
theorem not_lower_axis_profile_of_compatible_strip
    {n : ℕ} (hn : 24 ≤ n) {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j : β) (hwidth : 2*n ≤ 2^(L j))
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (hcompat : ∀ i, i ≠ j → Even (w i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val)
    (hvz : ∀ i, i ≠ j → (v i).val=0) :
    ¬ (v j).val < (w j).val := by
  classical
  intro hlt
  obtain ⟨haj,hwa,hwz,e,he,hbudget⟩ := compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j (by omega) w hw hcompat a ha
  have hrel := axis_profile_strip_boundary_relation L x j a haj w v hw hv hwa hwz hvz
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have htarget : (∑ i, (2^(L i)-1) • x i)=(v j).val • x j := by
    rw [← hvm.2]
    apply Finset.sum_eq_single j
    · intro i _ hij; rw [hvz i hij,zero_nsmul]
    · simp
  let c := (w j).val-(v j).val
  have hc : 0 < c := by dsimp only [c]; omega
  have hsum : c+((v j).val+1)=(w j).val+1 := by dsimp only [c]; omega
  have hzero : 2^(L a) • x a+c • x j=0 := by
    apply add_right_cancel (b := ((v j).val+1) • x j)
    calc
      _=2^(L a) • x a+(c+((v j).val+1)) • x j := by simp only [add_nsmul]; abel
      _=((v j).val+1) • x j := by rw [hsum]; exact hrel
      _=0+((v j).val+1) • x j := (zero_add _).symm
  exact not_validTuple_of_small_axis_target_and_negative_boundary hn L hL g E x b hchain j a haj hwidth
    c ((v j).val+1) hc (Nat.zero_lt_succ _) (by omega) hzero (by simpa using htarget) hg

/-- For genuine wide forests above length 24, an axis base and a
compatible strip have equal heights and the strip boundary is zero. -/
theorem axis_profile_and_compatible_strip_equal_zero_boundary
    {n : ℕ} (hn : 24 ≤ n) {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hwidth : 2*n ≤ 2^(L j))
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (hcompat : ∀ i, i ≠ j → Even (w i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val)
    (hvz : ∀ i, i ≠ j → (v i).val=0) :
    (v j).val=(w j).val ∧ 2^(L a) • x a=0 := by
  have hle := axis_profile_height_le_compatible_strip_height hr L hL hwide g hg E x b hchain hgen j (by omega) w v hw hv hcompat a ha hvz
  have hnlt := not_lower_axis_profile_of_compatible_strip hn hr L hL g hg E x b hchain j hwidth w v hw hv hcompat a ha hvz
  have heq : (v j).val=(w j).val := by omega
  obtain ⟨haj,hwa,hwz,_,_,_⟩ := compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j (by omega) w hw hcompat a ha
  have hrel := axis_profile_strip_boundary_relation L x j a haj w v hw hv hwa hwz hvz
  refine ⟨heq,?_⟩
  apply add_right_cancel (b := ((v j).val+1) • x j)
  simpa only [heq,zero_add] using hrel

/-- In a group with at most one nonzero element of order two, two
 distinct genuine chain boundaries cannot both vanish. -/
theorem genuine_forest_zero_boundary_unique
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (h : G) (htors : ∀ z : G, 2 • z=0 → z=0 ∨ z=h)
    (a c : β) (ha : 2^(L a) • x a=0) (hc : 2^(L c) • x c=0) : a=c := by
  let last : β → Fin n := fun i ↦ E ⟨i,⟨L i-1,by have := hL i; omega⟩⟩
  have hd : ∀ i, 2 • (g (last i)+b)=2^(L i) • x i := by
    intro i
    rw [hchain i ⟨L i-1,by have := hL i; omega⟩,smul_smul]
    congr 1
    calc
      _=2^((L i-1)+1) := (pow_succ' _ _).symm
      _=_ := by congr 1; have := hL i; omega
  have hz : ∀ i, g (last i)+b ≠ 0 := by
    intro i he
    apply hgen i (last i)
    apply add_right_cancel (b := b)
    calc
      _=0 := he
      _=(g (last i)+b)+(g (last i)+b) := by rw [he,add_zero]
      _=(2 • g (last i)+b)+b := by simp only [two_nsmul]; abel
  have hea : g (last a)+b=h := (htors _ ((hd a).trans ha)).resolve_left (hz a)
  have hec : g (last c)+b=h := (htors _ ((hd c).trans hc)).resolve_left (hz c)
  have he := validTuple_injective g hg (add_right_cancel (hea.trans hec.symm))
  exact congrArg Sigma.fst (E.injective he)

/-- In an even cyclic group, two distinct compatible strips cannot
coexist with a no-overflow profile in a sufficiently wide dominant forest. -/
theorem no_base_with_two_compatible_strips_in_even_cyclic_forest
    {n N M : ℕ} [NeZero N] (hn : 24 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hwidth : 2*n ≤ 2^(L j))
    (w u v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hu : u ∈ forestCollisionProfiles n L x)
    (hv : v ∈ forestCollisionProfiles n L x)
    (hwcompat : ∀ i, i ≠ j → Even (w i).val) (hucompat : ∀ i, i ≠ j → Even (u i).val)
    (a c : β) (hac : a ≠ c) (ha : 2^(L a)-1 < (w a).val) (hc : 2^(L c)-1 < (u c).val)
    (hvlow : ∀ i, (v i).val ≤ 2^(L i)-1) : False := by
  obtain ⟨hvz,_,_,_,_⟩ := two_compatible_strips_force_lower_axis_profile hr L hL hwide g hg E x b hchain hgen j (by omega) w u v hw hu hv hwcompat hucompat a c hac ha hc hvlow
  have haz := (axis_profile_and_compatible_strip_equal_zero_boundary hn hr L hL hwide g hg E x b hchain hgen j hwidth w v hw hv hwcompat a ha hvz).2
  have hcz := (axis_profile_and_compatible_strip_equal_zero_boundary hn hr L hL hwide g hg E x b hchain hgen j hwidth u v hu hv hucompat c hc hvz).2
  apply hac
  exact genuine_forest_zero_boundary_unique L hL g hg E x b hchain hgen (M : ZMod N)
    (fun z hz ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hN z (by simpa only [two_nsmul] using hz)) a c haz hcz

/-- In the remaining axis-base/strip case, the zero-boundary strip
must be on a length-one arm. Larger boundaries repeat cheaply enough
to give a full-length rival even with zero dominant increment. -/
theorem axis_base_compatible_strip_arm_length_one
    {n : ℕ} (hn : 24 ≤ n) {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hwidth : 2*n ≤ 2^(L j))
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (hcompat : ∀ i, i ≠ j → Even (w i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val)
    (hvz : ∀ i, i ≠ j → (v i).val=0) : L a=1 := by
  classical
  by_contra hnL
  have hLa : 2 ≤ L a := by have := hL a; omega
  have hKa : 4 ≤ 2^(L a) := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hLa
  obtain ⟨heq,hzero⟩ := axis_profile_and_compatible_strip_equal_zero_boundary hn hr L hL hwide g hg E x b hchain hgen j hwidth w v hw hv hcompat a ha hvz
  obtain ⟨haj,_,_,e,he,hbudget⟩ := compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j (by omega) w hw hcompat a ha
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have htarget : (∑ i, (2^(L i)-1) • x i)=(v j).val • x j := by
    rw [← hvm.2]
    apply Finset.sum_eq_single j
    · intro i _ hij; rw [hvz i hij,zero_nsmul]
    · simp
  exact not_validTuple_of_small_axis_target_and_boundary_step hn L hL g E x b hchain j a haj hwidth
    0 ((v j).val+1) (by omega) (Nat.zero_lt_succ _) (by omega)
    (by simpa using hzero) (by simpa using htarget) hg

end MinModulus
