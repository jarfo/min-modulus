import MinModulus.OneEscapeDescent
import MinModulus.QuotientRivalParity

/-!
# Extract uniform cyclic-lift obstructions from actual binary defects

Two doubling defects which cancel permit two extra coins at unchanged
total. Among at least three binary involutive defects such a pair
always exists, uniformly in the tuple size and all independent lift
bits. Hence an actual half-quotient doubling block cannot coexist with
an upstairs zero-sum pair. For two copies of the quotient involution,
validity itself extracts that zero-sum pair, excluding every lift.

A second general rule extracts opposite carry from quotient arithmetic:
two actual rivals with nonzero weighted half-difference exclude every
cyclic lift. A three-entry doubling chain, duplicate of its first
coordinate, and nonzero quotient involution give an explicit local
two-rival obstruction, wherever the five coordinates occur.

These close uniform lift-pattern classes, not arbitrary G3 extraction.
No endpoint SI classification or unrestricted global gate is assumed.
-/

namespace MinModulus
open Finset

/-- Among at least three defects taking only the values zero and an
involution, two distinct defects sum to zero. -/
theorem exists_distinct_doubling_defects_sum_zero
    {m : ℕ} (hm : 3 ≤ m) {G : Type*} [AddCommGroup G]
    (d : Fin m → G) (h : G) (hh : h+h=0) (hd : ∀ i, d i=0 ∨ d i=h) :
    ∃ a b : Fin m, a ≠ b ∧ d a+d b=0 := by
  let a : Fin m := ⟨0,by omega⟩
  let b : Fin m := ⟨1,by omega⟩
  let c : Fin m := ⟨2,by omega⟩
  have hab : a ≠ b := by intro he; have := congrArg Fin.val he; dsimp [a,b] at this; omega
  have hac : a ≠ c := by intro he; have := congrArg Fin.val he; dsimp [a,c] at this; omega
  have hbc : b ≠ c := by intro he; have := congrArg Fin.val he; dsimp [b,c] at this; omega
  rcases hd a with ha | ha <;> rcases hd b with hb | hb <;> rcases hd c with hc | hc
  · exact ⟨a,b,hab,by rw [ha,hb,zero_add]⟩
  · exact ⟨a,b,hab,by rw [ha,hb,zero_add]⟩
  · exact ⟨a,c,hac,by rw [ha,hc,zero_add]⟩
  · exact ⟨b,c,hbc,by rw [hb,hc,hh]⟩
  · exact ⟨b,c,hbc,by rw [hb,hc,zero_add]⟩
  · exact ⟨a,c,hac,by rw [ha,hc,hh]⟩
  · exact ⟨a,b,hab,by rw [ha,hb,hh]⟩
  · exact ⟨a,b,hab,by rw [ha,hb,hh]⟩

/-- Two distinct doubling edges whose defects cancel produce an
ACTUAL multiset with two extra coins and unchanged total. No validity
premise, cyclic order, or modulus hypothesis is used. -/
theorem exists_multiset_card_add_two_of_cancelling_doubling_defects
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (x : Fin m → G) (R : Equiv.Perm (Fin m))
    (a b : Fin m) (hab : a ≠ b)
    (hcancel : (2 • x a-x (R a))+(2 • x b-x (R b))=0) :
    ∃ t : Multiset (Fin m), t.card=m+2 ∧ (t.map x).sum=∑ i, x i := by
  classical
  have hR : R b ≠ R a := R.injective.ne hab.symm
  have hb : R b ∈ (Finset.univ : Finset (Fin m)).erase (R a) := by simp [hR]
  let S := ((Finset.univ : Finset (Fin m)).erase (R a)).erase (R b)
  have hcard : S.card+2=m := by
    have h1 := Finset.card_erase_add_one (Finset.mem_univ (R a))
    have h2 := Finset.card_erase_add_one hb
    simp only [Finset.card_univ,Fintype.card_fin] at h1
    dsimp [S]
    omega
  have hsum : (∑ i ∈ S, x i)+x (R b)+x (R a)=∑ i, x i := by
    dsimp [S]
    rw [Finset.sum_erase_add _ x hb,Finset.sum_erase_add _ x (Finset.mem_univ (R a))]
  have heq : x a+x a+(x b+x b)=x (R a)+x (R b) := by
    apply sub_eq_zero.mp
    convert hcancel using 1
    simp only [two_nsmul]
    abel
  let t := a ::ₘ a ::ₘ b ::ₘ b ::ₘ S.val
  refine ⟨t,?_,?_⟩
  · change S.card+1+1+1+1=m+2
    omega
  · change x a+(x a+(x b+(x b+(∑ i ∈ S, x i))))=∑ i, x i
    calc
      _=(x a+x a+(x b+x b))+(∑ i ∈ S, x i) := by abel
      _=(∑ i ∈ S, x i)+x (R b)+x (R a) := by rw [heq]; abel
      _=∑ i, x i := hsum

/-- A permutation with binary involutive doubling defects on at least
three coordinates always admits two-coin growth at unchanged total. -/
theorem exists_multiset_card_add_two_of_binary_doubling_defects
    {m : ℕ} (hm : 3 ≤ m) {G : Type*} [AddCommGroup G]
    (x : Fin m → G) (R : Equiv.Perm (Fin m)) (h : G) (hh : h+h=0)
    (hd : ∀ i, 2 • x i-x (R i)=0 ∨ 2 • x i-x (R i)=h) :
    ∃ t : Multiset (Fin m), t.card=m+2 ∧ (t.map x).sum=∑ i, x i := by
  obtain ⟨a,b,hab,hcancel⟩ := exists_distinct_doubling_defects_sum_zero hm _ h hh hd
  exact exists_multiset_card_add_two_of_cancelling_doubling_defects x R a b hab hcancel

/-- Two outside coordinates with zero total are incompatible with an
actual binary-defect doubling block of size at least three. -/
theorem not_validTuple_of_binary_doubling_defects_and_zero_sum_pair
    {m : ℕ} (hm : 3 ≤ m) {G : Type*} [AddCommGroup G]
    (g : Fin (m+2) → G) (R : Equiv.Perm (Fin m)) (h : G) (hh : h+h=0)
    (hd : ∀ i, 2 • g (Fin.castAdd 2 i)-g (Fin.castAdd 2 (R i))=0 ∨
      2 • g (Fin.castAdd 2 i)-g (Fin.castAdd 2 (R i))=h)
    (hz : (∑ i : Fin 2, g (Fin.natAdd m i))=0) : ¬ ValidTuple g := by
  classical
  intro hg
  obtain ⟨s,hs,hvalue⟩ := exists_multiset_card_add_two_of_binary_doubling_defects hm
    (fun i ↦ g (Fin.castAdd 2 i)) R h hh hd
  let t := s.map (Fin.castAdd 2)
  have htcard : t.card=m+2 := by simpa [t] using hs
  have htsum : (t.map g).sum=∑ i, g i := by
    rw [Fin.sum_univ_add,hz,add_zero]
    simpa only [t,Multiset.map_map,Function.comp_def] using hvalue
  let j : Fin (m+2) := Fin.natAdd m (0 : Fin 2)
  have hj : j ∉ t := by
    intro hmem
    obtain ⟨i,_,heq⟩ := Multiset.mem_map.mp hmem
    have he := congrArg Fin.val heq
    simp only [Fin.val_castAdd,j,Fin.val_natAdd,Fin.val_zero,add_zero] at he
    omega
  have hc := multiset_count_eq_one_of_validTuple g hg t htcard htsum j
  rw [Multiset.count_eq_zero.mpr hj] at hc
  omega

/-- An ACTUAL doubling-permuted half quotient supplies binary defects
in all even moduli. No coherent upstairs lifting is assumed. -/
theorem not_validTuple_of_half_quotient_doubling_and_zero_sum_pair
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m+2) → ZMod (2*M)) (R : Equiv.Perm (Fin m))
    (hd : ∀ i,
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.castAdd 2 (R i)))=
      2 • ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.castAdd 2 i)))
    (hz : (∑ i : Fin 2, g (Fin.natAdd m i))=0) : ¬ ValidTuple g := by
  apply not_validTuple_of_binary_doubling_defects_and_zero_sum_pair hm g R (M : ZMod (2*M)) (half_add_half rfl) _ hz
  intro i
  have hquot : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (2 • g (Fin.castAdd 2 i))=
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.castAdd 2 (R i))) := by
    rw [map_nsmul,hd]
  rcases eq_or_eq_add_half_of_castHom_eq _ _ hquot with heq | heq
  · exact Or.inl (sub_eq_zero.mpr heq)
  · exact Or.inr (by rw [heq]; abel)

/-- Every lift of a doubling-permuted block plus two copies of the
nonzero half-quotient involution is invalid. This is uniform in the
block size and all independent lift bits. Validity itself forces the
two actual outside lifts to be opposite, so their zero sum is extracted. -/
theorem not_validTuple_of_doubling_quotient_and_repeated_involution
    {m L : ℕ} [NeZero L] (hm : 3 ≤ m)
    (g : Fin (m+2) → ZMod (2*(2*L))) (R : Equiv.Perm (Fin m))
    (hd : ∀ i,
      ZMod.castHom (dvd_mul_left (2*L) 2) (ZMod (2*L)) (g (Fin.castAdd 2 (R i)))=
      2 • ZMod.castHom (dvd_mul_left (2*L) 2) (ZMod (2*L)) (g (Fin.castAdd 2 i)))
    (hx : ∀ i : Fin 2,
      ZMod.castHom (dvd_mul_left (2*L) 2) (ZMod (2*L)) (g (Fin.natAdd m i))=(L : ZMod (2*L))) :
    ¬ ValidTuple g := by
  intro hg
  have hL := Nat.pos_of_ne_zero (NeZero.ne L)
  letI : NeZero (2*L) := ⟨by omega⟩
  have hvalues (i : Fin 2) : g (Fin.natAdd m i)=(L : ZMod (2*(2*L))) ∨
      g (Fin.natAdd m i)=(L : ZMod (2*(2*L)))+(2*L : ℕ) := by
    apply eq_or_eq_add_half_of_castHom_eq
    simpa only [map_natCast] using hx i
  have hne : g (Fin.natAdd m (0 : Fin 2)) ≠ g (Fin.natAdd m (1 : Fin 2)) := by
    apply (validTuple_injective g hg).ne
    intro heq
    have he := congrArg Fin.val heq
    simp only [Fin.val_natAdd,Fin.val_zero,Fin.val_one,add_zero] at he
    omega
  have hzero : (L : ZMod (2*(2*L)))+L+(2*L : ℕ)=0 := by
    calc
      _=((2*(2*L) : ℕ) : ZMod (2*(2*L))) := by push_cast; ring
      _=0 := ZMod.natCast_self _
  have hz : (∑ i : Fin 2, g (Fin.natAdd m i))=0 := by
    rw [Fin.sum_univ_two]
    rcases hvalues 0 with h0 | h0 <;> rcases hvalues 1 with h1 | h1
    · exact False.elim (hne (h0.trans h1.symm))
    · rw [h0,h1]
      simpa only [add_assoc] using hzero
    · rw [h0,h1]
      calc
        _=(L : ZMod (2*(2*L)))+L+(2*L : ℕ) := by abel
        _=0 := hzero
    · exact False.elim (hne (h0.trans h1.symm))
  exact not_validTuple_of_half_quotient_doubling_and_zero_sum_pair hm g R hd hz hg

/-- Quotient arithmetic extracts opposite carry without choosing a
base lift: two actual rivals whose half-difference has nonzero quotient
weight exclude EVERY cyclic lift. -/
theorem not_validTuple_of_quotient_rivals_nonzero_half_difference
    {n M : ℕ} [NeZero M] (q : Fin n → ZMod M)
    (c d e : Fin n → ℤ) (hc : Witness q 0 c) (hd : Witness q 0 d)
    (he : ∀ i, c i-d i=2*e i) (hne : (∑ i, e i • q i) ≠ 0)
    (g : Fin n → ZMod (2*M))
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i) : ¬ ValidTuple g := by
  intro hg
  have hc' := (witness_half_of_valid_quotient_rival g hg q hquot c hc).2.2.2
  have hd' := (witness_half_of_valid_quotient_rival g hg q hquot d hd).2.2.2
  have hz : (∑ i, (c i-d i) • g i)=0 := by
    simp only [sub_smul,Finset.sum_sub_distrib,hc',hd',sub_self]
  have hzero : 2 • (∑ i, e i • g i)=0 := by
    simpa only [he,mul_smul,show (2 : ℤ)=((2 : ℕ) : ℤ) from rfl,natCast_zsmul,
      Finset.smul_sum] using hz
  have hqzero := castHom_eq_of_two_nsmul_eq (∑ i, e i • g i) 0 (by simpa using hzero)
  apply hne
  simpa only [map_sum,map_zsmul,hquot,map_zero] using hqzero

/-- A three-entry doubling chain, a duplicate of its first coordinate,
and a nonzero quotient involution yield an ACTUAL two-rival carry
obstruction. The five coordinates can lie anywhere in a larger tuple;
all other values and all independent lift bits are arbitrary. -/
theorem not_validTuple_of_quotient_doubling_chain_duplicate_involution
    {n M : ℕ} [NeZero M]
    (g : Fin n → ZMod (2*M)) (f : Fin 5 ↪ Fin n) (q : Fin 5 → ZMod M)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (f i))=q i)
    (h1 : q 1=2 • q 0) (h2 : q 2=2 • q 1) (hdup : q 4=q 0)
    (htor : q 3+q 3=0) (hne : q 3 ≠ 0) : ¬ ValidTuple g := by
  intro hg
  let c : Fin 5 → ℤ := ![-1,3,-1,0,-1]
  let d : Fin 5 → ℤ := ![-1,-1,1,2,-1]
  let e : Fin 5 → ℤ := ![0,2,-1,-1,0]
  have hc : Witness q 0 c := by
    refine ⟨?_,?_,?_,?_⟩
    · intro hz
      have h := congrFun hz 0
      norm_num [c] at h
    · intro i; fin_cases i <;> norm_num [c]
    · norm_num [Fin.sum_univ_succ,c]
    · simp [Fin.sum_univ_succ,c,zsmul_eq_mul,hdup,h2,h1,nsmul_eq_mul]
      ring
  have hd : Witness q 0 d := by
    refine ⟨?_,?_,?_,?_⟩
    · intro hz
      have h := congrFun hz 0
      norm_num [d] at h
    · intro i; fin_cases i <;> norm_num [d]
    · norm_num [Fin.sum_univ_succ,d]
    · have htwo : (2 : ZMod M)*q 3=0 := by simpa only [two_mul] using htor
      convert htwo using 1
      simp [Fin.sum_univ_succ,d,zsmul_eq_mul,hdup,h2,h1,nsmul_eq_mul]
      ring
  have he : ∀ i, c i-d i=2*e i := by intro i; fin_cases i <;> norm_num [c,d,e]
  have hweight : (∑ i, e i • q i)=-q 3 := by
    simp [Fin.sum_univ_succ,e,zsmul_eq_mul,h2,nsmul_eq_mul]
  exact not_validTuple_of_quotient_rivals_nonzero_half_difference q c d e hc hd he
    (by rw [hweight]; exact neg_ne_zero.mpr hne) _ hquot (validTuple_embedding f g hg)

end MinModulus
