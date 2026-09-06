import MinModulus.DoubleDefectGrowth

/-!
# Exclude every next lift of a cycle-plus-involution quotient

A doubling-permuted quotient block of size at least three, a nonzero
quotient involution, and a duplicate of ANY one of these coordinates
admit no valid cyclic lift. All independent lift bits are allowed.

For a repeated involution, distinct actual lifts have zero sum and
binary-defect growth gives a rival. For a repeated cycle coordinate,
actual antipodal half deletion extracts quotient-block validity.
That forces three distinct successive cycle coordinates at the
duplicate, which supply the already proved local two-rival obstruction.
Neither quotient validity nor local geometry is an extra premise.

This closes the entire next-lift obstruction for this endpoint family;
it does not classify arbitrary one-escape endpoints or close G3.
-/

namespace MinModulus
open Finset

/-- At every coordinate of a valid doubling-permuted block of size
at least three, the first three successive coordinates are distinct. -/
theorem doubling_three_distinct_of_valid
    {m M : ℕ} (hm : 3 ≤ m) (q : Fin m → ZMod M) (hq : ValidTuple q)
    (R : Equiv.Perm (Fin m)) (hd : ∀ i, q (R i)=2 • q i) (j : Fin m) :
    j ≠ R j ∧ j ≠ R (R j) ∧ R j ≠ R (R j) := by
  have h01 : j ≠ R j := (doubling_apply_ne_of_valid (by omega) q hq R hd j).symm
  have h12 : R j ≠ R (R j) := (doubling_apply_ne_of_valid (by omega) q hq R hd (R j)).symm
  refine ⟨h01,?_,h12⟩
  intro heq
  have h4 : 4 • q j=q j := by
    simpa only [hd,smul_smul,show (2 : ℕ)*2=4 by decide] using (congrArg q heq).symm
  have h3 : 3 • q j=0 := by
    simp only [nsmul_eq_mul,Nat.cast_ofNat] at h4 ⊢
    linear_combination h4
  have horder := addOrderOf_eq_mersenne_of_valid_doubling (by omega) q hq R hd j
  have hdiv : (2^m-1) ∣ 3 := by
    rw [← horder,addOrderOf_dvd_iff_nsmul_eq_zero]
    exact h3
  have hbound : 7 ≤ 2^m-1 := by
    have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hm
    norm_num at hpow
    omega
  exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < 3) (by omega : 3 < 2^m-1)) hdiv

/-- Any two distinct actual cyclic lifts of a nonzero quotient
involution have zero sum. This does not require a Mersenne modulus. -/
theorem add_eq_zero_of_distinct_lifts_of_nonzero_involution
    {M : ℕ} [NeZero M] (x y : ZMod (2*M)) (h : ZMod M)
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) x=h)
    (hy : ZMod.castHom (dvd_mul_left M 2) (ZMod M) y=h)
    (htor : h+h=0) (hne : h ≠ 0) (hxy : x ≠ y) : x+y=0 := by
  have hM := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  have hpair : x=y+(M : ℕ) := by
    rcases eq_or_eq_add_half_of_castHom_eq x y (hx.trans hy.symm) with heq | heq
    · exact (hxy heq).elim
    · exact heq
  have hdouble : y+y=(M : ZMod (2*M)) := by
    have hzero : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (y+y)=0 := by
      rw [map_add,hy,htor]
    rcases eq_or_eq_add_half_of_castHom_eq (y+y) 0 (by simpa only [map_zero] using hzero) with hz | hh
    · rcases zmod_eq_zero_or_half_of_add_self_eq_zero rfl y hz with hy0 | hyM
      · apply False.elim
        apply hne
        rw [← hy,hy0,map_zero]
      · apply False.elim
        apply hne
        rw [← hy,hyM,map_natCast,ZMod.natCast_self]
    · simpa only [zero_add] using hh
  rw [hpair]
  calc
    _=(y+y)+(M : ℕ) := by abel
    _=0 := by rw [hdouble]; exact half_add_half rfl

/-- A repeated last quotient coordinate makes the ACTUAL retained
quotient block valid. This extracts the cycle-validity premise from
the hypothetical parent, rather than assuming it about arbitrary lifts. -/
theorem valid_quotient_block_of_repeated_last_coordinate
    {m M : ℕ} [NeZero M] (g : Fin (m+2) → ZMod (2*M)) (hg : ValidTuple g)
    (q : Fin m → ZMod M)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.castAdd 2 i))=q i)
    (j : Fin m)
    (hdup : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m+1)))=q j) : ValidTuple q := by
  have hM := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  have hne : Fin.castAdd 2 j ≠ Fin.last (m+1) := by
    intro heq
    have he := congrArg Fin.val heq
    simp only [Fin.val_castAdd,Fin.val_last] at he
    omega
  have hdouble : 2 • g (Fin.last (m+1))=2 • g (Fin.castAdd 2 j) := by
    rw [← zmodScaleHom_castHom,← zmodScaleHom_castHom,hquot,hdup]
  have hv : ValidTuple (fun i : Fin (m+1) ↦
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i.castSucc)) := by
    simpa using validTuple_actual_half_of_doubled_collision g hg (Fin.last (m+1)) (Fin.castAdd 2 j) hne hdouble
  have hv' := validTuple_embedding (⟨Fin.castSucc,Fin.castSucc_injective m⟩ : Fin m ↪ Fin (m+1)) _ hv
  convert hv' using 1
  funext i
  exact (hquot i).symm

/-- Uniform next-lift exclusion for a doubling-permuted quotient
block, a nonzero quotient involution, and a duplicate of ANY retained
coordinate. All independent lift bits are arbitrary. Validity of the
actual quotient cycle and its local three-point pattern are extracted. -/
theorem not_validTuple_of_cycle_involution_quotient_and_duplicate
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m+2) → ZMod (2*M)) (q : Fin m → ZMod M)
    (R : Equiv.Perm (Fin m)) (hd : ∀ i, q (R i)=2 • q i)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.castAdd 2 i))=q i)
    (h : ZMod M) (htor : h+h=0) (hne : h ≠ 0)
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.natAdd m (0 : Fin 2)))=h)
    (hy : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.natAdd m (1 : Fin 2)))=h ∨
      ∃ j, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.natAdd m (1 : Fin 2)))=q j) :
    ¬ ValidTuple g := by
  intro hg
  rcases hy with hy | ⟨j,hy⟩
  · have hxy : g (Fin.natAdd m (0 : Fin 2)) ≠ g (Fin.natAdd m (1 : Fin 2)) := by
      apply (validTuple_injective g hg).ne
      intro heq
      have he := congrArg Fin.val heq
      simp only [Fin.val_natAdd,Fin.val_zero,Fin.val_one,add_zero] at he
      omega
    have hzero := add_eq_zero_of_distinct_lifts_of_nonzero_involution _ _ h hx hy htor hne hxy
    apply not_validTuple_of_half_quotient_doubling_and_zero_sum_pair hm g R _ _ hg
    · intro i
      rw [hquot,hquot,hd]
    · simpa only [Fin.sum_univ_two] using hzero
  · have hq : ValidTuple q := valid_quotient_block_of_repeated_last_coordinate g hg q hquot j hy
    obtain ⟨h01,h02,h12⟩ := doubling_three_distinct_of_valid hm q hq R hd j
    have h01v : j.val ≠ (R j).val := fun he ↦ h01 (Fin.ext he)
    have h02v : j.val ≠ (R (R j)).val := fun he ↦ h02 (Fin.ext he)
    have h12v : (R j).val ≠ (R (R j)).val := fun he ↦ h12 (Fin.ext he)
    let F : Fin 5 → Fin (m+2) := ![Fin.castAdd 2 j,Fin.castAdd 2 (R j),
      Fin.castAdd 2 (R (R j)),Fin.natAdd m 0,Fin.natAdd m 1]
    have hF : Function.Injective F := by
      intro a b heq
      have hev := congrArg Fin.val heq
      fin_cases a <;> fin_cases b <;> try rfl
      all_goals simp [F] at hev
      all_goals omega
    let f : Fin 5 ↪ Fin (m+2) := ⟨F,hF⟩
    let v : Fin 5 → ZMod M := ![q j,q (R j),q (R (R j)),h,q j]
    have hv : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (f i))=v i := by
      intro i
      fin_cases i
      · exact hquot j
      · exact hquot (R j)
      · exact hquot (R (R j))
      · exact hx
      · exact hy
    exact not_validTuple_of_quotient_doubling_chain_duplicate_involution g f v hv
      (hd j) (hd (R j)) rfl htor hne hg

end MinModulus
