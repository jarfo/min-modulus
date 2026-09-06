import MinModulus.CyclicLiftCertificate

/-!
# Dimension-sized cyclic lift certificates

An inconsistent binary equation family on n variables has an inconsistent
subfamily of at most n+1 ACTUAL rows. A finite spanning-set extraction
proves this without solving a bounded instance. Balanced row coefficients
make one coordinate redundant and sharpen the bound to n rows.

Every quotient rival is balanced. Thus for every nonempty n-coordinate
quotient at every positive half-modulus, exclusion of all cyclic lifts
is equivalent to a carry certificate using at most n nonstandard rivals.
The EXISTING unrestricted G3 gate is exactly universal extraction of
these dimension-sized certificates at exceptional quotients.

This proves a uniform size bound, not a two- or three-row cutoff and not
the universal critical/exceptional extraction itself. G1/G2/G3 remain open.
-/

namespace MinModulus
open Finset

/-- Any inconsistent finite binary equation family has an inconsistent
subfamily of at most n+1 rows. Rows remain ACTUAL members of the input. -/
theorem binary_obstruction_shrink
    {n : ℕ} {I : Type*} (row : I → Fin n → ZMod 2) (rhs : I → ZMod 2)
    (S : Finset I) (hrow : ∀ j, (∑ i ∈ S, row i j)=0) (hrhs : (∑ i ∈ S, rhs i)=1) :
    ∃ T : Finset I, T ⊆ S ∧ T.card ≤ n+1 ∧
      (∀ j, (∑ i ∈ T, row i j)=0) ∧ (∑ i ∈ T, rhs i)=1 := by
  classical
  let augmented : I → Fin (n+1) → ZMod 2 := fun i ↦ Fin.cons (rhs i) (row i)
  let e : Fin (n+1) → ZMod 2 := Pi.single 0 1
  let V := Submodule.span (ZMod 2) (augmented '' (S : Set I))
  have hsum : (∑ i ∈ S, augmented i)=e := by
    funext j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · simpa only [Finset.sum_apply,augmented,Fin.cons_zero,e,Pi.single_eq_same] using hrhs
    · simpa only [Finset.sum_apply,augmented,Fin.cons_succ,e,
        Pi.single_eq_of_ne (Fin.succ_ne_zero j)] using hrow j
  have he : e ∈ V := by
    rw [← hsum]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.subset_span ⟨i,hi,rfl⟩
  obtain ⟨l,hlcard,hlsupp,hlsum⟩ :=
    Submodule.mem_span_set_iff_exists_finsupp_le_finrank.mp he
  have hcoeff : ∀ x ∈ l.support, l x=(1 : ZMod 2) := by
    intro x hx
    have hn : l x ≠ 0 := Finsupp.mem_support_iff.mp hx
    have hc : ∀ z : ZMod 2, z=0 ∨ z=1 := by decide
    exact (hc (l x)).resolve_left hn
  have hplain : (∑ x ∈ l.support, x)=e := by
    have h : l.sum (fun x a ↦ a • x)=∑ x ∈ l.support, x := by
      exact Finset.sum_congr rfl (fun x hx ↦ by change l x • x=x; rw [hcoeff x hx,one_smul])
    exact h.symm.trans hlsum
  have hchoose : ∀ x : ↥l.support, ∃ i ∈ S, augmented i=x.val := by
    intro x
    exact hlsupp x.property
  choose f hfS hfvalue using hchoose
  have hfinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    rw [← hfvalue x,← hfvalue y,h]
  let T := l.support.attach.image f
  have hTsub : T ⊆ S := by
    intro i hi
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hi
    exact hfS x
  have hTcard : T.card ≤ n+1 := by
    have hle : T.card ≤ l.support.card := by
      simpa only [Finset.card_attach] using Finset.card_image_le (s := l.support.attach) (f := f)
    have hdim : Module.finrank (ZMod 2) V ≤ n+1 := by
      simpa using V.finrank_le
    exact hle.trans (hlcard.trans hdim)
  have hTsum : (∑ i ∈ T, augmented i)=e := by
    change (∑ i ∈ l.support.attach.image f, augmented i)=e
    rw [Finset.sum_image]
    · simp only [hfvalue]
      exact (Finset.sum_attach l.support id).trans hplain
    · intro x _ y _ h
      exact hfinj h
  refine ⟨T,hTsub,hTcard,?_,?_⟩
  · intro j
    have h := congrFun hTsum j.succ
    simpa only [Finset.sum_apply,augmented,Fin.cons_succ,e,
      Pi.single_eq_of_ne (Fin.succ_ne_zero j)] using h
  · have h := congrFun hTsum 0
    simpa only [Finset.sum_apply,augmented,Fin.cons_zero,e,Pi.single_eq_same] using h

/-- Balanced rows remove one redundant coordinate, sharpening the
inconsistent-subfamily bound from n+2 to n+1 for n+1 coordinates. -/
theorem balanced_binary_obstruction_shrink
    {n : ℕ} {I : Type*} (row : I → Fin (n+1) → ZMod 2) (rhs : I → ZMod 2)
    (S : Finset I) (hbalance : ∀ i ∈ S, (∑ j, row i j)=0)
    (hrow : ∀ j, (∑ i ∈ S, row i j)=0) (hrhs : (∑ i ∈ S, rhs i)=1) :
    ∃ T : Finset I, T ⊆ S ∧ T.card ≤ n+1 ∧
      (∀ j, (∑ i ∈ T, row i j)=0) ∧ (∑ i ∈ T, rhs i)=1 := by
  obtain ⟨T,hTS,hcard,htail,hrhs⟩ := binary_obstruction_shrink
    (fun i j ↦ row i j.succ) rhs S (fun j ↦ hrow j.succ) hrhs
  have hsum : (∑ j : Fin (n+1), ∑ i ∈ T, row i j)=0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun i hi ↦ hbalance i (hTS hi))
  have hhead : (∑ i ∈ T, row i 0)=0 := by
    rw [Fin.sum_univ_succ] at hsum
    simpa only [htail,Finset.sum_const_zero,add_zero] using hsum
  exact ⟨T,hTS,hcard,fun j ↦ Fin.cases hhead htail j,hrhs⟩

/-- Every carry obstruction in a nonempty n-coordinate quotient can
be witnessed by at most n ACTUAL nonstandard rivals, uniformly in M. -/
theorem exists_carry_obstruction_card_le_length
    {n M : ℕ} (hn : 0 < n) (v : Fin n → ZMod (2*M)) (q : Fin n → ZMod M)
    (hobs : HasCyclicLiftCarryObstruction v q) :
    ∃ S : Finset {c : Fin n → ℤ // Witness q 0 c}, S.card ≤ n ∧
      (∀ j, (∑ c ∈ S, (c.val j : ZMod 2))=0) ∧
      (∑ c ∈ S, cyclicRivalCarry v c.val) ≠ (S.card : ZMod 2) := by
  classical
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨S,hrow,hcarry⟩ := hobs
    let row := fun c : {c : Fin (n+1) → ℤ // Witness q 0 c} ↦ fun j ↦ (c.val j : ZMod 2)
    let rhs := fun c : {c : Fin (n+1) → ℤ // Witness q 0 c} ↦ 1-cyclicRivalCarry v c.val
    have hbalance : ∀ c ∈ S, (∑ j, row c j)=0 := by
      intro c _
      simpa only [row,Int.cast_sum,Int.cast_zero] using
        congrArg (fun z : ℤ ↦ (z : ZMod 2)) c.property.2.2.1
    have hrhs : (∑ c ∈ S, rhs c)=1 := by
      have hz : (∑ c ∈ S, rhs c) ≠ 0 := by
        intro hzero
        simp only [rhs,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,mul_one] at hzero
        exact hcarry (sub_eq_zero.mp hzero).symm
      have hc : ∀ z : ZMod 2, z=0 ∨ z=1 := by decide
      exact (hc _).resolve_left hz
    obtain ⟨T,_,hcard,hTrow,hTrhs⟩ := balanced_binary_obstruction_shrink row rhs S hbalance hrow hrhs
    refine ⟨T,hcard,hTrow,?_⟩
    intro hTcarry
    simp only [rhs,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,hTcarry,sub_self] at hTrhs
    exact zero_ne_one hTrhs

/-- Exclusion of all cyclic lifts is equivalent to an inconsistent
carry family with at most as many rows as tuple coordinates. -/
theorem no_valid_cyclic_lift_iff_small_carry_obstruction
    {n M : ℕ} [NeZero M] (hn : 0 < n)
    (v : Fin n → ZMod (2*M)) (q : Fin n → ZMod M)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (v i)=q i) :
    ¬(∃ g : Fin n → ZMod (2*M), ValidTuple g ∧
      ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i) ↔
    ∃ S : Finset {c : Fin n → ℤ // Witness q 0 c}, S.card ≤ n ∧
      (∀ j, (∑ c ∈ S, (c.val j : ZMod 2))=0) ∧
      (∑ c ∈ S, cyclicRivalCarry v c.val) ≠ (S.card : ZMod 2) := by
  rw [no_valid_cyclic_lift_iff_finite_carry_obstruction v q hquot]
  exact ⟨exists_carry_obstruction_card_le_length hn v q,
    fun ⟨S,_,hrow,hcarry⟩ ↦ ⟨S,hrow,hcarry⟩⟩

/-- The SAME G3 gate is exactly the extraction of at most n actual
quotient rivals with inconsistent carry at every exceptional n-tuple.
This is a dimension-uniform bound, not a finite-instance substitute. -/
theorem exceptionalLiftObstruction_iff_small_carry_certificates :
    ExceptionalLiftObstruction ↔
      ∀ n : ℕ, 2 ≤ n → 2 ^ Nat.log 2 n ≠ n →
        ∀ v : Fin n → ZMod (2*globalBound (n-1)),
          let q := fun i ↦ ZMod.castHom (dvd_mul_left (globalBound (n-1)) 2)
            (ZMod (globalBound (n-1))) (v i)
          ∃ S : Finset {c : Fin n → ℤ // Witness q 0 c}, S.card ≤ n ∧
            (∀ j, (∑ c ∈ S, (c.val j : ZMod 2))=0) ∧
            (∑ c ∈ S, cyclicRivalCarry v c.val) ≠ (S.card : ZMod 2) := by
  rw [exceptionalLiftObstruction_iff_finite_carry_certificates]
  constructor
  · intro h n hn hnp v
    exact exists_carry_obstruction_card_le_length (by omega) v _ (h n hn hnp v)
  · intro h n hn hnp v
    obtain ⟨S,_,hrow,hcarry⟩ := h n hn hnp v
    exact ⟨S,hrow,hcarry⟩

end MinModulus
