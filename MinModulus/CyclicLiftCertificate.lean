import MinModulus.CyclicLiftCarry

/-!
# Completeness of finite cyclic-lift carry certificates

A binary equation system, with any possibly infinite row index type,
either has one vector solving ALL equations or has a FINITE row set
whose left sides sum to zero and whose right sides sum to one. The
proof uses linear separation of the augmented row span, not enumeration.

Applied to the full quotient-rival system, finite inconsistent carry
certificates are NECESSARY AND SUFFICIENT for exclusion of every cyclic
lift of an arbitrary quotient at every positive half-modulus. Actual
lift construction, not assumed quotient validity, supplies the other arm.

The existing unrestricted G3 gate is exactly equivalent to supplying
these finite certificates for arbitrary exceptional quotients. This is
a reformulation of the SAME gate, not an additional gate or a proof of
the required exceptional certificate extraction. G1/G2/G3 remain open.
-/

namespace MinModulus
open Finset

/-- Every linear functional on a finite binary coordinate space is
the dot product with its actual values on the coordinate basis. -/
theorem binary_linearMap_eq_dot_basis {n : ℕ}
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (x : Fin n → ZMod 2) :
    L x=∑ j, x j*L (Pi.single j 1) := by
  classical
  have hx : (∑ j, Pi.single j (x j))=x := by ext j; simp
  conv_lhs => rw [← hx]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hsingle : Pi.single j (x j)=x j • (Pi.single j 1 : Fin n → ZMod 2) := by
    rw [← Pi.single_smul]
    simp
  rw [hsingle,map_smul]
  rfl

/-- General binary linear alternative, even for an infinite family of
rows: either one vector solves every equation, or a FINITE set of rows
sums to zero on the left and one on the right. -/
theorem binary_equations_solution_or_finite_obstruction
    {n : ℕ} {I : Type*} (row : I → Fin n → ZMod 2) (rhs : I → ZMod 2) :
    (∃ b : Fin n → ZMod 2, ∀ i, (∑ j, row i j*b j)=rhs i) ∨
    (∃ S : Finset I, (∀ j, (∑ i ∈ S, row i j)=0) ∧ (∑ i ∈ S, rhs i)=1) := by
  classical
  let augmented : I → Fin (n+1) → ZMod 2 := fun i ↦ Fin.cons (rhs i) (row i)
  let A := Finsupp.linearCombination (ZMod 2) augmented
  let e : Fin (n+1) → ZMod 2 := Pi.single 0 1
  by_cases he : e ∈ A.range
  · right
    obtain ⟨l,hl⟩ := he
    have hcoeff : ∀ i ∈ l.support, l i=(1 : ZMod 2) := by
      intro i hi
      have hn : l i ≠ 0 := Finsupp.mem_support_iff.mp hi
      have hcases : ∀ z : ZMod 2, z=0 ∨ z=1 := by decide
      exact (hcases (l i)).resolve_left hn
    have heq : (∑ i ∈ l.support, augmented i)=e := by
      have hh : A l=∑ i ∈ l.support, augmented i := by
        change (∑ i ∈ l.support, l i • augmented i)=_
        exact Finset.sum_congr rfl (fun i hi ↦ by rw [hcoeff i hi,one_smul])
      exact hh.symm.trans hl
    refine ⟨l.support,?_,?_⟩
    · intro j
      have h := congrFun heq j.succ
      simpa only [Finset.sum_apply,augmented,Fin.cons_succ,e,Pi.single_eq_of_ne (Fin.succ_ne_zero j)] using h
    · have h := congrFun heq 0
      simpa only [Finset.sum_apply,augmented,Fin.cons_zero,e,Pi.single_eq_same] using h
  · left
    obtain ⟨L,hL,hLe⟩ := (0 : A.range →ₗ[ZMod 2] ZMod 2).exists_extend_of_notMem he 1
    have hrowzero (i : I) : L (augmented i)=0 := by
      have hi : augmented i ∈ A.range := ⟨Finsupp.single i 1, by simp [A]⟩
      have h := congrArg (fun f : A.range →ₗ[ZMod 2] ZMod 2 ↦ f ⟨augmented i,hi⟩) hL
      simpa only [LinearMap.comp_apply,Submodule.subtype_apply,LinearMap.zero_apply] using h
    refine ⟨fun j ↦ L (Pi.single j.succ 1),?_⟩
    intro i
    have h := binary_linearMap_eq_dot_basis L (augmented i)
    rw [hrowzero,Fin.sum_univ_succ] at h
    simp only [augmented,Fin.cons_zero,Fin.cons_succ] at h
    have hhead : L (Pi.single 0 1)=1 := hLe
    rw [hhead,mul_one] at h
    have hneg : -(rhs i)=rhs i := by
      have hcases : ∀ z : ZMod 2, -z=z := by decide
      exact hcases _
    calc
      (∑ j, row i j*L (Pi.single j.succ 1))=-(rhs i) := by
        apply eq_neg_of_add_eq_zero_left
        simpa only [add_comm] using h.symm
      _=rhs i := hneg

/-- A finite inconsistent carry family of actual nonstandard quotient
rivals. This is certificate DATA, not an additional global proof gate. -/
def HasCyclicLiftCarryObstruction {n M : ℕ}
    (v : Fin n → ZMod (2*M)) (q : Fin n → ZMod M) : Prop :=
  ∃ S : Finset {c : Fin n → ℤ // Witness q 0 c},
    (∀ j, (∑ c ∈ S, (c.val j : ZMod 2))=0) ∧
      (∑ c ∈ S, cyclicRivalCarry v c.val) ≠ (S.card : ZMod 2)

/-- COMPLETE finite alternative for any quotient in every stratum:
either an actual valid lift exists, or a finite inconsistent carry
certificate exists. Infinite or unbounded families are not needed. -/
theorem exists_valid_cyclic_lift_or_finite_carry_obstruction
    {n M : ℕ} [NeZero M] (v : Fin n → ZMod (2*M))
    (q : Fin n → ZMod M)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (v i)=q i) :
    (∃ g : Fin n → ZMod (2*M), ValidTuple g ∧
      ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i) ∨
    HasCyclicLiftCarryObstruction v q := by
  classical
  rcases binary_equations_solution_or_finite_obstruction
    (fun c : {c : Fin n → ℤ // Witness q 0 c} ↦ fun j ↦ (c.val j : ZMod 2))
    (fun c ↦ 1-cyclicRivalCarry v c.val) with ⟨b,hb⟩ | ⟨S,hS,hsum⟩
  · left
    apply (exists_valid_cyclic_lift_iff_carry_equations v q hquot).mpr
    refine ⟨b,?_⟩
    intro c hc
    have h := hb ⟨c,hc⟩
    change (∑ j, (c j : ZMod 2)*b j)=1-cyclicRivalCarry v c at h
    simp only [zsmul_eq_mul]
    rw [h]
    abel
  · right
    refine ⟨S,hS,?_⟩
    intro hcarry
    simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,hcarry,sub_self] at hsum
    exact zero_ne_one hsum

/-- Finite carry certificates are NECESSARY AND SUFFICIENT for the
nonexistence of any valid cyclic lift of the chosen quotient. -/
theorem no_valid_cyclic_lift_iff_finite_carry_obstruction
    {n M : ℕ} [NeZero M] (v : Fin n → ZMod (2*M))
    (q : Fin n → ZMod M)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (v i)=q i) :
    ¬(∃ g : Fin n → ZMod (2*M), ValidTuple g ∧
      ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i) ↔
    HasCyclicLiftCarryObstruction v q := by
  classical
  constructor
  · intro h
    exact (exists_valid_cyclic_lift_or_finite_carry_obstruction v q hquot).resolve_left h
  · rintro ⟨S,hS,hcarry⟩ hex
    obtain ⟨b,hb⟩ := (exists_valid_cyclic_lift_iff_carry_equations v q hquot).mp hex
    have hlinear : (∑ c ∈ S, ∑ i, c.val i • b i)=0 := by
      rw [Finset.sum_comm]
      simp only [zsmul_eq_mul,← Finset.sum_mul,hS,zero_mul,Finset.sum_const_zero]
    have hsum : (∑ c ∈ S, (cyclicRivalCarry v c.val+(∑ i, c.val i • b i)))=
        ∑ _c ∈ S, (1 : ZMod 2) := Finset.sum_congr rfl (fun c _ ↦ hb c.val c.property)
    simp only [Finset.sum_add_distrib,hlinear,add_zero,Finset.sum_const,nsmul_eq_mul,mul_one] at hsum
    exact hcarry hsum

/-- Exact reformulation of the EXISTING unrestricted G3 gate by finite
carry certificates for arbitrary exceptional quotients. This neither
adds a gate nor proves that exceptional quotients supply certificates. -/
theorem exceptionalLiftObstruction_iff_finite_carry_certificates :
    ExceptionalLiftObstruction ↔
      ∀ n : ℕ, 2 ≤ n → 2 ^ Nat.log 2 n ≠ n →
        ∀ v : Fin n → ZMod (2*globalBound (n-1)),
          HasCyclicLiftCarryObstruction v (fun i ↦
            ZMod.castHom (dvd_mul_left (globalBound (n-1)) 2)
              (ZMod (globalBound (n-1))) (v i)) := by
  have hpos (n : ℕ) (hn : 2 ≤ n) : 0 < globalBound (n-1) := by
    unfold globalBound
    apply Nat.sub_pos_of_lt
    exact Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) (Nat.log_lt_self 2 (by omega : n-1 ≠ 0))
  constructor
  · intro h n hn hnp v
    letI : NeZero (globalBound (n-1)) := ⟨(hpos n hn).ne'⟩
    apply (no_valid_cyclic_lift_iff_finite_carry_obstruction v _ (fun _ ↦ rfl)).mp
    rintro ⟨g,hg,_⟩
    exact h n hn hnp ⟨g,hg⟩
  · intro h n hn hnp hvalid
    letI : NeZero (globalBound (n-1)) := ⟨(hpos n hn).ne'⟩
    obtain ⟨g,hg⟩ := hvalid
    exact (no_valid_cyclic_lift_iff_finite_carry_obstruction g _ (fun _ ↦ rfl)).mpr
      (h n hn hnp g) ⟨g,hg,fun _ ↦ rfl⟩

end MinModulus
