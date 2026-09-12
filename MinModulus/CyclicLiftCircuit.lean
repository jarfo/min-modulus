import MinModulus.SmallLiftCertificate

/-!
# Irreducible carry circuits for arbitrary cyclic quotients

A finite inconsistent binary equation family contains actual rows whose
only zero-sum subfamilies are empty and the whole family. On this parity
circuit, prescribed dot products are attainable exactly when their sum is
zero; deleting any one row makes all remaining equations solvable.

For a nonempty n-coordinate cyclic quotient at any positive half-modulus,
nonexistence of a valid lift is equivalent to an inconsistent carry circuit
with at most n actual rivals. The size bound was already proved in
SmallLiftCertificate; the new information is the irreducible circuit and
its exact local solvability. G1/G2/G3 remain open because uniform extraction
from critical or exceptional modulus bounds is still missing.
-/

namespace MinModulus
open Finset

/-- Every inconsistent binary family contains an inconsistent parity
circuit: its only subfamilies with zero row sum are empty and the whole
family. The selected rows are actual members of the supplied family. -/
theorem binary_obstruction_contains_parity_circuit
    {n : ℕ} {I : Type*} (row : I → Fin n → ZMod 2) (rhs : I → ZMod 2)
    (S : Finset I) (hrow : ∀ j, (∑ i ∈ S, row i j)=0)
    (hrhs : (∑ i ∈ S, rhs i)=1) :
    ∃ T : Finset I, T ⊆ S ∧ T.Nonempty ∧
      (∀ j, (∑ i ∈ T, row i j)=0) ∧ (∑ i ∈ T, rhs i)=1 ∧
      ∀ U : Finset I, U ⊆ T → (∀ j, (∑ i ∈ U, row i j)=0) → U=∅ ∨ U=T := by
  classical
  let P := fun k : ℕ ↦ ∃ T : Finset I, T ⊆ S ∧ T.card=k ∧
    (∀ j, (∑ i ∈ T, row i j)=0) ∧ (∑ i ∈ T, rhs i)=1
  have hex : ∃ k, P k := ⟨S.card,S,Finset.Subset.refl _,rfl,hrow,hrhs⟩
  obtain ⟨T,hTS,hcard,hTrow,hTrhs⟩ := Nat.find_spec hex
  have hmin (U : Finset I) (hUS : U ⊆ S)
      (hUrow : ∀ j, (∑ i ∈ U, row i j)=0) (hUrhs : (∑ i ∈ U, rhs i)=1) :
      T.card ≤ U.card := by
    rw [hcard]
    exact Nat.find_min' hex ⟨U,hUS,rfl,hUrow,hUrhs⟩
  have hne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h,Finset.sum_empty] at hTrhs
    exact zero_ne_one hTrhs
  refine ⟨T,hTS,hne,hTrow,hTrhs,?_⟩
  intro U hUT hUrow
  by_cases hUempty : U=∅
  · exact Or.inl hUempty
  right
  by_contra hUne
  have hproper : U.card < T.card := Finset.card_lt_card
    ⟨hUT,fun hTU ↦ hUne (Finset.Subset.antisymm hUT hTU)⟩
  have hcases : ∀ z : ZMod 2, z=0 ∨ z=1 := by decide
  rcases hcases (∑ i ∈ U, rhs i) with hzero | hone
  · have hdiffrow : ∀ j, (∑ i ∈ T\U, row i j)=0 := by
      intro j
      rw [Finset.sum_sdiff_eq_sub hUT,hTrow,hUrow,sub_self]
    have hdiff : (∑ i ∈ T\U, rhs i)=1 := by
      rw [Finset.sum_sdiff_eq_sub hUT,hTrhs,hzero,sub_zero]
    have hle := hmin (T\U) ((Finset.sdiff_subset).trans hTS) hdiffrow hdiff
    rw [Finset.card_sdiff_of_subset hUT] at hle
    have hpos : 0 < U.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hUempty)
    omega
  · have hle := hmin U (hUT.trans hTS) hUrow hone
    omega

/-- On a parity circuit, the only constraint on prescribed binary dot
products is that their total be zero. This gives a complete local equation
criterion, including solvability after removing any one circuit row. -/
theorem binary_equations_on_parity_circuit_iff
    {n : ℕ} {I : Type*} (row : I → Fin n → ZMod 2) (S : Finset I)
    (hrow : ∀ j, (∑ i ∈ S, row i j)=0)
    (hcircuit : ∀ U : Finset I, U ⊆ S →
      (∀ j, (∑ i ∈ U, row i j)=0) → U=∅ ∨ U=S)
    (rhs : I → ZMod 2) :
    (∃ b : Fin n → ZMod 2, ∀ i ∈ S, (∑ j, row i j*b j)=rhs i) ↔
      (∑ i ∈ S, rhs i)=0 := by
  classical
  constructor
  · rintro ⟨b,hb⟩
    calc
      (∑ i ∈ S, rhs i)=(∑ i ∈ S, ∑ j, row i j*b j) :=
        Finset.sum_congr rfl (fun i hi ↦ (hb i hi).symm)
      _=0 := by rw [Finset.sum_comm]; simp only [← Finset.sum_mul,hrow,zero_mul,Finset.sum_const_zero]
  · intro hrhs
    rcases binary_equations_solution_or_finite_obstruction
      (fun i : S ↦ row i.val) (fun i : S ↦ rhs i.val) with ⟨b,hb⟩ | ⟨T,hTrow,hTrhs⟩
    · exact ⟨b,fun i hi ↦ hb ⟨i,hi⟩⟩
    · let U := T.image (fun i : S ↦ i.val)
      have hUS : U ⊆ S := by
        intro i hi
        obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hi
        exact x.property
      have hUrow : ∀ j, (∑ i ∈ U, row i j)=0 := by
        intro j
        rw [Finset.sum_image (fun a _ b _ h ↦ Subtype.ext h)]
        exact hTrow j
      have hUrhs : (∑ i ∈ U, rhs i)=1 := by
        rw [Finset.sum_image (fun a _ b _ h ↦ Subtype.ext h)]
        exact hTrhs
      rcases hcircuit U hUS hUrow with h | h
      · rw [h,Finset.sum_empty] at hUrhs
        exact False.elim (zero_ne_one hUrhs)
      · rw [h,hrhs] at hUrhs
        exact False.elim (zero_ne_one hUrhs)

/-- Every obstruction to a nonempty cyclic lift contains a bounded
parity circuit of actual quotient rivals with inconsistent total carry.
All nonempty proper subfamilies have nonzero parity sum. -/
theorem exists_carry_obstruction_parity_circuit
    {n M : ℕ} (hn : 0 < n) (v : Fin n → ZMod (2*M)) (q : Fin n → ZMod M)
    (hobs : HasCyclicLiftCarryObstruction v q) :
    ∃ S : Finset {c : Fin n → ℤ // Witness q 0 c},
      S.Nonempty ∧ S.card ≤ n ∧
      (∀ j, (∑ c ∈ S, (c.val j : ZMod 2))=0) ∧
      (∑ c ∈ S, cyclicRivalCarry v c.val) ≠ (S.card : ZMod 2) ∧
      ∀ U : Finset {c : Fin n → ℤ // Witness q 0 c}, U ⊆ S →
        (∀ j, (∑ c ∈ U, (c.val j : ZMod 2))=0) → U=∅ ∨ U=S := by
  classical
  obtain ⟨S,hcard,hrow,hcarry⟩ := exists_carry_obstruction_card_le_length hn v q hobs
  let rhs := fun c : {c : Fin n → ℤ // Witness q 0 c} ↦ 1-cyclicRivalCarry v c.val
  have hrhs : (∑ c ∈ S, rhs c)=1 := by
    have hzero : (∑ c ∈ S, rhs c) ≠ 0 := by
      intro h
      simp only [rhs,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,mul_one] at h
      exact hcarry (sub_eq_zero.mp h).symm
    have hcases : ∀ z : ZMod 2, z=0 ∨ z=1 := by decide
    exact (hcases _).resolve_left hzero
  obtain ⟨T,hTS,hne,hTrow,hTrhs,hcircuit⟩ := binary_obstruction_contains_parity_circuit
    (fun c : {c : Fin n → ℤ // Witness q 0 c} ↦ fun j ↦ (c.val j : ZMod 2)) rhs S hrow hrhs
  refine ⟨T,hne,(Finset.card_le_card hTS).trans hcard,hTrow,?_,hcircuit⟩
  intro h
  simp only [rhs,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,h,sub_self] at hTrhs
  exact zero_ne_one hTrhs

/-- Nonexistence of a cyclic lift is exactly the existence of an
inconsistent carry circuit on at most the tuple length many actual rivals.
This refines the complete certificate criterion without a new open input. -/
theorem no_valid_cyclic_lift_iff_carry_circuit
    {n M : ℕ} [NeZero M] (hn : 0 < n)
    (v : Fin n → ZMod (2*M)) (q : Fin n → ZMod M)
    (hquot : ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (v i)=q i) :
    ¬(∃ g : Fin n → ZMod (2*M), ValidTuple g ∧
      ∀ i, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i)=q i) ↔
    ∃ S : Finset {c : Fin n → ℤ // Witness q 0 c},
      S.Nonempty ∧ S.card ≤ n ∧
      (∀ j, (∑ c ∈ S, (c.val j : ZMod 2))=0) ∧
      (∑ c ∈ S, cyclicRivalCarry v c.val) ≠ (S.card : ZMod 2) ∧
      ∀ U : Finset {c : Fin n → ℤ // Witness q 0 c}, U ⊆ S →
        (∀ j, (∑ c ∈ U, (c.val j : ZMod 2))=0) → U=∅ ∨ U=S := by
  rw [no_valid_cyclic_lift_iff_finite_carry_obstruction v q hquot]
  exact ⟨exists_carry_obstruction_parity_circuit hn v q,
    fun ⟨S,_,_,hrow,hcarry,_⟩ ↦ ⟨S,hrow,hcarry⟩⟩

/-- Removing any chosen row of a parity circuit makes arbitrary
right-hand sides solvable on the remaining circuit rows. This is a local
statement about the selected rows, not validity against every rival. -/
theorem parity_circuit_equations_solvable_after_erasing
    {n : ℕ} {I : Type*} [DecidableEq I] (row : I → Fin n → ZMod 2) (S : Finset I)
    (hrow : ∀ j, (∑ i ∈ S, row i j)=0)
    (hcircuit : ∀ U : Finset I, U ⊆ S →
      (∀ j, (∑ i ∈ U, row i j)=0) → U=∅ ∨ U=S)
    (rhs : I → ZMod 2) (a : I) (ha : a ∈ S) :
    ∃ b : Fin n → ZMod 2, ∀ i ∈ S.erase a, (∑ j, row i j*b j)=rhs i := by
  classical
  let total := ∑ i ∈ S.erase a, rhs i
  let adjusted := fun i ↦ if i=a then -total else rhs i
  have hadjusted (i : I) (hi : i ∈ S.erase a) : adjusted i=rhs i := by
    exact if_neg (Finset.mem_erase.mp hi).1
  have hzero : (∑ i ∈ S, adjusted i)=0 := by
    rw [← Finset.sum_erase_add _ _ ha]
    rw [Finset.sum_congr rfl (fun i hi ↦ hadjusted i hi)]
    change total+(if a=a then -total else rhs a)=0
    rw [if_pos rfl]
    exact add_neg_cancel total
  obtain ⟨b,hb⟩ := (binary_equations_on_parity_circuit_iff row S hrow hcircuit adjusted).mpr hzero
  exact ⟨b,fun i hi ↦ (hb i (Finset.mem_of_mem_erase hi)).trans (hadjusted i hi)⟩

end MinModulus
