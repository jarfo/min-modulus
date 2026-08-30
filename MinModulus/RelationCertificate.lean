/-
# Relation-matrix certificates for the odd top window

A square integer matrix whose rows are relations among a tuple annihilates
every coordinate by its determinant.  This file formalizes that adjugate
argument and connects a determinant `±(2^(m+1)-1)` directly to the chain-free
Mersenne endpoint in `OddOrder.lean`.
-/
import MinModulus.OddOrder
import Mathlib.LinearAlgebra.Matrix.Adjugate

namespace MinModulus

open Finset Matrix

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The rows of `A` are integer relations among the coordinates of `h`. -/
def MatrixRelations (A : Matrix (Fin m) (Fin m) ℤ) (h : Fin m → G) : Prop :=
  ∀ i, ∑ j, A i j • h j = 0

/-- **Adjugate annihilation.** If every row of a square integer matrix is a
relation among `h`, then the determinant annihilates every coordinate.

This is the group-valued form of `adj(A) A = det(A) I`; it does not require
`G` itself to be a module presented by the matrix. -/
theorem det_zsmul_eq_zero_of_matrixRelations (A : Matrix (Fin m) (Fin m) ℤ)
    (h : Fin m → G) (hrel : MatrixRelations A h) (j : Fin m) :
    A.det • h j = 0 := by
  have hzero : ∑ i, A.adjugate j i • (∑ k, A i k • h k) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hrel i, smul_zero]
  have hexpand :
      (∑ i, A.adjugate j i • (∑ k, A i k • h k)) =
        ∑ k, (A.adjugate * A) j k • h k := by
    simp_rw [smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [Matrix.mul_apply, Finset.sum_smul]
  rw [hexpand, Matrix.adjugate_mul] at hzero
  simpa [Matrix.one_apply] using hzero

/-! ### The exceptional non-chain certificate at order 15 -/

/-- Relation matrix for the torsion system
`2h₀+h₁+h₂=0`, `-h₀+2h₁+h₂=0`, `3h₂=0` carried by the
exceptional valid class `{0,1,3,10}` modulo `15`. -/
def torsion15RelationMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2, 1, 1; -1, 2, 1; 0, 0, 3]

/-- The exceptional torsion relation system is a genuine Mersenne
certificate: its determinant is `2^4-1 = 15`. -/
@[simp] theorem torsion15RelationMatrix_det : torsion15RelationMatrix.det = 15 := by
  decide

section Finite

variable [Fintype G]

/-- **Relation-matrix Mersenne certificate.** If a dissociated tuple spans a
finite cyclic group and satisfies a square relation system of determinant
`±(2^(m+1)-1)`, then the group has at least `2^(m+1)-1` elements.

This is the concrete matrix interface required by the non-chain branch of the
top-window roadmap: a future extraction theorem only has to produce `A`, its
row relations, and the signed determinant identity. -/
theorem mersenne_card_bound_of_relation_matrix (g : G) (h : Fin m → G)
    (A : Matrix (Fin m) (Fin m) ℤ)
    (hgen : AddSubgroup.zmultiples g = ⊤)
    (hspan : AddSubgroup.closure (Set.range h) = ⊤)
    (hdis : Function.Injective fun S : Finset (Fin m) => ∑ i ∈ S, h i)
    (hrel : MatrixRelations A h)
    (hdet : A.det = (2 ^ (m + 1) - 1 : ℕ) ∨
      A.det = -((2 ^ (m + 1) - 1 : ℕ) : ℤ)) :
    2 ^ (m + 1) - 1 ≤ Fintype.card G := by
  apply mersenne_certificate_card_bound_of_span g h hgen hspan hdis
  intro i
  have hi := det_zsmul_eq_zero_of_matrixRelations A h hrel i
  rcases hdet with hdet | hdet
  · rw [hdet] at hi
    rw [natCast_zsmul] at hi
    exact hi
  · rw [hdet, neg_smul] at hi
    have hpos : ((2 ^ (m + 1) - 1 : ℕ) : ℤ) • h i = 0 := neg_eq_zero.mp hi
    rw [natCast_zsmul] at hpos
    exact hpos

/-- The determinant bridge applied to the known non-chain torsion system at
the first odd threshold. -/
theorem torsion15_relation_card_bound (g : G) (h : Fin 3 → G)
    (hgen : AddSubgroup.zmultiples g = ⊤)
    (hspan : AddSubgroup.closure (Set.range h) = ⊤)
    (hdis : Function.Injective fun S : Finset (Fin 3) => ∑ i ∈ S, h i)
    (hrel : MatrixRelations torsion15RelationMatrix h) :
    15 ≤ Fintype.card G := by
  have hbound := mersenne_card_bound_of_relation_matrix g h torsion15RelationMatrix
    hgen hspan hdis hrel (Or.inl torsion15RelationMatrix_det)
  norm_num at hbound ⊢
  exact hbound

end Finite

end MinModulus
