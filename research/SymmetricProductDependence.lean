import MinModulus.AbelianMin

/-!
The seven nonempty squarefree products of symmetric group-algebra generators
need not be linearly independent, even for a valid tuple at an odd modulus.
This is a failed proof route for G2, not a min-modulus counterexample.
-/

namespace MinModulus.Research
open Finset

/-- A valid four-coordinate control at the sharp odd modulus. -/
def symmetricControl : Fin 4 → ZMod 15 := ![0,1,3,7]

private theorem symmetricControl_bounded :
    ∀ k : Fin 4 → Fin 5, (∑ i, (k i).val)=4 →
      (∑ i, (k i).val • symmetricControl i)=(∑ i, symmetricControl i) →
      ∀ i, (k i).val=1 := by
  decide +kernel

/-- The control satisfies the actual project validity predicate. -/
theorem symmetricControl_valid : ValidTuple symmetricControl := by
  intro k hcount hsum
  have hb (i : Fin 4) : k i < 5 := by
    have h := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (k j)) (Finset.mem_univ i)
    rw [hcount] at h
    omega
  exact symmetricControl_bounded (fun i ↦ ⟨k i,hb i⟩) hcount hsum

/-- Cyclic convolution on coefficient functions for F₂[Z/15Z]. -/
def cyclicConvolution15 (f h : ZMod 15 → ZMod 2) (x : ZMod 15) : ZMod 2 :=
  ∑ y : ZMod 15, f y * h (x-y)

/-- The symmetric generator e_a+e_{-a}, in coefficient notation. -/
def symmetricGenerator15 (a x : ZMod 15) : ZMod 2 :=
  (if x=a then 1 else 0)+(if x= -a then 1 else 0)

/-- Nonempty products indexed by their binary support masks, minus one. -/
def symmetricProducts15 : Fin 7 → ZMod 15 → ZMod 2 :=
  let a := symmetricGenerator15 1
  let b := symmetricGenerator15 3
  let c := symmetricGenerator15 7
  ![a,b,cyclicConvolution15 a b,c,cyclicConvolution15 a c,
    cyclicConvolution15 b c,cyclicConvolution15 (cyclicConvolution15 a b) c]

/-- A nonzero coefficient vector for the dependence. -/
def symmetricRelation15 : Fin 7 → ZMod 2 := ![0,1,0,1,1,1,1]

/-- b+c+ac+bc+abc=0 for a=e₁+e₋₁, b=e₃+e₋₃, c=e₇+e₋₇. -/
theorem symmetricProducts15_relation :
    ∑ i : Fin 7, symmetricRelation15 i • symmetricProducts15 i=0 := by
  funext x
  change (∑ i : Fin 7, symmetricRelation15 i * symmetricProducts15 i x)=0
  revert x
  decide +kernel

/-- The seven products from the valid control are linearly dependent. -/
theorem symmetricProducts15_not_linearIndependent :
    ¬ LinearIndependent (ZMod 2) symmetricProducts15 := by
  intro hi
  have hz := (linearIndependent_iff'.mp hi) Finset.univ symmetricRelation15
    symmetricProducts15_relation (1 : Fin 7) (Finset.mem_univ _)
  norm_num [symmetricRelation15] at hz

/-- Squaring the first generator doubles its group index. -/
theorem symmetricGenerator15_square :
    cyclicConvolution15 (symmetricGenerator15 1) (symmetricGenerator15 1)=
      symmetricGenerator15 2 := by
  funext x
  revert x
  decide +kernel

/-- Replace the last product by the Frobenius square of the first one. -/
def symmetricRecovered15 : Fin 7 → ZMod 15 → ZMod 2 :=
  ![symmetricProducts15 0,symmetricProducts15 1,symmetricProducts15 2,
    symmetricProducts15 3,symmetricProducts15 4,symmetricProducts15 5,
    cyclicConvolution15 (symmetricProducts15 0) (symmetricProducts15 0)]

/-- One Frobenius iterate repairs this specific seven-vector family. -/
theorem symmetricRecovered15_linearIndependent :
    LinearIndependent (ZMod 2) symmetricRecovered15 := by
  rw [Fintype.linearIndependent_iff]
  decide +kernel

end MinModulus.Research
