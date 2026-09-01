/-
# Witness kernels on retained subtuples

The exact halving-kernel theorem is localized here to an arbitrary coordinate
embedding.  A relation on a retained subtuple is extended by zero to the
original tuple.  Hence the retained coordinatewise quotient is valid exactly
when no original half witness is supported entirely on the retained image.
-/
import MinModulus.G1QuotientWitnessKernel

namespace MinModulus

open Finset

variable {n k : ℕ} {G : Type*} [AddCommGroup G]

/-- Extending a finite family by zero along an embedding preserves its sum. -/
theorem sum_extend_embedding_zero
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    {R : Type*} [AddCommMonoid R] (e : A ↪ B) (f : A → R) :
    (∑ j, Function.extend e f (fun _ ↦ 0) j) = ∑ i, f i := by
  classical
  let S : Finset B := Finset.univ.image e
  calc
    (∑ j, Function.extend e f (fun _ ↦ 0) j) =
        ∑ j ∈ S, Function.extend e f (fun _ ↦ 0) j := by
      rw [← Fintype.sum_extend_by_zero S
        (Function.extend e f (fun _ ↦ 0))]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ S
      · simp [hj]
      · have hnone : ¬ ∃ i, e i = j := by
          rintro ⟨i, rfl⟩
          exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
        simp [hj, Function.extend_apply' f (fun _ ↦ 0) j hnone]
    _ = ∑ i, f i := by
      dsimp [S]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro i _
        exact e.injective.extend_apply f (fun _ ↦ 0) i
      · exact e.injective.injOn

/-- The weighted sum of a coefficient vector extended by zero is the
weighted sum on the embedded subtuple. -/
theorem sum_zsmul_extend_embedding_zero
    (e : Fin k ↪ Fin n) (c : Fin k → ℤ) (g : Fin n → G) :
    (∑ j, Function.extend e c (fun _ ↦ 0) j • g j) =
      ∑ i, c i • g (e i) := by
  classical
  calc
    (∑ j, Function.extend e c (fun _ ↦ 0) j • g j) =
        ∑ j, Function.extend e (fun i ↦ c i • g (e i))
          (fun _ ↦ 0) j := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [e.injective.extend_apply c (fun _ ↦ 0) i,
          e.injective.extend_apply (fun i ↦ c i • g (e i))
            (fun _ ↦ 0) i]
      · rw [Function.extend_apply' c (fun _ ↦ 0) j hj,
          Function.extend_apply' (fun i ↦ c i • g (e i))
            (fun _ ↦ 0) j hj, zero_smul]
    _ = ∑ i, c i • g (e i) :=
      sum_extend_embedding_zero e (fun i ↦ c i • g (e i))

/-- A witness on a retained subtuple is exactly a witness on the original
tuple whose coefficient vector is extended by zero off the retained image. -/
theorem witness_extend_embedding_iff
    (e : Fin k ↪ Fin n) (g : Fin n → G) {h : G} (c : Fin k → ℤ) :
    Witness g h (Function.extend e c (fun _ ↦ 0)) ↔
      Witness (fun i ↦ g (e i)) h c := by
  classical
  constructor
  · intro hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hzero
      apply hc.1
      funext j
      by_cases hj : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [e.injective.extend_apply c (fun _ ↦ 0) i, hzero]
        rfl
      · exact Function.extend_apply' c (fun _ ↦ 0) j hj
    · intro i
      have hi := hc.2.1 (e i)
      rwa [e.injective.extend_apply c (fun _ ↦ 0) i] at hi
    · rw [← sum_extend_embedding_zero e c]
      exact hc.2.2.1
    · rw [← sum_zsmul_extend_embedding_zero e c g]
      exact hc.2.2.2
  · intro hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hzero
      apply hc.1
      funext i
      have hi := congrFun hzero (e i)
      rwa [e.injective.extend_apply c (fun _ ↦ 0) i] at hi
    · intro j
      by_cases hj : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [e.injective.extend_apply c (fun _ ↦ 0) i]
        exact hc.2.1 i
      · rw [Function.extend_apply' c (fun _ ↦ 0) j hj]
        omega
    · rw [sum_extend_embedding_zero e c]
      exact hc.2.2.1
    · rw [sum_zsmul_extend_embedding_zero e c g]
      exact hc.2.2.2

/-- Validity is hereditary under retaining an embedded subtuple. -/
theorem validTuple_embedding
    (e : Fin k ↪ Fin n) (g : Fin n → G) (hg : ValidTuple g) :
    ValidTuple (fun i ↦ g (e i)) := by
  rw [validTuple_iff_no_zero_witness]
  intro c hc
  exact (validTuple_iff_no_zero_witness g).mp hg
    (Function.extend e c (fun _ ↦ 0))
    ((witness_extend_embedding_iff e g c).2 hc)

/-- Exact cyclic kernel on a retained coordinate embedding.  A downstairs
zero witness is equivalent to the zero-extended original half witness. -/
theorem embeddedZmodCast_zeroWitness_iff_extendedHalfWitness
    {N M : ℕ} [NeZero N] (hN : N = 2 * M)
    (e : Fin k ↪ Fin n) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (c : Fin k → ℤ) :
    let f : ZMod N →+* ZMod M :=
      ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
    Witness (fun i ↦ f (g (e i))) 0 c ↔
      Witness g (M : ZMod N) (Function.extend e c (fun _ ↦ 0)) := by
  let f : ZMod N →+* ZMod M :=
    ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
  dsimp only
  calc
    Witness (fun i ↦ f (g (e i))) 0 c ↔
        Witness (fun i ↦ g (e i)) (M : ZMod N) c :=
      zmodCast_zeroWitness_iff_halfWitness hN (fun i ↦ g (e i))
        (validTuple_embedding e g hg) c
    _ ↔ Witness g (M : ZMod N)
        (Function.extend e c (fun _ ↦ 0)) :=
      (witness_extend_embedding_iff e g c).symm

/-- The retained coordinatewise quotient is valid exactly when no original
half witness is supported on the retained image. -/
theorem validTuple_embeddedZmodCast_iff_no_supportedHalfWitness
    {N M : ℕ} [NeZero N] (hN : N = 2 * M)
    (e : Fin k ↪ Fin n) (g : Fin n → ZMod N) (hg : ValidTuple g) :
    let f : ZMod N →+* ZMod M :=
      ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
    ValidTuple (fun i ↦ f (g (e i))) ↔
      ∀ c : Fin k → ℤ,
        ¬ Witness g (M : ZMod N) (Function.extend e c (fun _ ↦ 0)) := by
  let f : ZMod N →+* ZMod M :=
    ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
  dsimp only
  rw [validTuple_iff_no_zero_witness]
  constructor
  · intro hvalid c hc
    exact hvalid c
      ((embeddedZmodCast_zeroWitness_iff_extendedHalfWitness
        hN e g hg c).2 hc)
  · intro hno c hc
    exact hno c
      ((embeddedZmodCast_zeroWitness_iff_extendedHalfWitness
        hN e g hg c).1 hc)

end MinModulus
