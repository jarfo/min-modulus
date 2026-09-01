/-
# Retaining the all-zero quarter witness in the recursive descent

The two-pivot valid branch is strengthened here so that its output is one
explicit retained tuple which is both valid modulo the halved modulus and
carries the transported quarter relation as its new half witness.
-/
import MinModulus.G1AvoidanceQuarterQuartetPivot

namespace MinModulus

open Finset

variable {m n k : ℕ}

/-- A valid cyclic tuple together with a witness at a specified target. -/
def AdmitsValidTupleWithWitness (n N : ℕ) (h : ZMod N) : Prop :=
  ∃ g : Fin n → ZMod N, ValidTuple g ∧
    ∃ c : Fin n → ℤ, Witness g h c

/-- Restricting a function along an embedding and extending it by zero
recovers the original function when it vanishes off the image. -/
theorem extend_restrict_embedding_eq_of_zero_off
    {R : Type*} [Zero R] (e : Fin k ↪ Fin n) (c : Fin n → R)
    (hout : ∀ j : Fin n, (∀ i : Fin k, e i ≠ j) → c j = 0) :
    Function.extend e (fun i ↦ c (e i)) (fun _ ↦ 0) = c := by
  classical
  funext j
  by_cases hj : ∃ i : Fin k, e i = j
  · obtain ⟨i, rfl⟩ := hj
    exact e.injective.extend_apply (fun i ↦ c (e i)) (fun _ ↦ 0) i
  · rw [Function.extend_apply' (fun i ↦ c (e i)) (fun _ ↦ 0) j hj]
    exact (hout j (by
      intro i hi
      exact hj ⟨i, hi⟩)).symm

/-- The strong all-zero recursion.  When `N=2M=4K`, either deleting the
chosen triangle edge yields one explicit valid `(m-2)`-tuple modulo `M`
carrying a witness at its half target `K`, or an original half witness avoids
both edge vertices. -/
theorem exactTriangleAllZero_recursiveHalfWitness_or_pairAvoider
    {N M K : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
    (g : Fin m → ZMod N) (hg : ValidTuple g)
    (hall : WitnessExactTriangleAllZero g (M : ZMod N)) :
    AdmitsValidTupleWithWitness (m - 2) M (K : ZMod M) ∨
      ∃ a b : Fin m, a ≠ b ∧
        ∃ r : Fin m → ℤ,
          Witness g (M : ZMod N) r ∧ r a = 0 ∧ r b = 0 := by
  classical
  obtain ⟨t, a, b, q, cAB, cBD, cDA, hab, ht,
    hq, hqa, hqb, _hcAB, _hABhit, _hcBD, _hBDhit,
    _hcDA, _hDAhit⟩ :=
    exactTriangleAllZero_quarterTwoPivot g hg (half_add_half hN) hall
  by_cases havoid : ∃ r : Fin m → ℤ,
      Witness g (M : ZMod N) r ∧ r a = 0 ∧ r b = 0
  · exact Or.inr ⟨a, b, hab, havoid⟩
  · left
    let B : Finset (Fin m) := {a, b}
    let R : Finset (Fin m) := Finset.univ \ B
    let e : Fin R.card ↪ Fin m := (R.orderEmbOfFin rfl).toEmbedding
    let f : ZMod N →+* ZMod M :=
      ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
    let gR : Fin R.card → ZMod M := fun i ↦ f (g (e i))
    have haout : ∀ i : Fin R.card, e i ≠ a := by
      intro i hei
      have heiR : e i ∈ R := R.orderEmbOfFin_mem rfl i
      exact (Finset.mem_sdiff.mp heiR).2 (by simp [B, hei])
    have hbout : ∀ i : Fin R.card, e i ≠ b := by
      intro i hei
      have heiR : e i ∈ R := R.orderEmbOfFin_mem rfl i
      exact (Finset.mem_sdiff.mp heiR).2 (by simp [B, hei])
    have hvalidR : ValidTuple gR := by
      apply (validTuple_embeddedZmodCast_iff_no_supportedHalfWitness
        hN e g hg).2
      intro c hc
      have hca : Function.extend e c (fun _ ↦ 0) a = 0 :=
        Function.extend_apply' c (fun _ ↦ 0) a (by
          intro hex
          obtain ⟨i, hi⟩ := hex
          exact haout i hi)
      have hcb : Function.extend e c (fun _ ↦ 0) b = 0 :=
        Function.extend_apply' c (fun _ ↦ 0) b (by
          intro hex
          obtain ⟨i, hi⟩ := hex
          exact hbout i hi)
      exact havoid ⟨Function.extend e c (fun _ ↦ 0), hc, hca, hcb⟩
    let qR : Fin R.card → ℤ := fun i ↦ q (e i)
    have hqoff : ∀ j : Fin m, (∀ i : Fin R.card, e i ≠ j) → q j = 0 := by
      intro j hj
      have hjnotR : j ∉ R := by
        intro hjR
        have hjrange : j ∈ Set.range (R.orderEmbOfFin rfl) := by
          simpa using hjR
        obtain ⟨i, hi⟩ := hjrange
        exact hj i hi
      have hjB : j ∈ B := by
        simpa [R] using hjnotR
      rcases Finset.mem_insert.mp hjB with hja | hjb
      · simpa [hja] using hqa
      · have hjb' : j = b := by simpa [B] using hjb
        simpa [hjb'] using hqb
    have hqextend : Function.extend e qR (fun _ ↦ 0) = q := by
      exact extend_restrict_embedding_eq_of_zero_off e q hqoff
    have hqRup : Witness (fun i ↦ g (e i)) t qR := by
      apply (witness_extend_embedding_iff e g qR).1
      rw [hqextend]
      exact hq
    have hqRdown := witness_map_addMonoidHom f.toAddMonoidHom
      (fun i ↦ g (e i)) hqRup
    change Witness gR (f t) qR at hqRdown
    have htcast : f t = (K : ZMod M) :=
      quarterCenter_cast_eq_half hN hM hK t ht
    rw [htcast] at hqRdown
    have hRcard : R.card = m - 2 := by
      have hBcard : B.card = 2 := by simp [B, hab]
      calc
        R.card = Finset.univ.card - B.card := by
          exact Finset.card_sdiff_of_subset (Finset.subset_univ B)
        _ = m - 2 := by simp [hBcard]
    have hout : AdmitsValidTupleWithWitness R.card M (K : ZMod M) :=
      ⟨gR, hvalidR, qR, hqRdown⟩
    simpa [hRcard] using hout

end MinModulus
