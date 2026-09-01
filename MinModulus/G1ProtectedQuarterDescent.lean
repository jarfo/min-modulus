/-
# Protected quarter-layer support descent

A quarter witness can be kept through halving whenever the zero-witness
kernel has a support transversal on coordinates where that quarter vector is
zero.  This file proves the general recursive interface and the complementary
dichotomy: failure produces a half witness supported entirely inside the
protected quarter support.
-/
import MinModulus.G1AvoidanceQuarterQuartetRecursive

namespace MinModulus

open Finset

variable {m : ℕ}

/-- The nonzero coefficient support of an integer vector. -/
def coefficientSupport (c : Fin m → ℤ) : Finset (Fin m) :=
  Finset.univ.filter (fun i ↦ c i ≠ 0)

@[simp] theorem mem_coefficientSupport_iff
    (c : Fin m → ℤ) (i : Fin m) :
    i ∈ coefficientSupport c ↔ c i ≠ 0 := by
  simp [coefficientSupport]

/-- A set meeting the nonzero support of every witness at `h`. -/
def WitnessSupportTransversal
    {G : Type*} [AddCommGroup G]
    (g : Fin m → G) (h : G) (B : Finset (Fin m)) : Prop :=
  ∀ c : Fin m → ℤ, Witness g h c →
    ∃ i : Fin m, i ∈ B ∧ c i ≠ 0

/-- A support transversal disjoint from a protected quarter coefficient
vector yields one explicit valid retained tuple carrying that vector as its
new half witness. -/
theorem quarterWitness_supportTransversal_recursive
    {N M K : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
    (g : Fin m → ZMod N) (hg : ValidTuple g)
    {t : ZMod N} {q : Fin m → ℤ}
    (ht : t + t = (M : ZMod N)) (hq : Witness g t q)
    (B : Finset (Fin m))
    (htrans : WitnessSupportTransversal g (M : ZMod N) B)
    (hqzero : ∀ j ∈ B, q j = 0) :
    AdmitsValidTupleWithWitness (m - B.card) M (K : ZMod M) := by
  classical
  let R : Finset (Fin m) := Finset.univ \ B
  let e : Fin R.card ↪ Fin m := (R.orderEmbOfFin rfl).toEmbedding
  let f : ZMod N →+* ZMod M :=
    ZMod.castHom (show M ∣ N by exact ⟨2, by omega⟩) (ZMod M)
  let gR : Fin R.card → ZMod M := fun i ↦ f (g (e i))
  have hvalidR : ValidTuple gR := by
    apply (validTuple_embeddedZmodCast_iff_no_supportedHalfWitness
      hN e g hg).2
    intro c hc
    obtain ⟨j, hjB, hcj⟩ := htrans
      (Function.extend e c (fun _ ↦ 0)) hc
    have hjout : ¬ ∃ i : Fin R.card, e i = j := by
      rintro ⟨i, hi⟩
      have heiR : e i ∈ R := R.orderEmbOfFin_mem rfl i
      exact (Finset.mem_sdiff.mp heiR).2 (by simpa [hi] using hjB)
    exact hcj (Function.extend_apply' c (fun _ ↦ 0) j hjout)
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
    exact hqzero j hjB
  have hqextend : Function.extend e qR (fun _ ↦ 0) = q :=
    extend_restrict_embedding_eq_of_zero_off e q hqoff
  have hqRup : Witness (fun i ↦ g (e i)) t qR := by
    apply (witness_extend_embedding_iff e g qR).1
    rw [hqextend]
    exact hq
  have hqRdown := witness_map_addMonoidHom f.toAddMonoidHom
    (fun i ↦ g (e i)) hqRup
  change Witness gR (f t) qR at hqRdown
  rw [quarterCenter_cast_eq_half hN hM hK t ht] at hqRdown
  have hRcard : R.card = m - B.card := by
    simpa [R] using
      Finset.card_sdiff_of_subset (Finset.subset_univ B)
  have hout : AdmitsValidTupleWithWitness R.card M (K : ZMod M) :=
    ⟨gR, hvalidR, qR, hqRdown⟩
  simpa [hRcard] using hout

/-- Protecting the entire coefficient support gives an exact alternative.
Either the complementary coordinates already form a support transversal and
one obtains a valid recursive tuple on the protected support, or some original
half witness is supported wholly inside that support. -/
theorem quarterWitness_recursive_or_halfWitness_supported
    {N M K : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
    (g : Fin m → ZMod N) (hg : ValidTuple g)
    {t : ZMod N} {q : Fin m → ℤ}
    (ht : t + t = (M : ZMod N)) (hq : Witness g t q) :
    AdmitsValidTupleWithWitness (coefficientSupport q).card M (K : ZMod M) ∨
      ∃ c : Fin m → ℤ, Witness g (M : ZMod N) c ∧
        ∀ i : Fin m, q i = 0 → c i = 0 := by
  classical
  let P : Finset (Fin m) := coefficientSupport q
  let B : Finset (Fin m) := Finset.univ \ P
  by_cases htrans : WitnessSupportTransversal g (M : ZMod N) B
  · left
    have hqzero : ∀ j ∈ B, q j = 0 := by
      intro j hj
      have hjnotP : j ∉ P := (Finset.mem_sdiff.mp hj).2
      by_contra hqj
      exact hjnotP (by simpa [P] using hqj)
    have hrec := quarterWitness_supportTransversal_recursive
      hN hM hK g hg ht hq B htrans hqzero
    have hcard : m - B.card = P.card := by
      have hPsub : P ⊆ Finset.univ := Finset.subset_univ P
      have hBcard : B.card = m - P.card := by
        simpa [B] using Finset.card_sdiff_of_subset hPsub
      have hPle : P.card ≤ m := by
        have hle := Finset.card_le_card hPsub
        simpa using hle
      omega
    simpa [P, hcard] using hrec
  · right
    unfold WitnessSupportTransversal at htrans
    push Not at htrans
    obtain ⟨c, hc, hzero⟩ := htrans
    refine ⟨c, hc, ?_⟩
    intro i hqi
    have hiB : i ∈ B := by
      simp [B, P, coefficientSupport, hqi]
    exact hzero i hiB

end MinModulus
