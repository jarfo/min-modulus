/-
# Minimal support transversals for protected quarter descent

Deleting the whole complement of a protected quarter support gives a valid
recursive tuple but can lose too many coordinates.  This file shrinks that
complement to an inclusion-minimal support transversal.  Every deleted
coordinate then has a private half witness whose only nonzero coefficient on
the deletion set is that coordinate.  These private witnesses are distinct,
so the dimension loss is represented by countable witness data.
-/
import MinModulus.G1QuarterQuartetTrappedKernel

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- An inclusion-minimal support transversal, expressed by failure after
erasing any one of its coordinates. -/
def MinimalWitnessSupportTransversal
    (g : Fin m → G) (h : G) (B : Finset (Fin m)) : Prop :=
  WitnessSupportTransversal g h B ∧
    ∀ b ∈ B, ¬ WitnessSupportTransversal g h (B.erase b)

/-- Every finite support transversal contains a cardinality-minimal, hence
inclusion-minimal, subtransversal. -/
theorem exists_minimalWitnessSupportTransversal_subset
    (g : Fin m → G) (h : G) {B : Finset (Fin m)}
    (hB : WitnessSupportTransversal g h B) :
    ∃ B₀ : Finset (Fin m), B₀ ⊆ B ∧
      MinimalWitnessSupportTransversal g h B₀ := by
  classical
  let F : Finset (Finset (Fin m)) :=
    B.powerset.filter (WitnessSupportTransversal g h)
  have hF : F.Nonempty := by
    refine ⟨B, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Subset.rfl), hB⟩
  obtain ⟨B₀, hB₀F, hmin⟩ := Finset.exists_min_image F Finset.card hF
  have hB₀mem := Finset.mem_filter.mp hB₀F
  refine ⟨B₀, Finset.mem_powerset.mp hB₀mem.1, hB₀mem.2, ?_⟩
  intro b hb hErase
  have hEraseSub : B₀.erase b ⊆ B :=
    (Finset.erase_subset b B₀).trans (Finset.mem_powerset.mp hB₀mem.1)
  have hEraseF : B₀.erase b ∈ F :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hEraseSub, hErase⟩
  have hle := hmin (B₀.erase b) hEraseF
  have hlt := Finset.card_erase_lt_of_mem hb
  omega

/-- Every coordinate of a minimal support transversal has a private witness:
the witness is nonzero there and zero at every other transversal coordinate. -/
theorem exists_private_witness_of_minimalSupportTransversal
    (g : Fin m → G) (h : G) {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    {b : Fin m} (hb : b ∈ B) :
    ∃ c : Fin m → ℤ, Witness g h c ∧ c b ≠ 0 ∧
      ∀ a ∈ B, a ≠ b → c a = 0 := by
  classical
  have hnot := hmin.2 b hb
  unfold WitnessSupportTransversal at hnot
  push Not at hnot
  obtain ⟨c, hc, hzero⟩ := hnot
  obtain ⟨i, hiB, hci⟩ := hmin.1 c hc
  have hib : i = b := by
    by_contra hne
    exact hci (hzero i (Finset.mem_erase.mpr ⟨hne, hiB⟩))
  subst i
  refine ⟨c, hc, hci, ?_⟩
  intro a ha hab
  exact hzero a (Finset.mem_erase.mpr ⟨hab, ha⟩)

/-- A canonical private witness selected for each coordinate of a minimal
support transversal. -/
noncomputable def minimalSupportPrivateWitness
    (g : Fin m → G) (h : G) {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : {i : Fin m // i ∈ B}) : Fin m → ℤ :=
  Classical.choose
    (exists_private_witness_of_minimalSupportTransversal
      g h hmin b.property)

theorem minimalSupportPrivateWitness_isWitness
    (g : Fin m → G) (h : G) {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : {i : Fin m // i ∈ B}) :
    Witness g h (minimalSupportPrivateWitness g h hmin b) :=
  (Classical.choose_spec
    (exists_private_witness_of_minimalSupportTransversal
      g h hmin b.property)).1

theorem minimalSupportPrivateWitness_ne_zero
    (g : Fin m → G) (h : G) {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : {i : Fin m // i ∈ B}) :
    minimalSupportPrivateWitness g h hmin b b ≠ 0 :=
  (Classical.choose_spec
    (exists_private_witness_of_minimalSupportTransversal
      g h hmin b.property)).2.1

theorem minimalSupportPrivateWitness_eq_zero_of_ne
    (g : Fin m → G) (h : G) {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : {i : Fin m // i ∈ B})
    {a : Fin m} (ha : a ∈ B) (hab : a ≠ b) :
    minimalSupportPrivateWitness g h hmin b a = 0 :=
  (Classical.choose_spec
    (exists_private_witness_of_minimalSupportTransversal
      g h hmin b.property)).2.2 a ha hab

/-- Distinct deleted coordinates select distinct private witnesses.  Thus the
transversal cardinality injects into an explicit family of half witnesses. -/
theorem minimalSupportPrivateWitness_injective
    (g : Fin m → G) (h : G) {B : Finset (Fin m)}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Function.Injective (minimalSupportPrivateWitness g h hmin) := by
  intro b₁ b₂ heq
  apply Subtype.ext
  by_contra hne
  have hnz := minimalSupportPrivateWitness_ne_zero g h hmin b₁
  have hz := minimalSupportPrivateWitness_eq_zero_of_ne
    g h hmin b₂ b₁.property hne
  apply hnz
  calc
    minimalSupportPrivateWitness g h hmin b₁ b₁ =
        minimalSupportPrivateWitness g h hmin b₂ b₁ := congrFun heq b₁
    _ = 0 := hz

/-- The quantitative protected-descent package: `B` is an external minimal
support transversal, deleting exactly `B` retains `m-B.card` coordinates, and
every deleted coordinate owns a private half witness. -/
def ProtectedQuarterMinimalSupportDescent
    {N M K : ℕ} [NeZero N]
    (g : Fin m → ZMod N) (q : Fin m → ℤ) : Prop :=
  ∃ B : Finset (Fin m),
    B ⊆ Finset.univ \ coefficientSupport q ∧
    MinimalWitnessSupportTransversal g (M : ZMod N) B ∧
    AdmitsValidTupleWithWitness (m - B.card) M (K : ZMod M) ∧
    ∀ b ∈ B, ∃ c : Fin m → ℤ,
      Witness g (M : ZMod N) c ∧ c b ≠ 0 ∧
        ∀ a ∈ B, a ≠ b → c a = 0

/-- If no half witness is trapped inside the protected quarter support, shrink
its complementary support transversal before descending.  The result retains
`m-B.card` coordinates and exposes a private half-witness layer for every
coordinate actually deleted. -/
theorem quarterWitness_minimalExternalSupportDescent
    {N M K : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
    (g : Fin m → ZMod N) (hg : ValidTuple g)
    {t : ZMod N} {q : Fin m → ℤ}
    (ht : t + t = (M : ZMod N)) (hq : Witness g t q)
    (hkernel : ∀ c : Fin m → ℤ, Witness g (M : ZMod N) c →
      (∀ i : Fin m, q i = 0 → c i = 0) → False) :
    ProtectedQuarterMinimalSupportDescent (M := M) (K := K) g q := by
  classical
  let P : Finset (Fin m) := coefficientSupport q
  let Bfull : Finset (Fin m) := Finset.univ \ P
  have hfull : WitnessSupportTransversal g (M : ZMod N) Bfull := by
    intro c hc
    by_contra hnone
    push Not at hnone
    exact hkernel c hc (by
      intro i hqi
      have hi : i ∈ Bfull := by
        simp [Bfull, P, coefficientSupport, hqi]
      exact hnone i hi)
  obtain ⟨B, hBsub, hmin⟩ :=
    exists_minimalWitnessSupportTransversal_subset
      g (M : ZMod N) hfull
  have hqzero : ∀ j ∈ B, q j = 0 := by
    intro j hjB
    have hjfull := hBsub hjB
    have hjnotP : j ∉ P := (Finset.mem_sdiff.mp hjfull).2
    by_contra hqj
    exact hjnotP (by simpa [P] using hqj)
  have hrec : AdmitsValidTupleWithWitness
      (m - B.card) M (K : ZMod M) :=
    quarterWitness_supportTransversal_recursive
      hN hM hK g hg ht hq B hmin.1 hqzero
  refine ⟨B, ?_, hmin, hrec, ?_⟩
  · simpa [Bfull, P] using hBsub
  · intro b hb
    exact exists_private_witness_of_minimalSupportTransversal
      g (M : ZMod N) hmin hb

/-- The `(0,0,2)` residual triangle admits the dimension-sensitive minimal
support-transversal descent, rather than only the fixed four-coordinate
specialization. -/
theorem exactTriangleZeroZeroTwo_minimalSupportDescent
    {N M K : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
    (g : Fin m → ZMod N) (hg : ValidTuple g)
    (hprofile : WitnessExactTriangleZeroZeroTwo g (M : ZMod N)) :
    ∃ t : ZMod N, ∃ q : Fin m → ℤ,
      t + t = (M : ZMod N) ∧ Witness g t q ∧
        ProtectedQuarterMinimalSupportDescent (M := M) (K := K) g q := by
  obtain ⟨t, x, y, a, b, _hxy, _hab, _hxa, _hxb, _hya, _hyb,
    ht, hq, hkernel⟩ :=
    exactTriangleZeroZeroTwo_no_halfWitness_supportedOn_quarterPair
      g hg (half_add_half hN) hprofile
  refine ⟨t, balancedPairCoeffs x y a b, ht, hq, ?_⟩
  exact quarterWitness_minimalExternalSupportDescent
    hN hM hK g hg ht hq hkernel

/-- The all-zero residual triangle admits the same dimension-sensitive
minimal support-transversal descent. -/
theorem exactTriangleAllZero_minimalSupportDescent
    {N M K : ℕ} [NeZero N]
    (hN : N = 2 * M) (hM : M = 2 * K) (hK : 0 < K)
    (g : Fin m → ZMod N) (hg : ValidTuple g)
    (hall : WitnessExactTriangleAllZero g (M : ZMod N)) :
    ∃ t : ZMod N, ∃ q : Fin m → ℤ,
      t + t = (M : ZMod N) ∧ Witness g t q ∧
        ProtectedQuarterMinimalSupportDescent (M := M) (K := K) g q := by
  obtain ⟨t, x, d, y, z, _hxd, _hyz, _hxy, _hxz, _hdy, _hdz,
    ht, hq, hkernel⟩ :=
    exactTriangleAllZero_no_halfWitness_supportedOn_quarterPair
      g hg (half_add_half hN) hall
  refine ⟨t, balancedPairCoeffs x d y z, ht, hq, ?_⟩
  exact quarterWitness_minimalExternalSupportDescent
    hN hM hK g hg ht hq hkernel

end MinModulus
