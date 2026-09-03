/-
# Minimal transversals for all nonzero odd-primary kernel witnesses

The full coordinate set hits every nonzero cyclic-kernel witness.  Shrinking
it to an inclusion-minimal transversal exposes one private kernel witness per
deleted coordinate.  Deleting that minimal transversal gives the exact cyclic
quotient descent from `G1OddPrimaryWitnessTransversal`.
-/
import MinModulus.G1OddPrimaryWitnessTransversal

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- A coordinate set meeting every witness at every nonzero multiple of the
cyclic-kernel generator. -/
def CyclicKernelSupportTransversal
    (g : Fin m → G) (y : G) (B : Finset (Fin m)) : Prop :=
  ∀ z : ℤ, z • y ≠ 0 → ∀ c : Fin m → ℤ, Witness g (z • y) c →
    ∃ i : Fin m, i ∈ B ∧ c i ≠ 0

/-- An inclusion-minimal transversal for all nonzero cyclic-kernel witness
layers. -/
def MinimalCyclicKernelSupportTransversal
    (g : Fin m → G) (y : G) (B : Finset (Fin m)) : Prop :=
  CyclicKernelSupportTransversal g y B ∧
    ∀ b ∈ B, ¬ CyclicKernelSupportTransversal g y (B.erase b)

/-- The full coordinate set is always a cyclic-kernel support transversal. -/
theorem univ_cyclicKernelSupportTransversal
    (g : Fin m → G) (y : G) :
    CyclicKernelSupportTransversal g y Finset.univ := by
  intro z _hz c hc
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc.1
  exact ⟨i, Finset.mem_univ i, hi⟩

/-- Every finite cyclic-kernel support transversal contains an
inclusion-minimal subtransversal. -/
theorem exists_minimalCyclicKernelSupportTransversal_subset
    (g : Fin m → G) (y : G) {B : Finset (Fin m)}
    (hB : CyclicKernelSupportTransversal g y B) :
    ∃ B₀ : Finset (Fin m), B₀ ⊆ B ∧
      MinimalCyclicKernelSupportTransversal g y B₀ := by
  classical
  let F : Finset (Finset (Fin m)) :=
    B.powerset.filter (CyclicKernelSupportTransversal g y)
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

/-- Every point of a minimal cyclic-kernel transversal owns a witness at a
nonzero kernel target whose only nonzero transversal coordinate is that
point. -/
theorem exists_private_witness_of_minimalCyclicKernelTransversal
    (g : Fin m → G) (y : G) {B : Finset (Fin m)}
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    {b : Fin m} (hb : b ∈ B) :
    ∃ z : ℤ, ∃ c : Fin m → ℤ,
      z • y ≠ 0 ∧ Witness g (z • y) c ∧ c b ≠ 0 ∧
      ∀ a ∈ B, a ≠ b → c a = 0 := by
  classical
  have hnot := hmin.2 b hb
  unfold CyclicKernelSupportTransversal at hnot
  push Not at hnot
  obtain ⟨z, hzne, c, hc, hzero⟩ := hnot
  obtain ⟨i, hiB, hci⟩ := hmin.1 z hzne c hc
  have hib : i = b := by
    by_contra hne
    exact hci (hzero i (Finset.mem_erase.mpr ⟨hne, hiB⟩))
  subst i
  refine ⟨z, c, hzne, hc, hci, ?_⟩
  intro a ha hab
  exact hzero a (Finset.mem_erase.mpr ⟨hab, ha⟩)

/-- Bundled private witness selected at one point of a minimal cyclic-kernel
transversal. -/
structure CyclicKernelPrivateWitnessData
    (g : Fin m → G) (y : G) {B : Finset (Fin m)}
    (b : {i : Fin m // i ∈ B}) where
  scalar : ℤ
  coeff : Fin m → ℤ
  target_ne_zero : scalar • y ≠ 0
  isWitness : Witness g (scalar • y) coeff
  owner_ne_zero : coeff b ≠ 0
  zero_other : ∀ a ∈ B, a ≠ b → coeff a = 0

/-- Canonical private kernel-witness data at each deleted coordinate. -/
noncomputable def minimalCyclicKernelPrivateWitnessData
    (g : Fin m → G) (y : G) {B : Finset (Fin m)}
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (b : {i : Fin m // i ∈ B}) :
    CyclicKernelPrivateWitnessData g y b :=
  let h := exists_private_witness_of_minimalCyclicKernelTransversal
    g y hmin b.property
  { scalar := Classical.choose h
    coeff := Classical.choose (Classical.choose_spec h)
    target_ne_zero := (Classical.choose_spec
      (Classical.choose_spec h)).1
    isWitness := (Classical.choose_spec
      (Classical.choose_spec h)).2.1
    owner_ne_zero := (Classical.choose_spec
      (Classical.choose_spec h)).2.2.1
    zero_other := (Classical.choose_spec
      (Classical.choose_spec h)).2.2.2 }

/-- Distinct deleted coordinates have distinct selected private coefficient
vectors. -/
theorem minimalCyclicKernelPrivateWitness_coeff_injective
    (g : Fin m → G) (y : G) {B : Finset (Fin m)}
    (hmin : MinimalCyclicKernelSupportTransversal g y B) :
    Function.Injective
      (fun b ↦ (minimalCyclicKernelPrivateWitnessData g y hmin b).coeff) := by
  intro b₁ b₂ heq
  apply Subtype.ext
  by_contra hne
  have hnz :=
    (minimalCyclicKernelPrivateWitnessData g y hmin b₁).owner_ne_zero
  have hz :=
    (minimalCyclicKernelPrivateWitnessData g y hmin b₂).zero_other
      b₁ b₁.property hne
  apply hnz
  calc
    (minimalCyclicKernelPrivateWitnessData g y hmin b₁).coeff b₁ =
        (minimalCyclicKernelPrivateWitnessData g y hmin b₂).coeff b₁ :=
      congrFun heq b₁
    _ = 0 := hz

/-- The complement of a minimal support transversal satisfies the embedding
form required by cyclic quotient descent. -/
theorem minimalCyclicKernelTransversal_complement
    (g : Fin m → G) (y : G) {B : Finset (Fin m)}
    (hmin : MinimalCyclicKernelSupportTransversal g y B) :
    let R : Finset (Fin m) := Finset.univ \ B
    let e : Fin R.card ↪ Fin m := (R.orderEmbOfFin rfl).toEmbedding
    CyclicKernelWitnessTransversal g y e := by
  dsimp only
  intro z hz c hc
  obtain ⟨j, hjB, hcj⟩ := hmin.1 z hz c hc
  refine ⟨j, ?_, hcj⟩
  intro i hei
  have heiR : ((Finset.univ \ B).orderEmbOfFin rfl).toEmbedding i ∈
      Finset.univ \ B := (Finset.univ \ B).orderEmbOfFin_mem rfl i
  have heiNotB := (Finset.mem_sdiff.mp heiR).2
  apply heiNotB
  rw [hei]
  exact hjB

/-- Every valid cyclic tuple admits a dimension-sensitive minimal
cyclic-kernel descent.  Each deleted coordinate carries distinct private
witness data at a nonzero kernel target. -/
theorem exists_minimalCyclicKernelTransversal_descent
    {N : ℕ} [NeZero N]
    (g : Fin m → ZMod N) (hg : ValidTuple g) (y : ZMod N) :
    ∃ B : Finset (Fin m),
      MinimalCyclicKernelSupportTransversal g y B ∧
      AdmitsValidTuple (m - B.card) (N / addOrderOf y) ∧
      ∀ b ∈ B, ∃ z : ℤ, ∃ c : Fin m → ℤ,
        z • y ≠ 0 ∧ Witness g (z • y) c ∧ c b ≠ 0 ∧
        ∀ a ∈ B, a ≠ b → c a = 0 := by
  classical
  obtain ⟨B, _hBsub, hmin⟩ :=
    exists_minimalCyclicKernelSupportTransversal_subset
      g y (univ_cyclicKernelSupportTransversal g y)
  let R : Finset (Fin m) := Finset.univ \ B
  let e : Fin R.card ↪ Fin m := (R.orderEmbOfFin rfl).toEmbedding
  have hhit : CyclicKernelWitnessTransversal g y e :=
    minimalCyclicKernelTransversal_complement g y hmin
  have hdesc : AdmitsValidTuple R.card (N / addOrderOf y) :=
    admitsValidTuple_div_addOrderOf_of_cyclicKernelTransversal
      g hg y e hhit
  have hRcard : R.card = m - B.card := by
    simp [R, Finset.card_sdiff_of_subset (Finset.subset_univ B)]
  refine ⟨B, hmin, by simpa [hRcard] using hdesc, ?_⟩
  intro b hb
  exact exists_private_witness_of_minimalCyclicKernelTransversal
    g y hmin hb

/-- For the pure-star torsion element, the minimal-transversal descent keeps
the same two-adic factor and divides only the odd factor. -/
theorem MersenneTorsionPrimeCertificate.exists_minimalTransversal_oddFactorDescent
    {t q ell p : ℕ} [NeZero (2 ^ t * q)]
    {y : ZMod (2 ^ t * q)}
    (hcert : MersenneTorsionPrimeCertificate q ell p y)
    (g : Fin m → ZMod (2 ^ t * q)) (hg : ValidTuple g) :
    ∃ B : Finset (Fin m),
      MinimalCyclicKernelSupportTransversal g y B ∧
      AdmitsValidTuple (m - B.card)
        (2 ^ t * (q / addOrderOf y)) ∧
      ∀ b ∈ B, ∃ z : ℤ, ∃ c : Fin m → ℤ,
        z • y ≠ 0 ∧ Witness g (z • y) c ∧ c b ≠ 0 ∧
        ∀ a ∈ B, a ≠ b → c a = 0 := by
  obtain ⟨B, hmin, hdesc, hprivate⟩ :=
    exists_minimalCyclicKernelTransversal_descent g hg y
  rw [hcert.quotientModulus_eq] at hdesc
  exact ⟨B, hmin, hdesc, hprivate⟩

/-- Pure-star endpoint with a minimal transversal and the resulting strict
odd-factor descent attached to its sole non-capacity branch. -/
def PureEdgeStarLeafOddPrimaryDescentOutcome
    {t q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ t * q))
    (h : ZMod (2 ^ t * q)) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) : Prop :=
  let leaf : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  2 * d + 1 ≤ m + 1 ∨
    (d + 2 ≤ m + 1 ∧
      ∃ j k ell : Fin d,
        center j = leaf k ∧ center ell ∉ Set.range leaf) ∨
    (PureEdgeStarLeafRelativeTorsionAlgebra g h r T a d center ∧
      ∃ i : Fin d, ∃ ell p : ℕ, ∃ B : Finset (Fin (m + 1)),
        2 ≤ ell ∧ ell ≤ d ∧
        (2 ^ ell - 1) • (g (leaf i) - (h + g r)) = 0 ∧
        MersenneTorsionPrimeCertificate q ell p
          (g (leaf i) - (h + g r)) ∧
        orderOf (2 : ZMod p) ≤ d ∧
        MinimalCyclicKernelSupportTransversal g
          (g (leaf i) - (h + g r)) B ∧
        AdmitsValidTuple (m + 1 - B.card)
          (2 ^ t * (q / addOrderOf (g (leaf i) - (h + g r)))) ∧
        ∀ b ∈ B, ∃ z : ℤ, ∃ c : Fin (m + 1) → ℤ,
          z • (g (leaf i) - (h + g r)) ≠ 0 ∧
          Witness g (z • (g (leaf i) - (h + g r))) c ∧
          c b ≠ 0 ∧ ∀ a' ∈ B, a' ≠ b → c a' = 0)

/-- Attach the minimal odd-primary witness transversal and its recursive
tuple to the saturated pure-star branch. -/
theorem pureEdgeStarLeafCycle_oddPrimaryDescentOutcome_of_oddPrimaryOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryOutcome g h r T a d center) :
    PureEdgeStarLeafOddPrimaryDescentOutcome g h r T a d center := by
  rcases hout with hcap | hmixed |
      ⟨halg, i, ell, p, hellTwo, hellD, htorsion, hcert, hordD⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · right
    right
    obtain ⟨B, hmin, hdesc, hprivate⟩ :=
      hcert.exists_minimalTransversal_oddFactorDescent g hg
    exact ⟨halg, i, ell, p, B, hellTwo, hellD, htorsion, hcert, hordD,
      hmin, hdesc, hprivate⟩

/-- Global noncrossing pure-star endpoint with the strict odd-factor
minimal-transversal descent installed losslessly. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryDescentOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (r : Fin (m + 1))
    (qroot : ReducedSubsetSumCollision g h)
    (hqCanonical : qroot ∈ canonicalReducedCollisions (g := g) hh)
    (hcoeff : subsetCollisionCoeffs qroot.val.1 qroot.val.2 =
        supportAvoidingWitnessAt g hno r ∨
      subsetCollisionCoeffs qroot.val.1 qroot.val.2 =
        -supportAvoidingWitnessAt g hno r)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hcross : ∀ q' : ReducedSubsetSumCollision g h,
      ¬ ((qroot, q') ∈ canonicalPositiveNegativeCrossPairs (g := g) hh ∨
        (q', qroot) ∈ canonicalPositiveNegativeCrossPairs (g := g) hh))
    (hL : (witnessPureEdgeStarLeaves g h r).Nonempty) :
    ∃ T : ↥(witnessPureEdgeStarLeaves g h r) →
        ↥(witnessPureEdgeStarLeaves g h r),
      ∃ a : ↥(witnessPureEdgeStarLeaves g h r), ∃ d : ℕ,
        ∃ center : Fin d → Fin (m + 1),
          d ≤ (witnessPureEdgeStarLeaves g h r).card ∧
          IsMinimalFixedPointFreeCycle T a d ∧
          Function.Injective center ∧
          (∀ j : Fin d,
            center j ≠ r ∧
            center j ≠ (T^[j.val] a : Fin (m + 1)) ∧
            center j ≠ (T (T^[j.val] a) : Fin (m + 1)) ∧
            (2 : ℤ) • g (center j) =
              h + g r + g (T (T^[j.val] a) : Fin (m + 1))) ∧
          PureEdgeStarLeafOddPrimaryDescentOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryOutcome
      g hg hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_oddPrimaryDescentOutcome_of_oddPrimaryOutcome
      g hg r T center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
