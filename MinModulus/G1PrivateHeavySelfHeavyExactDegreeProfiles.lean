/-
# Uniform exact-degree layers and coefficient profiles

The arbitrary-degree omission recurrence stops when all `q` guaranteed
omissions have been fixed.  This module describes that terminal layer without
specializing to four, five, or any later degree.

Any private self-heavy owner subfamily whose witnesses have omission degree at
least `q` splits exactly into degree `q` and degree at least `q+1`.  On the
exact layer, a fixed `q`-element omission set is the entire omission set.  The
remaining nonnegative coefficient mass is encoded by the owner coefficient
and a companion profile which is zero at the owner.  This profile is also
zero on the minimal transversal and on every omission, and its mass plus the
owner coefficient is exactly `q`.
-/
import MinModulus.G1PrivateHeavySelfHeavyOmissionDegreeExtension

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Members of `S` whose canonical private witness has exactly `q`
omissions. -/
noncomputable def minimalSupportPrivateSelfHeavyExactDegreeWithin
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (q : ℕ) : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) := by
  classical
  exact S.filter (fun b ↦
    (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card = q)

/-- Members of `S` whose canonical private witness has omission degree at
least `q+1`. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (q : ℕ) : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) := by
  classical
  exact S.filter (fun b ↦
    q + 1 ≤ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card)

@[simp] theorem mem_minimalSupportPrivateSelfHeavyExactDegreeWithin_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (q : ℕ) (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    b ∈ minimalSupportPrivateSelfHeavyExactDegreeWithin g h hmin S q ↔
      b ∈ S ∧
        (witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val)).card = q := by
  classical
  simp [minimalSupportPrivateSelfHeavyExactDegreeWithin]

@[simp] theorem mem_minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (q : ℕ) (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    b ∈ minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin
        g h hmin S q ↔
      b ∈ S ∧
        q + 1 ≤ (witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val)).card := by
  classical
  simp [minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin]

/-- Uniform exact-degree/next-degree partition. -/
theorem minimalSupportPrivateSelfHeavy_exactDegree_union_atLeastSuccDegree
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (q : ℕ)
    (hdegree : ∀ b ∈ S, q ≤ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card) :
    minimalSupportPrivateSelfHeavyExactDegreeWithin g h hmin S q ∪
        minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin
          g h hmin S q = S := by
  classical
  ext b
  constructor
  · intro hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact (mem_minimalSupportPrivateSelfHeavyExactDegreeWithin_iff
        g h hmin S q b).mp hb |>.1
    · exact (mem_minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin_iff
        g h hmin S q b).mp hb |>.1
  · intro hb
    by_cases heq : (witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val)).card = q
    · exact Finset.mem_union_left _
        ((mem_minimalSupportPrivateSelfHeavyExactDegreeWithin_iff
          g h hmin S q b).mpr ⟨hb, heq⟩)
    · exact Finset.mem_union_right _
        ((mem_minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin_iff
          g h hmin S q b).mpr ⟨hb, by
            have := hdegree b hb
            omega⟩)

/-- The two layers in the uniform degree partition are disjoint. -/
theorem minimalSupportPrivateSelfHeavy_exactDegree_disjoint_atLeastSuccDegree
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (q : ℕ) :
    Disjoint
      (minimalSupportPrivateSelfHeavyExactDegreeWithin g h hmin S q)
      (minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin
        g h hmin S q) := by
  classical
  rw [Finset.disjoint_left]
  intro b hbExact hbSucc
  have heq :=
    (mem_minimalSupportPrivateSelfHeavyExactDegreeWithin_iff
      g h hmin S q b).mp hbExact |>.2
  have hsucc :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin_iff
      g h hmin S q b).mp hbSucc |>.2
  omega

/-- Exact cardinality form of the uniform degree partition. -/
theorem card_minimalSupportPrivateSelfHeavy_eq_exactDegree_add_atLeastSuccDegree
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (q : ℕ)
    (hdegree : ∀ b ∈ S, q ≤ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card) :
    S.card =
      (minimalSupportPrivateSelfHeavyExactDegreeWithin
        g h hmin S q).card +
      (minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin
        g h hmin S q).card := by
  let E := minimalSupportPrivateSelfHeavyExactDegreeWithin g h hmin S q
  let H := minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin
    g h hmin S q
  have hunion : E ∪ H = S :=
    minimalSupportPrivateSelfHeavy_exactDegree_union_atLeastSuccDegree
      g h hmin S q hdegree
  calc
    S.card = (E ∪ H).card := congrArg Finset.card hunion.symm
    _ = E.card + H.card := Finset.card_union_of_disjoint
      (minimalSupportPrivateSelfHeavy_exactDegree_disjoint_atLeastSuccDegree
        g h hmin S q)

/-- A lower bound on a degree-`q` family transfers, with factor two, to its
exact layer or its next-degree layer. -/
theorem le_two_mul_exactDegree_or_le_two_mul_atLeastSuccDegree
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (q K : ℕ)
    (hdegree : ∀ b ∈ S, q ≤ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)).card)
    (hK : K ≤ S.card) :
    K ≤ 2 * (minimalSupportPrivateSelfHeavyExactDegreeWithin
      g h hmin S q).card ∨
      K ≤ 2 * (minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin
        g h hmin S q).card := by
  rw [card_minimalSupportPrivateSelfHeavy_eq_exactDegree_add_atLeastSuccDegree
    g h hmin S q hdegree] at hK
  omega

/-- Direct owner family corresponding to one arbitrary-degree extension
fiber.  It removes the subtype introduced by the incidence construction. -/
noncomputable def minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (z : Fin (m + 1)) :
    Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) := by
  classical
  exact S.filter (fun b ↦ z ∉ R ∧
    z ∈ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val))

@[simp] theorem mem_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (z : Fin (m + 1))
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    b ∈ minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners
        g h hmin S R z ↔
      b ∈ S ∧ z ∉ R ∧
        z ∈ witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val) := by
  classical
  simp [minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners]

/-- Removing the extension-fiber subtype loses no cardinality. -/
theorem card_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionFiber_eq_owners
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (z : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionFiber
        g h hmin S R z).card =
      (minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners
        g h hmin S R z).card := by
  classical
  apply Finset.card_bij (fun b _hb ↦ b.val)
  · intro b hb
    have hb' := Finset.mem_filter.mp hb
    exact
      (mem_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners_iff
        g h hmin S R z b.val).mpr
        ⟨b.property, hb'.2.1, hb'.2.2⟩
  · intro b _hb c _hc hbc
    exact Subtype.ext hbc
  · intro b hb
    have hb' :=
      (mem_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners_iff
        g h hmin S R z b).mp hb
    let bS : ↥S := ⟨b, hb'.1⟩
    refine ⟨bS, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ bS, hb'.2.1, hb'.2.2⟩

/-- On the exact-degree layer, a fixed `q`-element omitted set is the entire
omission set. -/
theorem minimalSupportPrivateSelfHeavyExactDegree_omissions_eq_fixed
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (q : ℕ)
    (hRcard : R.card = q)
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val))
    {b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyExactDegreeWithin
      g h hmin S q) :
    witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) = R := by
  have hb' :=
    (mem_minimalSupportPrivateSelfHeavyExactDegreeWithin_iff
      g h hmin S q b).mp hb
  have hsubset := hfixed b hb'.1
  apply Finset.Subset.antisymm
  · exact Finset.eq_of_subset_of_card_le hsubset (by
      rw [hRcard, hb'.2]) |>.symm.le
  · exact hsubset

/-- The companion coefficient profile of an owner.  It retains the witness
coefficients away from both the omission set and the varying owner, and is
zero everywhere else. -/
noncomputable def minimalSupportPrivateSelfHeavyCompanionProfile
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    Fin (m + 1) → ℤ := fun i ↦
  if i ∈ (witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val))ᶜ.erase b.val then
    minimalSupportPrivateWitness g h hmin b.val i
  else 0

/-- The complete exact-degree profile key: owner coefficient followed by the
owner-erased companion coefficient vector. -/
noncomputable def minimalSupportPrivateSelfHeavyExactDegreeProfileKey
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    ℤ × (Fin (m + 1) → ℤ) :=
  (minimalSupportPrivateWitness g h hmin b.val b.val,
    minimalSupportPrivateSelfHeavyCompanionProfile g h hmin b)

/-- Companion coefficients are nonnegative. -/
theorem minimalSupportPrivateSelfHeavyCompanionProfile_nonneg
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (i : Fin (m + 1)) :
    0 ≤ minimalSupportPrivateSelfHeavyCompanionProfile g h hmin b i := by
  classical
  unfold minimalSupportPrivateSelfHeavyCompanionProfile
  split_ifs with hi
  · have hiO : i ∉ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) := by
      have hiCompl : i ∈ (witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val))ᶜ :=
        Finset.mem_of_mem_erase hi
      simpa using hiCompl
    exact nonneg_of_not_mem_exactOmissions
      (minimalSupportPrivateWitness_isWitness g h hmin b.val).2.1
      (witnessOmissionCoordinates_exact
        (minimalSupportPrivateWitness g h hmin b.val)) hiO
  · exact le_rfl

/-- The varying owner coordinate is erased from its companion profile. -/
@[simp] theorem minimalSupportPrivateSelfHeavyCompanionProfile_owner
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    minimalSupportPrivateSelfHeavyCompanionProfile g h hmin b b.val = 0 := by
  classical
  simp [minimalSupportPrivateSelfHeavyCompanionProfile]

/-- Omitted coordinates vanish in the companion profile. -/
theorem minimalSupportPrivateSelfHeavyCompanionProfile_eq_zero_of_omitted
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    {i : Fin (m + 1)}
    (hi : i ∈ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)) :
    minimalSupportPrivateSelfHeavyCompanionProfile g h hmin b i = 0 := by
  classical
  simp [minimalSupportPrivateSelfHeavyCompanionProfile, hi]

/-- Privacy forces the companion profile to vanish throughout the minimal
transversal, including at the owner because that coordinate is erased. -/
theorem minimalSupportPrivateSelfHeavyCompanionProfile_eq_zero_of_mem_transversal
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    {i : Fin (m + 1)} (hiB : i ∈ B) :
    minimalSupportPrivateSelfHeavyCompanionProfile g h hmin b i = 0 := by
  classical
  by_cases hie : i = b.val
  · subst i
    exact minimalSupportPrivateSelfHeavyCompanionProfile_owner g h hmin b
  · have hzero := minimalSupportPrivateWitness_eq_zero_of_ne
      g h hmin b.val hiB hie
    unfold minimalSupportPrivateSelfHeavyCompanionProfile
    split_ifs
    · exact hzero
    · rfl

/-- Away from the omissions and owner, the profile records the original
witness coefficient exactly. -/
theorem minimalSupportPrivateSelfHeavyCompanionProfile_eq_coeff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    {i : Fin (m + 1)}
    (hiO : i ∉ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val))
    (hie : i ≠ b.val) :
    minimalSupportPrivateSelfHeavyCompanionProfile g h hmin b i =
      minimalSupportPrivateWitness g h hmin b.val i := by
  classical
  simp [minimalSupportPrivateSelfHeavyCompanionProfile, hiO, hie]

/-- The owner level of an exact-degree self-heavy profile lies in `[2,q]`. -/
theorem minimalSupportPrivateSelfHeavyExactDegreeProfileKey_owner_bounds
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (q : ℕ)
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    {b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyExactDegreeWithin
      g h hmin S q) :
    (2 : ℤ) ≤
        (minimalSupportPrivateSelfHeavyExactDegreeProfileKey
          g h hmin b).1 ∧
      (minimalSupportPrivateSelfHeavyExactDegreeProfileKey
          g h hmin b).1 ≤ (q : ℤ) := by
  have hb' :=
    (mem_minimalSupportPrivateSelfHeavyExactDegreeWithin_iff
      g h hmin S q b).mp hb
  have hbSelf := hself b hb'.1
  have hheavy := minimalSupportPrivateSelfHeavy_ownerHeavy
    g h hmin hbSelf
  have hnotomit : minimalSupportPrivateWitness g h hmin b.val b.val ≠ -1 := by
    omega
  have hupper := witness_coeff_le_card_witnessOmissionCoordinates
    g (minimalSupportPrivateWitness_isWitness g h hmin b.val) hnotomit
  rw [hb'.2] at hupper
  exact ⟨by simpa [minimalSupportPrivateSelfHeavyExactDegreeProfileKey] using
      hheavy,
    by simpa [minimalSupportPrivateSelfHeavyExactDegreeProfileKey] using
      hupper⟩

/-- The owner coefficient and companion profile retain all `q` units of
nonnegative mass in an exact-degree witness. -/
theorem minimalSupportPrivateSelfHeavyExactDegreeProfileKey_mass
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (q : ℕ)
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    {b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyExactDegreeWithin
      g h hmin S q) :
    (minimalSupportPrivateSelfHeavyExactDegreeProfileKey
        g h hmin b).1 +
        ∑ i, (minimalSupportPrivateSelfHeavyExactDegreeProfileKey
          g h hmin b).2 i = (q : ℤ) := by
  classical
  let c := minimalSupportPrivateWitness g h hmin b.val
  let O := witnessOmissionCoordinates c
  let e : Fin (m + 1) := b.val
  have hb' :=
    (mem_minimalSupportPrivateSelfHeavyExactDegreeWithin_iff
      g h hmin S q b).mp hb
  have hbSelf := hself b hb'.1
  have hheavy : 2 ≤ c e := by
    exact minimalSupportPrivateSelfHeavy_ownerHeavy g h hmin hbSelf
  have heO : e ∈ Oᶜ := by
    simp only [Finset.mem_compl]
    intro he
    have hneg : c e = -1 := by
      exact (witnessOmissionCoordinates_exact c e).2 he
    omega
  have hmass := witness_compl_sum_eq_card_exactOmissions
    g (minimalSupportPrivateWitness_isWitness g h hmin b.val) O
      (witnessOmissionCoordinates_exact c)
  have hsplit := Finset.sum_erase_add Oᶜ c heO
  have hprofile :
      (∑ i, minimalSupportPrivateSelfHeavyCompanionProfile
        g h hmin b i) = ∑ i ∈ Oᶜ.erase e, c i := by
    change (∑ i, if i ∈ Oᶜ.erase e then c i else 0) =
      ∑ i ∈ Oᶜ.erase e, c i
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hOcard : O.card = q := by
    simpa [O, c] using hb'.2
  have hmass' : (∑ i ∈ Oᶜ, c i) = (q : ℤ) := by
    simpa [c, hOcard] using hmass
  change c e + ∑ i,
    minimalSupportPrivateSelfHeavyCompanionProfile g h hmin b i = (q : ℤ)
  calc
    c e + ∑ i, minimalSupportPrivateSelfHeavyCompanionProfile
        g h hmin b i = c e + ∑ i ∈ Oᶜ.erase e, c i := by rw [hprofile]
    _ = ∑ i ∈ Oᶜ, c i := by omega
    _ = (q : ℤ) := hmass'

/-- With `q` fixed omissions, the profile key reconstructs every witness
coefficient: `-1` on the fixed set, the recorded level at the owner, and the
companion profile everywhere else. -/
theorem minimalSupportPrivateSelfHeavyExactDegreeProfileKey_reconstruct
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (q : ℕ)
    (hRcard : R.card = q)
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val))
    {b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyExactDegreeWithin
      g h hmin S q) :
    let c := minimalSupportPrivateWitness g h hmin b.val
    let p := minimalSupportPrivateSelfHeavyExactDegreeProfileKey g h hmin b
    ∀ i, c i =
      if i ∈ R then -1 else if i = b.val then p.1 else p.2 i := by
  classical
  dsimp only
  let c := minimalSupportPrivateWitness g h hmin b.val
  let O := witnessOmissionCoordinates c
  let p := minimalSupportPrivateSelfHeavyExactDegreeProfileKey g h hmin b
  have hOeq : O = R := by
    exact minimalSupportPrivateSelfHeavyExactDegree_omissions_eq_fixed
      g h hmin S R q hRcard hfixed hb
  have hexact : ExactOmissions c R := by
    rw [← hOeq]
    exact witnessOmissionCoordinates_exact c
  intro i
  by_cases hiR : i ∈ R
  · have hci : c i = -1 := (hexact i).2 hiR
    rw [if_pos hiR]
    simpa [c] using hci
  · by_cases hie : i = b.val
    · subst i
      simp [hiR, minimalSupportPrivateSelfHeavyExactDegreeProfileKey]
    · have hiO' : i ∉ O := by
        rwa [hOeq]
      have hiO : i ∉ witnessOmissionCoordinates c := by
        simpa [O] using hiO'
      have hp := minimalSupportPrivateSelfHeavyCompanionProfile_eq_coeff
        g h hmin b hiO hie
      simp [hiR, hie, minimalSupportPrivateSelfHeavyExactDegreeProfileKey, hp]

/-- A complete exact-degree profile gives one affine equation.  Once its
profile key is fixed, only the owner coordinate varies. -/
theorem minimalSupportPrivateSelfHeavyExactDegreeProfileKey_affine
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (q : ℕ)
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (hRcard : R.card = q)
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val))
    {b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyExactDegreeWithin
      g h hmin S q) :
    let p := minimalSupportPrivateSelfHeavyExactDegreeProfileKey g h hmin b
    p.1 • g b.val + ∑ i, p.2 i • g i = h + ∑ i ∈ R, g i := by
  classical
  dsimp only
  let c := minimalSupportPrivateWitness g h hmin b.val
  let O := witnessOmissionCoordinates c
  let e : Fin (m + 1) := b.val
  let p := minimalSupportPrivateSelfHeavyExactDegreeProfileKey g h hmin b
  have hb' :=
    (mem_minimalSupportPrivateSelfHeavyExactDegreeWithin_iff
      g h hmin S q b).mp hb
  have hbSelf := hself b hb'.1
  have hheavy : 2 ≤ c e := by
    exact minimalSupportPrivateSelfHeavy_ownerHeavy g h hmin hbSelf
  have hOeq : O = R := by
    exact minimalSupportPrivateSelfHeavyExactDegree_omissions_eq_fixed
      g h hmin S R q hRcard hfixed hb
  have hexact : ExactOmissions c R := by
    rw [← hOeq]
    exact witnessOmissionCoordinates_exact c
  have heR : e ∉ R := by
    intro he
    have hneg : c e = -1 := (hexact e).2 he
    omega
  have hpoint : ∀ i,
      c i • g i + (if i ∈ R then g i else 0) =
        (if i = e then p.1 • g i else 0) + p.2 i • g i := by
    intro i
    by_cases hiR : i ∈ R
    · have hci : c i = -1 := (hexact i).2 hiR
      have hie : i ≠ e := by
        intro hie
        subst i
        exact heR hiR
      have hiO : i ∈ witnessOmissionCoordinates
          (minimalSupportPrivateWitness g h hmin b.val) := by
        simpa [c, O, hOeq] using hiR
      have hpzero :=
        minimalSupportPrivateSelfHeavyCompanionProfile_eq_zero_of_omitted
          g h hmin b hiO
      simp [hiR, hie, hci, p,
        minimalSupportPrivateSelfHeavyExactDegreeProfileKey, hpzero]
    · by_cases hie : i = e
      · subst i
        simp [heR, p, e,
          minimalSupportPrivateSelfHeavyExactDegreeProfileKey, c]
      · have hiO' : i ∉ O := by
          rwa [hOeq]
        have hiO : i ∉ witnessOmissionCoordinates c := by
          simpa [O] using hiO'
        have hp := minimalSupportPrivateSelfHeavyCompanionProfile_eq_coeff
          g h hmin b (by simpa [c] using hiO) (by simpa [e] using hie)
        simp [hiR, hie, p,
          minimalSupportPrivateSelfHeavyExactDegreeProfileKey, c, hp]
  have hsum :
      (∑ i, c i • g i) + (∑ i ∈ R, g i) =
        p.1 • g e + ∑ i, p.2 i • g i := by
    calc
      (∑ i, c i • g i) + (∑ i ∈ R, g i) =
          ∑ i, (c i • g i + if i ∈ R then g i else 0) := by
            rw [Finset.sum_add_distrib, Finset.sum_ite_mem,
              Finset.univ_inter]
      _ = ∑ i, ((if i = e then p.1 • g i else 0) + p.2 i • g i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact hpoint i
      _ = p.1 • g e + ∑ i, p.2 i • g i := by
        rw [Finset.sum_add_distrib,
          Finset.sum_ite_eq' Finset.univ e (fun i ↦ p.1 • g i)]
        simp
  have hcval : (∑ i, c i • g i) = h := by
    exact (minimalSupportPrivateWitness_isWitness g h hmin b.val).2.2.2
  rw [hcval] at hsum
  exact hsum.symm

/-- Realized profile keys in an exact-degree subfamily. -/
noncomputable def minimalSupportPrivateSelfHeavyExactDegreeProfiles
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (q : ℕ) : Finset (ℤ × (Fin (m + 1) → ℤ)) := by
  classical
  exact (minimalSupportPrivateSelfHeavyExactDegreeWithin
    g h hmin S q).image
      (minimalSupportPrivateSelfHeavyExactDegreeProfileKey g h hmin)

@[simp] theorem mem_minimalSupportPrivateSelfHeavyExactDegreeProfiles_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (q : ℕ) (p : ℤ × (Fin (m + 1) → ℤ)) :
    p ∈ minimalSupportPrivateSelfHeavyExactDegreeProfiles g h hmin S q ↔
      ∃ b ∈ minimalSupportPrivateSelfHeavyExactDegreeWithin g h hmin S q,
        minimalSupportPrivateSelfHeavyExactDegreeProfileKey g h hmin b = p := by
  classical
  simp [minimalSupportPrivateSelfHeavyExactDegreeProfiles]

/-- Every realized exact-degree profile has owner level in `[2,q]`, a
nonnegative companion vector supported off both `B` and the fixed omissions,
and total companion mass `q-ownerLevel`. -/
theorem minimalSupportPrivateSelfHeavyExactDegreeProfile_spec
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (q : ℕ)
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (hRcard : R.card = q)
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val))
    {p : ℤ × (Fin (m + 1) → ℤ)}
    (hp : p ∈ minimalSupportPrivateSelfHeavyExactDegreeProfiles
      g h hmin S q) :
    (2 : ℤ) ≤ p.1 ∧ p.1 ≤ (q : ℤ) ∧
      (∀ i, 0 ≤ p.2 i) ∧
      (∀ i ∈ B, p.2 i = 0) ∧
      (∀ i ∈ R, p.2 i = 0) ∧
      p.1 + ∑ i, p.2 i = (q : ℤ) ∧
      (∑ i, p.2 i) ≤ (q : ℤ) - 2 := by
  obtain ⟨b, hb, rfl⟩ :=
    (mem_minimalSupportPrivateSelfHeavyExactDegreeProfiles_iff
      g h hmin S q p).mp hp
  have hbounds :=
    minimalSupportPrivateSelfHeavyExactDegreeProfileKey_owner_bounds
      g h hmin S q hself hb
  have hmass := minimalSupportPrivateSelfHeavyExactDegreeProfileKey_mass
    g h hmin S q hself hb
  have hnonneg : ∀ i,
      0 ≤ (minimalSupportPrivateSelfHeavyExactDegreeProfileKey
        g h hmin b).2 i := by
    intro i
    exact minimalSupportPrivateSelfHeavyCompanionProfile_nonneg
      g h hmin b i
  have hzeroB : ∀ i ∈ B,
      (minimalSupportPrivateSelfHeavyExactDegreeProfileKey
        g h hmin b).2 i = 0 := by
    intro i hiB
    exact minimalSupportPrivateSelfHeavyCompanionProfile_eq_zero_of_mem_transversal
      g h hmin b hiB
  have hOeq :=
    minimalSupportPrivateSelfHeavyExactDegree_omissions_eq_fixed
      g h hmin S R q hRcard hfixed hb
  have hzeroR : ∀ i ∈ R,
      (minimalSupportPrivateSelfHeavyExactDegreeProfileKey
        g h hmin b).2 i = 0 := by
    intro i hiR
    apply minimalSupportPrivateSelfHeavyCompanionProfile_eq_zero_of_omitted
      g h hmin b
    rw [hOeq]
    exact hiR
  exact ⟨hbounds.1, hbounds.2, hnonneg, hzeroB, hzeroR, hmass, by
    omega⟩

/-- Owners in an exact-degree subfamily realizing one fixed profile key. -/
noncomputable def minimalSupportPrivateSelfHeavyExactDegreeProfileFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (q : ℕ) (p : ℤ × (Fin (m + 1) → ℤ)) :
    Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) := by
  classical
  exact (minimalSupportPrivateSelfHeavyExactDegreeWithin
    g h hmin S q).filter (fun b ↦
      minimalSupportPrivateSelfHeavyExactDegreeProfileKey g h hmin b = p)

@[simp] theorem mem_minimalSupportPrivateSelfHeavyExactDegreeProfileFiber_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (q : ℕ) (p : ℤ × (Fin (m + 1) → ℤ))
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    b ∈ minimalSupportPrivateSelfHeavyExactDegreeProfileFiber
        g h hmin S q p ↔
      b ∈ minimalSupportPrivateSelfHeavyExactDegreeWithin g h hmin S q ∧
        minimalSupportPrivateSelfHeavyExactDegreeProfileKey g h hmin b = p := by
  classical
  simp [minimalSupportPrivateSelfHeavyExactDegreeProfileFiber]

/-- Grouping an exact-degree layer by its complete profile key is an exact
cardinality partition. -/
theorem card_minimalSupportPrivateSelfHeavyExactDegreeWithin_eq_sum_profileFibers
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (q : ℕ) :
    (minimalSupportPrivateSelfHeavyExactDegreeWithin
        g h hmin S q).card =
      ∑ p ∈ minimalSupportPrivateSelfHeavyExactDegreeProfiles
          g h hmin S q,
        (minimalSupportPrivateSelfHeavyExactDegreeProfileFiber
          g h hmin S q p).card := by
  classical
  let E := minimalSupportPrivateSelfHeavyExactDegreeWithin g h hmin S q
  let key := minimalSupportPrivateSelfHeavyExactDegreeProfileKey g h hmin
  calc
    E.card = ∑ p ∈ E.image key,
        (E.filter (fun b ↦ key b = p)).card :=
      Finset.card_eq_sum_card_image key E
    _ = ∑ p ∈ minimalSupportPrivateSelfHeavyExactDegreeProfiles
            g h hmin S q,
          (minimalSupportPrivateSelfHeavyExactDegreeProfileFiber
            g h hmin S q p).card := by rfl

/-- Every member of a fixed profile fiber satisfies the same affine equation;
the owner is its only varying coordinate. -/
theorem minimalSupportPrivateSelfHeavyExactDegreeProfileFiber_affine
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (q : ℕ)
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (hRcard : R.card = q)
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val))
    (p : ℤ × (Fin (m + 1) → ℤ))
    {b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyExactDegreeProfileFiber
      g h hmin S q p) :
    p.1 • g b.val + ∑ i, p.2 i • g i = h + ∑ i ∈ R, g i := by
  have hb' :=
    (mem_minimalSupportPrivateSelfHeavyExactDegreeProfileFiber_iff
      g h hmin S q p b).mp hb
  have haffine :=
    minimalSupportPrivateSelfHeavyExactDegreeProfileKey_affine
      g h hmin S R q hself hRcard hfixed hb'.1
  rw [hb'.2] at haffine
  exact haffine

/-- The four-fixed owner family in the original ambient owner type. -/
noncomputable def minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1)) :
    Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin) :=
  minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners
    g h hmin
      (minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners
        g h hmin z w u)
      ({z, w, u} : Finset (Fin (m + 1))) v

@[simp] theorem mem_minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1))
    (b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)) :
    b ∈ minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
        g h hmin z w u v ↔
      b ∈ minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners
          g h hmin z w u ∧
      v ∉ ({z, w, u} : Finset (Fin (m + 1))) ∧
      v ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) := by
  classical
  exact mem_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionOwners_iff
    g h hmin
      (minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners
        g h hmin z w u)
      ({z, w, u} : Finset (Fin (m + 1))) v b

/-- The nested four-fixed fiber from the recurrence and its direct owner
family have exactly the same cardinality. -/
theorem card_minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionFiber_eq_owners
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionFiber
        g h hmin z w u v).card =
      (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
        g h hmin z w u v).card := by
  exact card_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionFiber_eq_owners
    g h hmin
      (minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners
        g h hmin z w u)
      ({z, w, u} : Finset (Fin (m + 1))) v

/-- Structural facts retained by the direct four-fixed owner family. -/
theorem minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_spec
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1))
    {b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈
      minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
        g h hmin z w u v) :
    b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin ∧
      4 ≤ (witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val)).card ∧
      v ≠ z ∧ v ≠ w ∧ v ≠ u ∧
      z ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) ∧
      w ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) ∧
      u ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) ∧
      v ∈ witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val) := by
  have hb' :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_iff
      g h hmin z w u v b).mp hb
  have hbTriple :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastFourTripleOmissionOwners_iff
      g h hmin z w u b).mp hb'.1
  have hbFour :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastFourVertices_iff
      g h hmin b).mp hbTriple.1
  have hbSelf :=
    (mem_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_iff
      g h hmin b).mp hbFour.1 |>.1
  have hvNe : v ≠ z ∧ v ≠ w ∧ v ≠ u := by
    simpa using hb'.2.1
  exact ⟨hbSelf, hbFour.2, hvNe.1, hvNe.2.1, hvNe.2.2,
    hbTriple.2.2.2.2.1, hbTriple.2.2.2.2.2.1,
    hbTriple.2.2.2.2.2.2, hb'.2.2⟩

/-- Exact-four members of a four-fixed at-least-four family. -/
noncomputable def minimalSupportPrivateSelfHeavyQuadrupleExactFourOwners
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1)) :=
  minimalSupportPrivateSelfHeavyExactDegreeWithin g h hmin
    (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
      g h hmin z w u v) 4

/-- At-least-five members of a four-fixed at-least-four family. -/
noncomputable def minimalSupportPrivateSelfHeavyQuadrupleAtLeastFiveOwners
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1)) :=
  minimalSupportPrivateSelfHeavyAtLeastSuccDegreeWithin g h hmin
    (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
      g h hmin z w u v) 4

/-- The first concrete instance of the uniform split: a four-fixed family is
exactly the disjoint union of its exact-four and at-least-five layers. -/
theorem minimalSupportPrivateSelfHeavy_quadrupleExactFour_union_atLeastFive
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1)) :
    minimalSupportPrivateSelfHeavyQuadrupleExactFourOwners
        g h hmin z w u v ∪
      minimalSupportPrivateSelfHeavyQuadrupleAtLeastFiveOwners
        g h hmin z w u v =
      minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
        g h hmin z w u v := by
  let Q := minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
    g h hmin z w u v
  apply minimalSupportPrivateSelfHeavy_exactDegree_union_atLeastSuccDegree
    g h hmin Q 4
  intro b hb
  exact (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_spec
    g h hmin z w u v hb).2.1

/-- Exact cardinality form of the concrete exact-four/at-least-five split. -/
theorem card_minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_eq_exactFour_add_atLeastFive
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1)) :
    (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
        g h hmin z w u v).card =
      (minimalSupportPrivateSelfHeavyQuadrupleExactFourOwners
        g h hmin z w u v).card +
      (minimalSupportPrivateSelfHeavyQuadrupleAtLeastFiveOwners
        g h hmin z w u v).card := by
  let Q := minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
    g h hmin z w u v
  apply card_minimalSupportPrivateSelfHeavy_eq_exactDegree_add_atLeastSuccDegree
    g h hmin Q 4
  intro b hb
  exact (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_spec
    g h hmin z w u v hb).2.1

/-- A lower bound for the nested four-fixed recurrence fiber transfers to an
exact-four layer or to a genuinely higher-degree layer. -/
theorem le_two_mul_quadrupleExactFour_or_le_two_mul_quadrupleAtLeastFive
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1)) (K : ℕ)
    (hK : K ≤
      (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionFiber
        g h hmin z w u v).card) :
    K ≤ 2 * (minimalSupportPrivateSelfHeavyQuadrupleExactFourOwners
      g h hmin z w u v).card ∨
      K ≤ 2 * (minimalSupportPrivateSelfHeavyQuadrupleAtLeastFiveOwners
        g h hmin z w u v).card := by
  let Q := minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
    g h hmin z w u v
  have hK' : K ≤ Q.card := by
    rw [← card_minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionFiber_eq_owners
      g h hmin z w u v]
    exact hK
  apply le_two_mul_exactDegree_or_le_two_mul_atLeastSuccDegree
    g h hmin Q 4 K _ hK'
  intro b hb
  exact (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_spec
    g h hmin z w u v hb).2.1

/-- Four pairwise-distinct external omissions form a four-element set
disjoint from the minimal transversal. -/
theorem quadrupleOmissionSet_disjoint_and_card
    {B : Finset (Fin (m + 1))} {z w u v : Fin (m + 1)}
    (hzB : z ∉ B) (hwB : w ∉ B) (huB : u ∉ B) (hvB : v ∉ B)
    (hwz : w ≠ z) (huz : u ≠ z) (huw : u ≠ w)
    (hvz : v ≠ z) (hvw : v ≠ w) (hvu : v ≠ u) :
    Disjoint ({z, w, u, v} : Finset (Fin (m + 1))) B ∧
      ({z, w, u, v} : Finset (Fin (m + 1))).card = 4 := by
  constructor
  · rw [Finset.disjoint_left]
    intro i hi hiB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hzB hiB
    · exact hwB hiB
    · exact huB hiB
    · exact hvB hiB
  · have hzw : z ≠ w := Ne.symm hwz
    have hzu : z ≠ u := Ne.symm huz
    have hzv : z ≠ v := Ne.symm hvz
    have hwu : w ≠ u := Ne.symm huw
    have hwv : w ≠ v := Ne.symm hvw
    have huv : u ≠ v := Ne.symm hvu
    simp [hzw, hzu, hzv, hwu, hwv, huv]

/-- Realized complete coefficient profiles in the four-fixed exact-four
layer. -/
noncomputable def minimalSupportPrivateSelfHeavyQuadrupleExactFourProfiles
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1)) :=
  minimalSupportPrivateSelfHeavyExactDegreeProfiles g h hmin
    (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
      g h hmin z w u v) 4

/-- Fixed complete-profile fibers in the four-fixed exact-four layer. -/
noncomputable def minimalSupportPrivateSelfHeavyQuadrupleExactFourProfileFiber
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1))
    (p : ℤ × (Fin (m + 1) → ℤ)) :=
  minimalSupportPrivateSelfHeavyExactDegreeProfileFiber g h hmin
    (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
      g h hmin z w u v) 4 p

/-- The exact-four profile encoder has the promised uniform invariants. -/
theorem minimalSupportPrivateSelfHeavyQuadrupleExactFourProfile_spec
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1))
    (hzB : z ∉ B) (hwB : w ∉ B) (huB : u ∉ B) (hvB : v ∉ B)
    (hwz : w ≠ z) (huz : u ≠ z) (huw : u ≠ w)
    (hvz : v ≠ z) (hvw : v ≠ w) (hvu : v ≠ u)
    {p : ℤ × (Fin (m + 1) → ℤ)}
    (hp : p ∈ minimalSupportPrivateSelfHeavyQuadrupleExactFourProfiles
      g h hmin z w u v) :
    (2 : ℤ) ≤ p.1 ∧ p.1 ≤ 4 ∧
      (∀ i, 0 ≤ p.2 i) ∧
      (∀ i ∈ B, p.2 i = 0) ∧
      (∀ i ∈ ({z, w, u, v} : Finset (Fin (m + 1))), p.2 i = 0) ∧
      p.1 + ∑ i, p.2 i = 4 ∧
      (∑ i, p.2 i) ≤ 2 := by
  let Q := minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
    g h hmin z w u v
  let R : Finset (Fin (m + 1)) := {z, w, u, v}
  have hset := quadrupleOmissionSet_disjoint_and_card
    hzB hwB huB hvB hwz huz huw hvz hvw hvu
  have hself : ∀ b ∈ Q,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin := by
    intro b hb
    exact (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_spec
      g h hmin z w u v hb).1
  have hfixed : ∀ b ∈ Q, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val) := by
    intro b hb i hi
    have hspec :=
      minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_spec
        g h hmin z w u v hb
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hspec.2.2.2.2.2.1
    · exact hspec.2.2.2.2.2.2.1
    · exact hspec.2.2.2.2.2.2.2.1
    · exact hspec.2.2.2.2.2.2.2.2
  exact minimalSupportPrivateSelfHeavyExactDegreeProfile_spec
    g h hmin Q R 4 hself hset.2 hfixed hp

/-- A fixed exact-four profile gives the expected owner-only affine fiber. -/
theorem minimalSupportPrivateSelfHeavyQuadrupleExactFourProfileFiber_affine
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1))
    (hzB : z ∉ B) (hwB : w ∉ B) (huB : u ∉ B) (hvB : v ∉ B)
    (hwz : w ≠ z) (huz : u ≠ z) (huw : u ≠ w)
    (hvz : v ≠ z) (hvw : v ≠ w) (hvu : v ≠ u)
    (p : ℤ × (Fin (m + 1) → ℤ))
    {b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateSelfHeavyQuadrupleExactFourProfileFiber
      g h hmin z w u v p) :
    p.1 • g b.val + ∑ i, p.2 i • g i =
      h + ∑ i ∈ ({z, w, u, v} : Finset (Fin (m + 1))), g i := by
  let Q := minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners
    g h hmin z w u v
  let R : Finset (Fin (m + 1)) := {z, w, u, v}
  have hset := quadrupleOmissionSet_disjoint_and_card
    hzB hwB huB hvB hwz huz huw hvz hvw hvu
  have hself : ∀ b ∈ Q,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin := by
    intro b hbQ
    exact (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_spec
      g h hmin z w u v hbQ).1
  have hfixed : ∀ b ∈ Q, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val) := by
    intro b hbQ i hi
    have hspec :=
      minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_spec
        g h hmin z w u v hbQ
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hspec.2.2.2.2.2.1
    · exact hspec.2.2.2.2.2.2.1
    · exact hspec.2.2.2.2.2.2.2.1
    · exact hspec.2.2.2.2.2.2.2.2
  exact minimalSupportPrivateSelfHeavyExactDegreeProfileFiber_affine
    g h hmin Q R 4 hself hset.2 hfixed p hb

/-- Feed the uniform exact-degree split into the four-stage global omission
endpoint.  Its last branch is now an exact-four profile layer or a genuinely
at-least-five layer, rather than an unclassified four-fixed family. -/
theorem minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_boundedExactThree_or_quadrupleExactFour_or_atLeastFive
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (K L r L' r' L'' r'' L''' r''' : ℕ)
    (hself : K ≤
      (minimalSupportPrivateSelfHeavyVertices g h hmin).card)
    (hfirst : 2 * (L * r) < 3 * K)
    (hsecond : L' * r' < 2 * (r + 1))
    (hthird : L'' * r'' < r' + 1)
    (hfourth : 2 * (L''' * r''') < r'' + 1) :
    K ≤ 2 *
        (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ∨
      B.card + L ≤ m + 1 ∨
      B.card + 1 + L' ≤ m + 1 ∨
      B.card + 2 + L'' ≤ m + 1 ∨
      r'' + 1 ≤ 2 * (3 + 2 * (m + 1 - B.card)) ∨
      B.card + 3 + L''' ≤ m + 1 ∨
      ∃ z w u v : Fin (m + 1),
        z ∉ B ∧ w ∉ B ∧ u ∉ B ∧ v ∉ B ∧
        w ≠ z ∧ u ≠ z ∧ u ≠ w ∧
        v ≠ z ∧ v ≠ w ∧ v ≠ u ∧
        ((r''' + 1 ≤ 2 *
            (minimalSupportPrivateSelfHeavyQuadrupleExactFourOwners
              g h hmin z w u v).card) ∨
          r''' + 1 ≤ 2 *
            (minimalSupportPrivateSelfHeavyQuadrupleAtLeastFiveOwners
              g h hmin z w u v).card) := by
  rcases
      minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_boundedExactThree_or_quadrupleFiber
        g hg hmin K L r L' r' L'' r'' L''' r'''
          hself hfirst hsecond hthird hfourth with
    htwo | hcap | hcap' | hcap'' | hexact | hcap''' |
      ⟨z, w, u, v, hzB, hwB, huB, hvB, hwz, huz, huw,
        hvz, hvw, hvu, hquad⟩
  · exact Or.inl htwo
  · exact Or.inr (Or.inl hcap)
  · exact Or.inr (Or.inr (Or.inl hcap'))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hcap'')))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hexact))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcap''')))))
  · have hK : r''' + 1 ≤
        (minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionFiber
          g h hmin z w u v).card := by
      omega
    have hsplit :=
      le_two_mul_quadrupleExactFour_or_le_two_mul_quadrupleAtLeastFive
        g h hmin z w u v (r''' + 1) hK
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨z, w, u, v, hzB, hwB, huB, hvB, hwz, huz, huw,
        hvz, hvw, hvu, hsplit⟩)))))

end MinModulus
