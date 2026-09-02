/-
# Cyclic bounds and weak-composition counting for exact-degree profiles

The complete profile key from the preceding module turns every fixed-key
owner family into one fiber of scalar multiplication.  In `ZMod N`, validity
makes owner values injective, so a key with owner level `d` contains at most
`gcd(N,d) ≤ d ≤ q` owners.

The remaining task is to count the possible nonnegative companion vectors.
They are supported on coordinates outside the transversal and the fixed
omissions and have mass at most `q-2`; padding by one dummy coordinate embeds
them in the weak compositions of exactly `q-2`.
-/
import MinModulus.G1PrivateHeavySelfHeavyExactDegreeProfiles
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Coordinates available to a companion profile after removing the minimal
transversal and the fixed omissions. -/
def minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates
    (B R : Finset (Fin (m + 1))) : Finset (Fin (m + 1)) :=
  (B ∪ R)ᶜ

/-- Exact number of free coordinates when the fixed omissions are external
to the transversal. -/
theorem card_minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates
    (B R : Finset (Fin (m + 1))) (hRB : Disjoint R B) :
    (minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R).card =
      m + 1 - (B.card + R.card) := by
  classical
  rw [minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates,
    Finset.card_compl, Fintype.card_fin,
    Finset.card_union_of_disjoint hRB.symm]

/-- Converting a nonnegative integer vector supported on `C` to naturals and
summing over the subtype `C` preserves its total mass. -/
theorem sum_toNat_freeCoordinates_eq_toNat_sum
    {C : Finset (Fin (m + 1))} (p : Fin (m + 1) → ℤ)
    (hnonneg : ∀ i, 0 ≤ p i)
    (hzero : ∀ i, i ∉ C → p i = 0) :
    (∑ i : ↥C, (p i.val).toNat) = (∑ i, p i).toNat := by
  have hsumNonneg : 0 ≤ ∑ i, p i := Finset.sum_nonneg fun i _hi ↦ hnonneg i
  apply Int.ofNat_injective
  calc
    ((∑ i : ↥C, (p i.val).toNat : ℕ) : ℤ) =
        ∑ i : ↥C, p i.val := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      exact Int.toNat_of_nonneg (hnonneg i.val)
    _ = ∑ i ∈ C, p i := by
      simpa using Finset.sum_attach C p
    _ = ∑ i, p i := by
      apply Finset.sum_subset (Finset.subset_univ C)
      intro i _hi hiC
      exact hzero i hiC
    _ = (((∑ i, p i).toNat : ℕ) : ℤ) := by
      exact (Int.toNat_of_nonneg hsumNonneg).symm

/-- Natural companion mass on the free-coordinate subtype. -/
def exactDegreeProfileFreeMass
    (C : Finset (Fin (m + 1)))
    (p : ℤ × (Fin (m + 1) → ℤ)) : ℕ :=
  ∑ i : ↥C, (p.2 i.val).toNat

/-- Pad a companion vector of mass at most `k` by one dummy coordinate. -/
noncomputable def exactDegreeProfilePaddedComposition
    (C : Finset (Fin (m + 1))) (k : ℕ)
    (p : ℤ × (Fin (m + 1) → ℤ)) :
    (↥C ⊕ Unit) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun x ↦
    match x with
    | Sum.inl i => (p.2 i.val).toNat
    | Sum.inr _ => k - exactDegreeProfileFreeMass C p

/-- The padded vector has total mass exactly `k`. -/
theorem sum_exactDegreeProfilePaddedComposition
    (C : Finset (Fin (m + 1))) (k : ℕ)
    (p : ℤ × (Fin (m + 1) → ℤ))
    (hmass : exactDegreeProfileFreeMass C p ≤ k) :
    ∑ x, exactDegreeProfilePaddedComposition C k p x = k := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [exactDegreeProfilePaddedComposition]
  change exactDegreeProfileFreeMass C p + (k -
    exactDegreeProfileFreeMass C p) = k
  exact Nat.add_sub_of_le hmass

/-- Tuple values at the owner coordinate are injective on the ambient private
tail-heavy owner type. -/
theorem minimalSupportPrivateTailHeavy_ownerValue_injective
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) :
    Function.Injective (fun b :
      ↥(minimalSupportPrivateTailHeavyVertices g h hmin) ↦ g b.val) := by
  intro b c hbc
  apply Subtype.ext
  apply Subtype.ext
  exact validTuple_injective g hg hbc

/-- A fixed exact-degree profile is a cyclic multiplication fiber with the
sharp torsion-aware bound `gcd(N,d)`. -/
theorem card_minimalSupportPrivateSelfHeavyExactDegreeProfileFiber_le_gcd
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (q : ℕ)
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (hRcard : R.card = q)
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val))
    (p : ℤ × (Fin (m + 1) → ℤ)) :
    (minimalSupportPrivateSelfHeavyExactDegreeProfileFiber
        g h hmin S q p).card ≤ N.gcd p.1.toNat := by
  let F := minimalSupportPrivateSelfHeavyExactDegreeProfileFiber
    g h hmin S q p
  let value : ↥(minimalSupportPrivateTailHeavyVertices g h hmin) → ZMod N :=
    fun b ↦ g b.val
  have hinj : Function.Injective value :=
    minimalSupportPrivateTailHeavy_ownerValue_injective g hg hmin
  have hconst : ∀ b ∈ F,
      p.1.toNat • value b =
        h + ∑ i ∈ R, g i - ∑ i, p.2 i • g i := by
    intro b hb
    have hb' :=
      (mem_minimalSupportPrivateSelfHeavyExactDegreeProfileFiber_iff
        g h hmin S q p b).mp hb
    have hbounds :=
      minimalSupportPrivateSelfHeavyExactDegreeProfileKey_owner_bounds
        g h hmin S q hself hb'.1
    rw [hb'.2] at hbounds
    have hpnonneg : 0 ≤ p.1 := by omega
    have hpcast : ((p.1.toNat : ℕ) : ℤ) = p.1 :=
      Int.toNat_of_nonneg hpnonneg
    have haffine :=
      minimalSupportPrivateSelfHeavyExactDegreeProfileFiber_affine
        g h hmin S R q hself hRcard hfixed p hb
    have howner : p.1 • value b =
        h + ∑ i ∈ R, g i - ∑ i, p.2 i • g i := by
      change p.1 • g b.val =
        h + ∑ i ∈ R, g i - ∑ i, p.2 i • g i
      calc
        p.1 • g b.val =
            (p.1 • g b.val + ∑ i, p.2 i • g i) -
              ∑ i, p.2 i • g i := by abel
        _ = h + ∑ i ∈ R, g i - ∑ i, p.2 i • g i := by
          rw [haffine]
    have howner' : ((p.1.toNat : ℕ) : ℤ) • value b =
        h + ∑ i ∈ R, g i - ∑ i, p.2 i • g i := by
      rw [hpcast]
      exact howner
    simpa only [natCast_zsmul] using howner'
  have hcard := card_le_gcd_of_injective_nsmul_eq_const
    F value hinj p.1.toNat
      (h + ∑ i ∈ R, g i - ∑ i, p.2 i • g i) hconst
  simpa [Nat.card_zmod] using hcard

/-- Coarsening the cyclic kernel by the degree gives at most `q` owners in
every realized fixed-profile fiber. -/
theorem card_minimalSupportPrivateSelfHeavyExactDegreeProfileFiber_le_degree
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (q : ℕ)
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (hRcard : R.card = q)
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val))
    (p : ℤ × (Fin (m + 1) → ℤ))
    (hp : p ∈ minimalSupportPrivateSelfHeavyExactDegreeProfiles
      g h hmin S q) :
    (minimalSupportPrivateSelfHeavyExactDegreeProfileFiber
      g h hmin S q p).card ≤ q := by
  have hkernel :=
    card_minimalSupportPrivateSelfHeavyExactDegreeProfileFiber_le_gcd
      g hg hmin S R q hself hRcard hfixed p
  have hspec := minimalSupportPrivateSelfHeavyExactDegreeProfile_spec
    g h hmin S R q hself hRcard hfixed hp
  have hpnonneg : 0 ≤ p.1 := by omega
  have hpcast : ((p.1.toNat : ℕ) : ℤ) = p.1 :=
    Int.toNat_of_nonneg hpnonneg
  have hlevel : p.1.toNat ≤ q := by
    have hlevel' : ((p.1.toNat : ℕ) : ℤ) ≤ (q : ℤ) := by
      rw [hpcast]
      exact hspec.2.1
    exact_mod_cast hlevel'
  have hlevelPos : 0 < p.1.toNat := by omega
  exact hkernel.trans <| (Nat.gcd_le_right N hlevelPos).trans hlevel

/-- Before counting the keys themselves, exact fiber summation and the
cyclic bound reduce the whole exact-degree layer to `q` times their number. -/
theorem card_minimalSupportPrivateSelfHeavyExactDegreeWithin_le_degree_mul_profiles
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (q : ℕ)
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (hRcard : R.card = q)
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)) :
    (minimalSupportPrivateSelfHeavyExactDegreeWithin
        g h hmin S q).card ≤
      q * (minimalSupportPrivateSelfHeavyExactDegreeProfiles
        g h hmin S q).card := by
  rw [card_minimalSupportPrivateSelfHeavyExactDegreeWithin_eq_sum_profileFibers]
  calc
    (∑ p ∈ minimalSupportPrivateSelfHeavyExactDegreeProfiles g h hmin S q,
        (minimalSupportPrivateSelfHeavyExactDegreeProfileFiber
          g h hmin S q p).card) ≤
      ∑ _p ∈ minimalSupportPrivateSelfHeavyExactDegreeProfiles
          g h hmin S q, q := by
        apply Finset.sum_le_sum
        intro p hp
        exact card_minimalSupportPrivateSelfHeavyExactDegreeProfileFiber_le_degree
          g hg hmin S R q hself hRcard hfixed p hp
    _ = q * (minimalSupportPrivateSelfHeavyExactDegreeProfiles
        g h hmin S q).card := by simp [Nat.mul_comm]

/-- The natural mass recorded on the free-coordinate subtype is exactly the
naturalization of the full integer companion mass. -/
theorem exactDegreeProfileFreeMass_eq_toNat_sum
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
    exactDegreeProfileFreeMass
        (minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R) p =
      (∑ i, p.2 i).toNat := by
  let C := minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R
  have hspec := minimalSupportPrivateSelfHeavyExactDegreeProfile_spec
    g h hmin S R q hself hRcard hfixed hp
  apply sum_toNat_freeCoordinates_eq_toNat_sum p.2 hspec.2.2.1
  intro i hiC
  have hiUnion : i ∈ B ∪ R := by
    by_cases hiB : i ∈ B
    · exact Finset.mem_union_left R hiB
    · apply Finset.mem_union_right B
      by_contra hiR
      apply hiC
      simp [minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates,
        hiB, hiR]
  rcases Finset.mem_union.mp hiUnion with hiB | hiR
  · exact hspec.2.2.2.1 i hiB
  · exact hspec.2.2.2.2.1 i hiR

/-- Every realized companion profile has natural free mass at most `q-2`. -/
theorem exactDegreeProfileFreeMass_le
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
    exactDegreeProfileFreeMass
        (minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R) p ≤
      q - 2 := by
  have hspec := minimalSupportPrivateSelfHeavyExactDegreeProfile_spec
    g h hmin S R q hself hRcard hfixed hp
  rw [exactDegreeProfileFreeMass_eq_toNat_sum
    g h hmin S R q hself hRcard hfixed hp]
  have hsumNonneg : 0 ≤ ∑ i, p.2 i :=
    Finset.sum_nonneg fun i _hi ↦ hspec.2.2.1 i
  omega

/-- A realized exact-degree profile padded to an exact weak composition of
`q-2` over its free coordinates plus one dummy coordinate. -/
noncomputable def minimalSupportPrivateSelfHeavyExactDegreeProfileComposition
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
    (p : ↥(minimalSupportPrivateSelfHeavyExactDegreeProfiles
      g h hmin S q)) :
    ↥((Finset.univ : Finset
        (↥(minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R) ⊕
          Unit)).finsuppAntidiag (q - 2)) := by
  classical
  let C := minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R
  let f := exactDegreeProfilePaddedComposition C (q - 2) p.val
  refine ⟨f, ?_⟩
  rw [Finset.mem_finsuppAntidiag]
  constructor
  · change ∑ x, f x = q - 2
    exact sum_exactDegreeProfilePaddedComposition C (q - 2) p.val
      (exactDegreeProfileFreeMass_le
        g h hmin S R q hself hRcard hfixed p.property)
  · exact Finset.subset_univ f.support

/-- The padded weak-composition encoding is injective on realized profile
keys. -/
theorem minimalSupportPrivateSelfHeavyExactDegreeProfileComposition_injective
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (q : ℕ)
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (hRcard : R.card = q)
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)) :
    Function.Injective
      (minimalSupportPrivateSelfHeavyExactDegreeProfileComposition
        g h hmin S R q hself hRcard hfixed) := by
  let C := minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R
  intro p r hpr
  have hpSpec := minimalSupportPrivateSelfHeavyExactDegreeProfile_spec
    g h hmin S R q hself hRcard hfixed p.property
  have hrSpec := minimalSupportPrivateSelfHeavyExactDegreeProfile_spec
    g h hmin S R q hself hRcard hfixed r.property
  have hcomp : p.val.2 = r.val.2 := by
    funext i
    by_cases hiC : i ∈ C
    · let iC : ↥C := ⟨i, hiC⟩
      have hnat := congrArg
        (fun x ↦ x.val (Sum.inl iC)) hpr
      have hnat' : (p.val.2 i).toNat = (r.val.2 i).toNat := by
        simpa [minimalSupportPrivateSelfHeavyExactDegreeProfileComposition,
          exactDegreeProfilePaddedComposition, C, iC] using hnat
      calc
        p.val.2 i = (((p.val.2 i).toNat : ℕ) : ℤ) :=
          (Int.toNat_of_nonneg (hpSpec.2.2.1 i)).symm
        _ = (((r.val.2 i).toNat : ℕ) : ℤ) := by rw [hnat']
        _ = r.val.2 i := Int.toNat_of_nonneg (hrSpec.2.2.1 i)
    · have hiUnion : i ∈ B ∪ R := by
        by_cases hiB : i ∈ B
        · exact Finset.mem_union_left R hiB
        · apply Finset.mem_union_right B
          by_contra hiR
          apply hiC
          simp [C, minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates,
            hiB, hiR]
      rcases Finset.mem_union.mp hiUnion with hiB | hiR
      · rw [hpSpec.2.2.2.1 i hiB, hrSpec.2.2.2.1 i hiB]
      · rw [hpSpec.2.2.2.2.1 i hiR, hrSpec.2.2.2.2.1 i hiR]
  have hlevel : p.val.1 = r.val.1 := by
    have hpMass := hpSpec.2.2.2.2.2.1
    have hrMass := hrSpec.2.2.2.2.2.1
    rw [hcomp] at hpMass
    omega
  apply Subtype.ext
  exact Prod.ext hlevel hcomp

/-- Stars and bars bounds the number of realized exact-degree keys by the
weak compositions of mass at most `q-2` on the free coordinates. -/
theorem card_minimalSupportPrivateSelfHeavyExactDegreeProfiles_le_choose_free
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (q : ℕ)
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (hRcard : R.card = q)
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val)) :
    (minimalSupportPrivateSelfHeavyExactDegreeProfiles
        g h hmin S q).card ≤
      ((minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R).card +
        (q - 2)).choose (q - 2) := by
  let C := minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates B R
  let P := minimalSupportPrivateSelfHeavyExactDegreeProfiles g h hmin S q
  let A := ↥C ⊕ Unit
  let T := (Finset.univ : Finset A).finsuppAntidiag (q - 2)
  let encode : ↥P → ↥T :=
    minimalSupportPrivateSelfHeavyExactDegreeProfileComposition
      g h hmin S R q hself hRcard hfixed
  have hinj : Function.Injective encode :=
    minimalSupportPrivateSelfHeavyExactDegreeProfileComposition_injective
      g h hmin S R q hself hRcard hfixed
  have hcard : Fintype.card ↥P ≤ Fintype.card ↥T :=
    Fintype.card_le_of_injective encode hinj
  have hcard' : P.card ≤ T.card := by
    simpa only [Fintype.card_coe] using hcard
  rw [Finset.card_finsuppAntidiag_nat_eq_choose] at hcard'
  have hAcard : Fintype.card A = C.card + 1 := by
    simp [A]
  have huniv : (Finset.univ : Finset A).card = C.card + 1 := by
    simpa using hAcard
  have harith : C.card + 1 + (q - 2) - 1 = C.card + (q - 2) := by
    omega
  change P.card ≤
    ((Finset.univ : Finset A).card + (q - 2) - 1).choose (q - 2) at hcard'
  rw [huniv, harith] at hcard'
  simpa [P, C] using hcard'

/-- Substituting the exact free-coordinate count gives the explicit
subtraction-safe profile bound used by the omission recurrence. -/
theorem card_minimalSupportPrivateSelfHeavyExactDegreeProfiles_le_choose
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
    (hRB : Disjoint R B) :
    (minimalSupportPrivateSelfHeavyExactDegreeProfiles
        g h hmin S q).card ≤
      (m + 1 - (B.card + q) + (q - 2)).choose (q - 2) := by
  have hbound := card_minimalSupportPrivateSelfHeavyExactDegreeProfiles_le_choose_free
    g h hmin S R q hself hRcard hfixed
  rw [card_minimalSupportPrivateSelfHeavyExactDegreeFreeCoordinates
    B R hRB, hRcard] at hbound
  exact hbound

/-- Uniform cyclic/stars-and-bars bound for the entire exact-degree owner
layer. -/
theorem card_minimalSupportPrivateSelfHeavyExactDegreeWithin_le
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (S : Finset ↥(minimalSupportPrivateTailHeavyVertices g h hmin))
    (R : Finset (Fin (m + 1))) (q : ℕ)
    (hself : ∀ b ∈ S,
      b ∈ minimalSupportPrivateSelfHeavyVertices g h hmin)
    (hRcard : R.card = q)
    (hfixed : ∀ b ∈ S, R ⊆ witnessOmissionCoordinates
      (minimalSupportPrivateWitness g h hmin b.val))
    (hRB : Disjoint R B) :
    (minimalSupportPrivateSelfHeavyExactDegreeWithin
        g h hmin S q).card ≤
      q * (m + 1 - (B.card + q) + (q - 2)).choose (q - 2) := by
  have hfibers :=
    card_minimalSupportPrivateSelfHeavyExactDegreeWithin_le_degree_mul_profiles
      g hg hmin S R q hself hRcard hfixed
  have hprofiles :=
    card_minimalSupportPrivateSelfHeavyExactDegreeProfiles_le_choose
      g h hmin S R q hself hRcard hfixed hRB
  exact hfibers.trans (Nat.mul_le_mul_left q hprofiles)

/-- The first concrete application of the uniform bound: every four-fixed
exact-four layer has a quadratic stars-and-bars bound, uniformly in the
modulus. -/
theorem card_minimalSupportPrivateSelfHeavyQuadrupleExactFourOwners_le
    {N : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    {h : ZMod N} {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z w u v : Fin (m + 1))
    (hzB : z ∉ B) (hwB : w ∉ B) (huB : u ∉ B) (hvB : v ∉ B)
    (hwz : w ≠ z) (huz : u ≠ z) (huw : u ≠ w)
    (hvz : v ≠ z) (hvw : v ≠ w) (hvu : v ≠ u) :
    (minimalSupportPrivateSelfHeavyQuadrupleExactFourOwners
        g h hmin z w u v).card ≤
      4 * (m + 1 - (B.card + 4) + 2).choose 2 := by
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
  have hbound := card_minimalSupportPrivateSelfHeavyExactDegreeWithin_le
    g hg hmin Q R 4 hself hset.2 hfixed hset.1
  simpa [minimalSupportPrivateSelfHeavyQuadrupleExactFourOwners, Q, R] using
    hbound

/-- Substitute the uniform exact-four count into the four-stage global
omission endpoint.  Its sole unbounded omission branch now has witness
degree at least five. -/
theorem minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_boundedExactThree_or_boundedQuadrupleExactFour_or_atLeastFive
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
            (4 * (m + 1 - (B.card + 4) + 2).choose 2)) ∨
          r''' + 1 ≤ 2 *
            (minimalSupportPrivateSelfHeavyQuadrupleAtLeastFiveOwners
              g h hmin z w u v).card) := by
  rcases
      minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_boundedExactThree_or_quadrupleExactFour_or_atLeastFive
        g hg hmin K L r L' r' L'' r'' L''' r'''
          hself hfirst hsecond hthird hfourth with
    htwo | hcap | hcap' | hcap'' | hexact | hcap''' |
      ⟨z, w, u, v, hzB, hwB, huB, hvB, hwz, huz, huw,
        hvz, hvw, hvu, hfour | hfive⟩
  · exact Or.inl htwo
  · exact Or.inr (Or.inl hcap)
  · exact Or.inr (Or.inr (Or.inl hcap'))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hcap'')))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hexact))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcap''')))))
  · have hbound :=
      card_minimalSupportPrivateSelfHeavyQuadrupleExactFourOwners_le
        g hg hmin z w u v hzB hwB huB hvB hwz huz huw hvz hvw hvu
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨z, w, u, v, hzB, hwB, huB, hvB, hwz, huz, huw, hvz, hvw, hvu,
        Or.inl (hfour.trans (Nat.mul_le_mul_left 2 hbound))⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨z, w, u, v, hzB, hwB, huB, hvB, hwz, huz, huw, hvz, hvw, hvu,
        Or.inr hfive⟩)))))

end MinModulus
