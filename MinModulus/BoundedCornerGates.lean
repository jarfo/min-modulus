import MinModulus.LinearCycleEscape

/-! The original three conjecture gates retain two proved restrictions:
every bounded-corner family charge fails, and shifts supporting an actual
cycle have more escapes than the sharper linear threshold. This implies
the earlier rectangular profile obstruction and keeps every previous
quantitative escape restriction. Equivalences and the original induction
assemblies still have precisely three open inputs. None is asserted. -/

namespace MinModulus
open Finset
open scoped Classical

/-- The exact bounded-corner obstruction and the sharper escape condition
at every shift supporting an actual affine cycle. -/
def BoundedCornerCycleObstruction {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) : Prop :=
  (∀ (r : ℕ) (b : G) (x : Fin r → G) (L : Fin r → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n),
    (∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a) →
    ∀ a : Fin r, 4 ≤ L a → 2^(L a-3) < chainFamilyCornerError n L) ∧
  (3 ≤ n → ∀ (b : G) (m : ℕ), 0 < m → ∀ (e : Fin m ↪ Fin n) (R : Equiv.Perm (Fin m)),
    (∀ i, g (e (R i))=2 • g (e i)+b) →
    n < 5*(Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card+1)

/-- The stronger obstruction retains the previously proved profile restriction. -/
theorem bounded_corner_cycle_obstruction_implies_profile
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (h : BoundedCornerCycleObstruction g) : AffineChainProfileObstruction g := by
  intro r b x L e hc a ha
  apply (h.1 r b x L e hc a ha).trans_le
  exact Nat.mul_le_mul_right _ (chain_family_corner_card_le_product n L)

/-- Every hypothetical global counterexample satisfies both restrictions. -/
theorem bounded_corner_cycle_obstruction_of_global_counterexample
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hsmall : N < globalBound n) : BoundedCornerCycleObstruction g := by
  constructor
  · intro r b x L e hc a ha
    by_contra hh
    have h := global_lower_bound_of_bounded_corner_family g hg b x L e hc a ha (by omega)
    omega
  · intro hn b m hm e R hc
    have h := linear_escapes_of_global_counterexample_with_affine_cycle hn hm g hg hsmall b e R hc
    convert h using 2
    congr

/-- Every hypothetical original exact-stratum counterexample satisfies both restrictions. -/
theorem bounded_corner_cycle_obstruction_of_stratum_counterexample
    {n s q : ℕ} (hq : Odd q) (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (hsmall : 2^s*q < stratumBound n s) : BoundedCornerCycleObstruction g := by
  constructor
  · intro r b x L e hc a ha
    by_contra hh
    have h := stratum_lower_bound_of_bounded_corner_family hq g hg b x L e hc a ha (by omega)
    omega
  · intro hn b m hm e R hc
    have h := linear_escapes_of_stratum_counterexample_with_affine_cycle hq hn hm g hg hsmall b e R hc
    convert h using 2
    congr

/-- The original odd target is retained without weakening its modulus bound. -/
theorem bounded_corner_cycle_obstruction_of_odd_counterexample
    {n N : ℕ} (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hsmall : N < 2^n-1) : BoundedCornerCycleObstruction g := by
  have h := bounded_corner_cycle_obstruction_of_stratum_counterexample (n:=n) (s:=0) hN
  rw [show (2 : ℕ)^0*N=N by simp] at h
  exact h g hg (by simpa [stratumBound] using hsmall)

/-- Every hypothetical original exceptional tuple has both obstructions. -/
theorem bounded_corner_cycle_obstruction_of_exceptional_tuple
    {n : ℕ} (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1))) (hg : ValidTuple g) :
    BoundedCornerCycleObstruction g := by
  constructor
  · intro r b x L e hc a ha
    by_contra hh
    exact not_validTuple_exceptional_of_bounded_corner_family hnpow g b x L e hc a ha (by omega) hg
  · intro hn b m hm e R hc
    have h := linear_escapes_of_exceptional_tuple_with_affine_cycle hn hm hnpow g hg b e R hc
    convert h using 2
    congr

/-- The existing quantitative residual with both proved geometric restrictions. -/
def PrimitiveBoundedCornerDeleteStep : Prop :=
  ∀ {n s q : ℕ}, 4 ≤ n → Odd q →
    ∀ g : Fin (n+1) → ZMod (2^(s+1)*q), ValidTuple g →
      2^(s+1)*q < stratumBound (n+1) (s+1) →
      WitnessThreeDistinctOmissions g ((2^s*q : ℕ) : ZMod (2^(s+1)*q)) →
      (∀ (j : Fin (n+1)) (a : Fin n), AddSubgroup.closure
        (Set.range (fun i : Fin n ↦ g (j.succAbove i)-g (j.succAbove a)))=⊤) →
      (∀ b : ZMod (2^(s+1)*q),
        3 ≤ (Finset.univ.filter (fun i ↦ ∀ j, g j ≠ 2 • g i+b)).card) →
      (51 ≤ n → ∀ b : ZMod (2^(s+1)*q),
        4 ≤ (Finset.univ.filter (fun i ↦ ∀ j, g j ≠ 2 • g i+b)).card) →
      (100 ≤ n → ∀ b : ZMod (2^(s+1)*q),
        5 ≤ (Finset.univ.filter (fun i ↦ ∀ j, g j ≠ 2 • g i+b)).card) →
      (∀ (b : ZMod (2^(s+1)*q)) (r : ℕ),
        (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r →
        2^((n+1)/r-3) < (n+r).choose r) →
      BoundedCornerCycleObstruction g →
      AdmitsValidTuple n (2^s*q)

/-- The existing quantitative residual with both proved geometric restrictions. -/
def OddBoundedCornerLowerBound : Prop :=
  ∀ {n N : ℕ}, Odd N → ∀ g : Fin n → ZMod N, ValidTuple g →
    (4 ≤ n → ∀ (b : ZMod N) (r : ℕ),
      (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r →
      2^(n/r-3) < (n+r-1).choose r) →
    BoundedCornerCycleObstruction g →
    2^n-1 ≤ N

/-- The existing quantitative residual with both proved geometric restrictions. -/
def ExceptionalBoundedCornerObstruction : Prop :=
  ∀ n : ℕ, 2 ≤ n → 2^Nat.log 2 n ≠ n →
    ∀ g : Fin n → ZMod (2*globalBound (n-1)), ValidTuple g →
      (4 ≤ n → ∀ (b : ZMod (2*globalBound (n-1))) (r : ℕ),
        (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r →
        2^((n+r)/(r+1)-3) < (n+r).choose (r+1) ∧
          n < (r+1)^2*(Nat.log 2 n+1)+3*(r+1)) →
      BoundedCornerCycleObstruction g →
      False

/-- The original primitive G1 gate is equivalent to its profile restriction. -/
theorem primitiveThreeOmissionDeleteStep_iff_boundedCorner :
    PrimitiveThreeOmissionDeleteStep ↔ PrimitiveBoundedCornerDeleteStep := by
  rw [primitiveThreeOmissionDeleteStep_iff_quantitativeEscape]
  constructor
  · intro h n s q hn hq g hg hc hthree hfull hescape hfour hfive hquant _
    exact h hn hq g hg hc hthree hfull hescape hfour hfive hquant
  · intro h n s q hn hq g hg hc hthree hfull hescape hfour hfive hquant
    exact h hn hq g hg hc hthree hfull hescape hfour hfive hquant
      (bounded_corner_cycle_obstruction_of_stratum_counterexample hq g hg hc)

/-- The original G2 gate retains all dimensions and its exact target. -/
theorem oddStratumLowerBound_iff_boundedCorner :
    OddStratumLowerBound ↔ OddBoundedCornerLowerBound := by
  rw [oddStratumLowerBound_iff_quantitativeEscape]
  constructor
  · intro h n N hN g hg hquant _
    exact h hN g hg hquant
  · intro h n N hN g hg hquant
    by_contra hh
    exact hh (h hN g hg hquant (bounded_corner_cycle_obstruction_of_odd_counterexample hN g hg (by omega)))

/-- The original G3 gate is equivalent to its all-family restriction. -/
theorem exceptionalLiftObstruction_iff_boundedCorner :
    ExceptionalLiftObstruction ↔ ExceptionalBoundedCornerObstruction := by
  rw [exceptionalLiftObstruction_iff_quantitativeEscape]
  constructor
  · intro h n hn hnpow g hg hquant _
    exact h n hn hnpow g hg hquant
  · intro h n hn hnpow g hg hquant
    exact h n hn hnpow g hg hquant (bounded_corner_cycle_obstruction_of_exceptional_tuple hnpow g hg)

/-- Exact-stratum induction uses precisely the same three equivalent gates. -/
theorem stratum_lower_bound_of_three_bounded_corner_inputs
    (hG1 : PrimitiveBoundedCornerDeleteStep) (hG2 : OddBoundedCornerLowerBound)
    (hG3 : ExceptionalBoundedCornerObstruction)
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q) (hv : AdmitsValidTuple n (2^s*q)) :
    stratumBound n s ≤ 2^s*q :=
  stratum_lower_bound_of_primitive_threeOmissionDeleteStep
    (primitiveThreeOmissionDeleteStep_iff_boundedCorner.mpr hG1)
    (oddStratumLowerBound_iff_boundedCorner.mpr hG2)
    (exceptionalLiftObstruction_iff_boundedCorner.mpr hG3) hn hq hv

/-- Global induction retains exactly G1/G2/G3, with no fourth input. -/
theorem global_lower_bound_of_three_bounded_corner_inputs
    (hG1 : PrimitiveBoundedCornerDeleteStep) (hG2 : OddBoundedCornerLowerBound)
    (hG3 : ExceptionalBoundedCornerObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) : globalBound n ≤ N :=
  global_lower_bound_of_primitive_threeOmissionDeleteStep
    (primitiveThreeOmissionDeleteStep_iff_boundedCorner.mpr hG1)
    (oddStratumLowerBound_iff_boundedCorner.mpr hG2)
    (exceptionalLiftObstruction_iff_boundedCorner.mpr hG3) hn hN hv

end MinModulus
