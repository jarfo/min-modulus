import MinModulus.ChainFamilyWithoutCover
import MinModulus.G3QuantitativeEscape

/-! Every counterexample fails the exact family charge at every affine
shift. This necessary condition restricts each existing quantitative
G1/G2/G3 residual without changing its original obligation. Equivalences
and the exact-stratum/global assemblies retain exactly three open inputs;
none of the unrestricted conjecture gates is asserted here. -/

namespace MinModulus
open Finset

/-- Every embedded actual family at every affine shift fails the exact
charge on each member of length at least four. -/
def AffineChainProfileObstruction {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) : Prop :=
  ∀ (r : ℕ) (b : G) (x : Fin r → G) (L : Fin r → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n),
    (∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a) →
    ∀ a : Fin r, 4 ≤ L a → 2^(L a-3) < chainFamilyTruncatedError n L

/-- Every hypothetical global counterexample carries the profile obstruction. -/
theorem affine_chain_profile_obstruction_of_global_counterexample
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hsmall : N < globalBound n) : AffineChainProfileObstruction g := by
  intro r b x L e hchain a ha
  by_contra hh
  have h := global_lower_bound_of_truncated_family_without_cover g hg b x L e hchain a ha (by omega)
  omega

/-- Every hypothetical exact-stratum counterexample has the same obstruction. -/
theorem affine_chain_profile_obstruction_of_stratum_counterexample
    {n s q : ℕ} (hq : Odd q) (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (hsmall : 2^s*q < stratumBound n s) : AffineChainProfileObstruction g := by
  intro r b x L e hchain a ha
  by_contra hh
  have h := stratum_lower_bound_of_truncated_family_without_cover hq g hg b x L e hchain a ha (by omega)
  omega

/-- The full odd-stratum obstruction uses its original binary-minus-one target. -/
theorem affine_chain_profile_obstruction_of_odd_counterexample
    {n N : ℕ} (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hsmall : N < 2^n-1) : AffineChainProfileObstruction g := by
  have h := affine_chain_profile_obstruction_of_stratum_counterexample (n:=n) (s:=0) hN
  have he : (2 : ℕ)^0*N=N := by simp
  rw [he] at h
  exact h g hg (by simpa [stratumBound] using hsmall)

/-- Every hypothetical exceptional G3 tuple has the profile obstruction. -/
theorem affine_chain_profile_obstruction_of_exceptional_tuple
    {n : ℕ} (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1))) (hg : ValidTuple g) :
    AffineChainProfileObstruction g := by
  intro r b x L e hchain a ha
  by_contra hh
  exact not_validTuple_exceptional_of_truncated_family_without_cover hnpow g b x L e hchain a ha (by omega) hg

/-- The existing quantitative residual, restricted by the proved profile obstruction. -/
def PrimitiveChainProfileDeleteStep : Prop :=
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
      AffineChainProfileObstruction g →
      AdmitsValidTuple n (2^s*q)

/-- The existing quantitative residual, restricted by the proved profile obstruction. -/
def OddChainProfileLowerBound : Prop :=
  ∀ {n N : ℕ}, Odd N → ∀ g : Fin n → ZMod N, ValidTuple g →
    (4 ≤ n → ∀ (b : ZMod N) (r : ℕ),
      (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r →
      2^(n/r-3) < (n+r-1).choose r) →
    AffineChainProfileObstruction g →
    2^n-1 ≤ N

/-- The existing quantitative residual, restricted by the proved profile obstruction. -/
def ExceptionalChainProfileObstruction : Prop :=
  ∀ n : ℕ, 2 ≤ n → 2^Nat.log 2 n ≠ n →
    ∀ g : Fin n → ZMod (2*globalBound (n-1)), ValidTuple g →
      (4 ≤ n → ∀ (b : ZMod (2*globalBound (n-1))) (r : ℕ),
        (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r →
        2^((n+r)/(r+1)-3) < (n+r).choose (r+1) ∧
          n < (r+1)^2*(Nat.log 2 n+1)+3*(r+1)) →
      AffineChainProfileObstruction g →
      False

/-- The original primitive G1 gate is equivalent to its profile restriction. -/
theorem primitiveThreeOmissionDeleteStep_iff_chainProfile :
    PrimitiveThreeOmissionDeleteStep ↔ PrimitiveChainProfileDeleteStep := by
  rw [primitiveThreeOmissionDeleteStep_iff_quantitativeEscape]
  constructor
  · intro h n s q hn hq g hg hc hthree hfull hescape hfour hfive hquant _
    exact h hn hq g hg hc hthree hfull hescape hfour hfive hquant
  · intro h n s q hn hq g hg hc hthree hfull hescape hfour hfive hquant
    exact h hn hq g hg hc hthree hfull hescape hfour hfive hquant
      (affine_chain_profile_obstruction_of_stratum_counterexample hq g hg hc)

/-- The original G2 gate retains all dimensions and its exact target. -/
theorem oddStratumLowerBound_iff_chainProfile :
    OddStratumLowerBound ↔ OddChainProfileLowerBound := by
  rw [oddStratumLowerBound_iff_quantitativeEscape]
  constructor
  · intro h n N hN g hg hquant _
    exact h hN g hg hquant
  · intro h n N hN g hg hquant
    by_contra hh
    exact hh (h hN g hg hquant (affine_chain_profile_obstruction_of_odd_counterexample hN g hg (by omega)))

/-- The original G3 gate is equivalent to its all-family restriction. -/
theorem exceptionalLiftObstruction_iff_chainProfile :
    ExceptionalLiftObstruction ↔ ExceptionalChainProfileObstruction := by
  rw [exceptionalLiftObstruction_iff_quantitativeEscape]
  constructor
  · intro h n hn hnpow g hg hquant _
    exact h n hn hnpow g hg hquant
  · intro h n hn hnpow g hg hquant
    exact h n hn hnpow g hg hquant (affine_chain_profile_obstruction_of_exceptional_tuple hnpow g hg)

/-- Exact-stratum induction uses precisely the same three equivalent gates. -/
theorem stratum_lower_bound_of_three_chain_profile_inputs
    (hG1 : PrimitiveChainProfileDeleteStep) (hG2 : OddChainProfileLowerBound)
    (hG3 : ExceptionalChainProfileObstruction)
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q) (hv : AdmitsValidTuple n (2^s*q)) :
    stratumBound n s ≤ 2^s*q :=
  stratum_lower_bound_of_primitive_threeOmissionDeleteStep
    (primitiveThreeOmissionDeleteStep_iff_chainProfile.mpr hG1)
    (oddStratumLowerBound_iff_chainProfile.mpr hG2)
    (exceptionalLiftObstruction_iff_chainProfile.mpr hG3) hn hq hv

/-- Global induction retains exactly G1/G2/G3, with no fourth input. -/
theorem global_lower_bound_of_three_chain_profile_inputs
    (hG1 : PrimitiveChainProfileDeleteStep) (hG2 : OddChainProfileLowerBound)
    (hG3 : ExceptionalChainProfileObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) : globalBound n ≤ N :=
  global_lower_bound_of_primitive_threeOmissionDeleteStep
    (primitiveThreeOmissionDeleteStep_iff_chainProfile.mpr hG1)
    (oddStratumLowerBound_iff_chainProfile.mpr hG2)
    (exceptionalLiftObstruction_iff_chainProfile.mpr hG3) hn hN hv

end MinModulus
