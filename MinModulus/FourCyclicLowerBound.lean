import MinModulus.FourModTenCertificate
import MinModulus.PrimitiveCriticalInduction
import MinModulus.OddOrder

namespace MinModulus
open Finset

/-- Equality in the abelian cardinal bound cannot occur modulo eight. -/
theorem not_validTuple_four_mod_eight (g : Fin 4 → ZMod 8) : ¬ ValidTuple g := by
  intro hg
  have hh := equality_order_two g hg (by norm_num [ZMod.card]) (1 : ZMod 8)
  exact (by decide : (2 : ZMod 8) ≠ 0) (by simpa using hh)

/-- Every cyclic valid four-tuple has modulus at least twelve. -/
theorem cyclic_lower_bound_four {N : ℕ} (hN : 0 < N)
    (g : Fin 4 → ZMod N) (hg : ValidTuple g) : 12 ≤ N := by
  letI : NeZero N := ⟨hN.ne'⟩
  have hb : 8 ≤ N := by simpa only [ZMod.card,Nat.reducePow] using card_ge g hg
  by_contra hn
  have hcases : N=8 ∨ N=9 ∨ N=10 ∨ N=11 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact not_validTuple_four_mod_eight g hg
  · have hh := odd_min_four (by decide : Odd 9) g hg
    omega
  · exact not_validTuple_four_mod_ten g hg
  · have hh := odd_min_four (by decide : Odd 11) g hg
    omega

/-- Every exact two-adic stratum satisfies the conjectured four-tuple bound. -/
theorem stratum_lower_bound_four {s q : ℕ} (hq : Odd q)
    (g : Fin 4 → ZMod (2^s*q)) (hg : ValidTuple g) :
    stratumBound 4 s ≤ 2^s*q := by
  have hpos : 0 < 2^s*q := mul_pos (by positivity) hq.pos
  have hb := cyclic_lower_bound_four hpos g hg
  rcases s with _ | s
  · have hv : AdmitsValidTuple 4 q := by
      simpa only [pow_zero,one_mul] using
        (show AdmitsValidTuple 4 (2^0*q) from ⟨g,hg⟩)
    obtain ⟨w,hw⟩ := hv
    simpa [stratumBound,show Nat.log 2 4=2 by decide] using odd_min_four hq w hw
  · rcases s with _ | s
    · have hpar := hq
      rcases hpar with ⟨k,hk⟩
      norm_num [stratumBound,show Nat.log 2 4=2 by decide] at hb ⊢
      omega
    · have hs : min (s+1+1) (Nat.log 2 4)=2 := by norm_num
      simpa only [stratumBound,hs,Nat.reducePow,Nat.reduceSub] using hb

/-- Primitive G1 above an explicit lower bound on child dimension. -/
def PrimitiveThreeOmissionDeleteStepFrom (k : ℕ) : Prop :=
  ∀ {n s q : ℕ}, k ≤ n → Odd q →
    ∀ g : Fin (n+1) → ZMod (2^(s+1)*q), ValidTuple g →
      2^(s+1)*q < stratumBound (n+1) (s+1) →
      WitnessThreeDistinctOmissions g ((2^s*q : ℕ) : ZMod (2^(s+1)*q)) →
      (∀ (j : Fin (n+1)) (a : Fin n), AddSubgroup.closure
        (Set.range (fun i : Fin n ↦ g (j.succAbove i)-g (j.succAbove a)))=⊤) →
      AdmitsValidTuple n (2^s*q)

/-- The four-coordinate stratum bound removes the first primitive G1 case. -/
theorem primitiveThreeOmissionDeleteStep_iff_from_four :
    PrimitiveThreeOmissionDeleteStep ↔ PrimitiveThreeOmissionDeleteStepFrom 4 := by
  constructor
  · intro h n s q hn hq g hg hc hw hp
    exact h (by omega) hq g hg hc hw hp
  · intro h n s q hn hq g hg hc hw hp
    by_cases hn4 : 4 ≤ n
    · exact h hn4 hq g hg hc hw hp
    · have hn3 : n=3 := by omega
      subst n
      have hb := stratum_lower_bound_four hq g hg
      exact (Nat.not_lt_of_ge hb hc).elim

end MinModulus
