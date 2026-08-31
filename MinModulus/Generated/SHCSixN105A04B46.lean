import MinModulus.Generated.SHCSixN105A04B44

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a04_b46_c00 (q : Σ d : Fin (3 - 0 - 2), Fin (3 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨51, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (3 - 2)), q⟩) code = true := by
  exact ⟨385, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a04_b46 (q : IncreasingThree 3) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨51, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a04_b46_c00 q

end MinModulus.SHCSixExceptionalCertificate.Generated
