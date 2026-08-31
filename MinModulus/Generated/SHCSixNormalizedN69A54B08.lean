import MinModulus.Generated.SHCSixNormalizedN69A54B06

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate69_a54_b08_c00 (q : Σ d : Fin (3 - 0 - 2), Fin (3 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 56 65 ⟨(⟨0, by norm_num⟩ : Fin (3 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate69_a54_b08 (q : IncreasingThree 3) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 56 65 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate69_a54_b08_c00 q

end MinModulus.SHCSixCertificate.Generated
