import MinModulus.Generated.SHCSixNormalizedN67A35B23

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a35_b25_c00 (q : Σ d : Fin (3 - 0 - 2), Fin (3 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 37 63 ⟨(⟨0, by norm_num⟩ : Fin (3 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a35_b25 (q : IncreasingThree 3) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 37 63 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a35_b25_c00 q

end MinModulus.SHCSixCertificate.Generated
