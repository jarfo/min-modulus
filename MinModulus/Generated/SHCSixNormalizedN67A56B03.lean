import MinModulus.Generated.SHCSixNormalizedN67A56B01

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a56_b03_c00 (q : Σ d : Fin (4 - 0 - 2), Fin (4 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 58 62 ⟨(⟨0, by norm_num⟩ : Fin (4 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a56_b03_c01 (q : Σ d : Fin (4 - 1 - 2), Fin (4 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 58 62 ⟨(⟨1, by norm_num⟩ : Fin (4 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a56_b03 (q : IncreasingThree 4) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 58 62 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a56_b03_c00 q
  · exact certificate67_a56_b03_c01 q

end MinModulus.SHCSixCertificate.Generated
