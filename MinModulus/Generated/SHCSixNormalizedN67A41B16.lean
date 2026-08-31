import MinModulus.Generated.SHCSixNormalizedN67A41B14

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a41_b16_c00 (q : Σ d : Fin (6 - 0 - 2), Fin (6 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 60 ⟨(⟨0, by norm_num⟩ : Fin (6 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b16_c01 (q : Σ d : Fin (6 - 1 - 2), Fin (6 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 60 ⟨(⟨1, by norm_num⟩ : Fin (6 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b16_c02 (q : Σ d : Fin (6 - 2 - 2), Fin (6 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 60 ⟨(⟨2, by norm_num⟩ : Fin (6 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b16_c03 (q : Σ d : Fin (6 - 3 - 2), Fin (6 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 60 ⟨(⟨3, by norm_num⟩ : Fin (6 - 2)), q⟩) code = true := by
  exact ⟨6019, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a41_b16 (q : IncreasingThree 6) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 60 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a41_b16_c00 q
  · exact certificate67_a41_b16_c01 q
  · exact certificate67_a41_b16_c02 q
  · exact certificate67_a41_b16_c03 q

end MinModulus.SHCSixCertificate.Generated
