import MinModulus.Generated.SHCSixNormalizedN67A10B46

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a10_b48_c00 (q : Σ d : Fin (5 - 0 - 2), Fin (5 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 12 61 ⟨(⟨0, by norm_num⟩ : Fin (5 - 2)), q⟩) code = true := by
  exact ⟨897, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a10_b48_c01 (q : Σ d : Fin (5 - 1 - 2), Fin (5 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 12 61 ⟨(⟨1, by norm_num⟩ : Fin (5 - 2)), q⟩) code = true := by
  exact ⟨9472, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a10_b48_c02 (q : Σ d : Fin (5 - 2 - 2), Fin (5 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 12 61 ⟨(⟨2, by norm_num⟩ : Fin (5 - 2)), q⟩) code = true := by
  exact ⟨5635, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a10_b48 (q : IncreasingThree 5) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 12 61 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a10_b48_c00 q
  · exact certificate67_a10_b48_c01 q
  · exact certificate67_a10_b48_c02 q

end MinModulus.SHCSixCertificate.Generated
