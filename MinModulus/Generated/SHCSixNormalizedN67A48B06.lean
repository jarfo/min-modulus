import MinModulus.Generated.SHCSixNormalizedN67A48B04

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a48_b06_c00 (q : Σ d : Fin (9 - 0 - 2), Fin (9 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 50 57 ⟨(⟨0, by norm_num⟩ : Fin (9 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a48_b06_c01 (q : Σ d : Fin (9 - 1 - 2), Fin (9 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 50 57 ⟨(⟨1, by norm_num⟩ : Fin (9 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a48_b06_c02 (q : Σ d : Fin (9 - 2 - 2), Fin (9 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 50 57 ⟨(⟨2, by norm_num⟩ : Fin (9 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a48_b06_c03 (q : Σ d : Fin (9 - 3 - 2), Fin (9 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 50 57 ⟨(⟨3, by norm_num⟩ : Fin (9 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a48_b06_c04 (q : Σ d : Fin (9 - 4 - 2), Fin (9 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 50 57 ⟨(⟨4, by norm_num⟩ : Fin (9 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a48_b06_c05 (q : Σ d : Fin (9 - 5 - 2), Fin (9 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 50 57 ⟨(⟨5, by norm_num⟩ : Fin (9 - 2)), q⟩) code = true := by
  exact ⟨8322, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a48_b06_c06 (q : Σ d : Fin (9 - 6 - 2), Fin (9 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 50 57 ⟨(⟨6, by norm_num⟩ : Fin (9 - 2)), q⟩) code = true := by
  exact ⟨7938, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a48_b06 (q : IncreasingThree 9) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 50 57 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a48_b06_c00 q
  · exact certificate67_a48_b06_c01 q
  · exact certificate67_a48_b06_c02 q
  · exact certificate67_a48_b06_c03 q
  · exact certificate67_a48_b06_c04 q
  · exact certificate67_a48_b06_c05 q
  · exact certificate67_a48_b06_c06 q

end MinModulus.SHCSixCertificate.Generated
