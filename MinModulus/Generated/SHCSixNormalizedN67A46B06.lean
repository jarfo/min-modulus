import MinModulus.Generated.SHCSixNormalizedN67A46B04

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a46_b06_c00 (q : Σ d : Fin (11 - 0 - 2), Fin (11 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 48 55 ⟨(⟨0, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a46_b06_c01 (q : Σ d : Fin (11 - 1 - 2), Fin (11 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 48 55 ⟨(⟨1, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a46_b06_c02 (q : Σ d : Fin (11 - 2 - 2), Fin (11 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 48 55 ⟨(⟨2, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨5251, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a46_b06_c03 (q : Σ d : Fin (11 - 3 - 2), Fin (11 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 48 55 ⟨(⟨3, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a46_b06_c04 (q : Σ d : Fin (11 - 4 - 2), Fin (11 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 48 55 ⟨(⟨4, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a46_b06_c05 (q : Σ d : Fin (11 - 5 - 2), Fin (11 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 48 55 ⟨(⟨5, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a46_b06_c06 (q : Σ d : Fin (11 - 6 - 2), Fin (11 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 48 55 ⟨(⟨6, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a46_b06_c07 (q : Σ d : Fin (11 - 7 - 2), Fin (11 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 48 55 ⟨(⟨7, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨7944, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a46_b06_c08 (q : Σ d : Fin (11 - 8 - 2), Fin (11 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 48 55 ⟨(⟨8, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨5275, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a46_b06 (q : IncreasingThree 11) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 48 55 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a46_b06_c00 q
  · exact certificate67_a46_b06_c01 q
  · exact certificate67_a46_b06_c02 q
  · exact certificate67_a46_b06_c03 q
  · exact certificate67_a46_b06_c04 q
  · exact certificate67_a46_b06_c05 q
  · exact certificate67_a46_b06_c06 q
  · exact certificate67_a46_b06_c07 q
  · exact certificate67_a46_b06_c08 q

end MinModulus.SHCSixCertificate.Generated
