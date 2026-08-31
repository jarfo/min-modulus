import MinModulus.Generated.SHCSixNormalizedN67A02B42

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a02_b44_c00 (q : Σ d : Fin (17 - 0 - 2), Fin (17 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 ⟨(⟨0, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a02_b44_c01 (q : Σ d : Fin (17 - 1 - 2), Fin (17 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 ⟨(⟨1, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨6448, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a02_b44_c02 (q : Σ d : Fin (17 - 2 - 2), Fin (17 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 ⟨(⟨2, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a02_b44_c03 (q : Σ d : Fin (17 - 3 - 2), Fin (17 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 ⟨(⟨3, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a02_b44_c04 (q : Σ d : Fin (17 - 4 - 2), Fin (17 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 ⟨(⟨4, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨519, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a02_b44_c05 (q : Σ d : Fin (17 - 5 - 2), Fin (17 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 ⟨(⟨5, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a02_b44_c06 (q : Σ d : Fin (17 - 6 - 2), Fin (17 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 ⟨(⟨6, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨7577, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a02_b44_c07 (q : Σ d : Fin (17 - 7 - 2), Fin (17 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 ⟨(⟨7, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a02_b44_c08 (q : Σ d : Fin (17 - 8 - 2), Fin (17 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 ⟨(⟨8, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨5635, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a02_b44_c09 (q : Σ d : Fin (17 - 9 - 2), Fin (17 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 ⟨(⟨9, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a02_b44_c10 (q : Σ d : Fin (17 - 10 - 2), Fin (17 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 ⟨(⟨10, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨6403, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a02_b44_c11 (q : Σ d : Fin (17 - 11 - 2), Fin (17 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 ⟨(⟨11, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a02_b44_c12 (q : Σ d : Fin (17 - 12 - 2), Fin (17 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 ⟨(⟨12, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a02_b44_c13 (q : Σ d : Fin (17 - 13 - 2), Fin (17 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 ⟨(⟨13, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a02_b44_c14 (q : Σ d : Fin (17 - 14 - 2), Fin (17 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 ⟨(⟨14, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a02_b44 (q : IncreasingThree 17) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 4 49 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a02_b44_c00 q
  · exact certificate67_a02_b44_c01 q
  · exact certificate67_a02_b44_c02 q
  · exact certificate67_a02_b44_c03 q
  · exact certificate67_a02_b44_c04 q
  · exact certificate67_a02_b44_c05 q
  · exact certificate67_a02_b44_c06 q
  · exact certificate67_a02_b44_c07 q
  · exact certificate67_a02_b44_c08 q
  · exact certificate67_a02_b44_c09 q
  · exact certificate67_a02_b44_c10 q
  · exact certificate67_a02_b44_c11 q
  · exact certificate67_a02_b44_c12 q
  · exact certificate67_a02_b44_c13 q
  · exact certificate67_a02_b44_c14 q

end MinModulus.SHCSixCertificate.Generated
