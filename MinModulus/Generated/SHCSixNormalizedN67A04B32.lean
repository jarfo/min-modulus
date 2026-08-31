import MinModulus.Generated.SHCSixNormalizedN67A04B30

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a04_b32_c00 (q : Σ d : Fin (27 - 0 - 2), Fin (27 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨0, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c01 (q : Σ d : Fin (27 - 1 - 2), Fin (27 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨1, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  exact ⟨8711, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c02 (q : Σ d : Fin (27 - 2 - 2), Fin (27 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨2, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11791, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6404, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c03 (q : Σ d : Fin (27 - 3 - 2), Fin (27 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨3, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  exact ⟨6448, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c04 (q : Σ d : Fin (27 - 4 - 2), Fin (27 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨4, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c05 (q : Σ d : Fin (27 - 5 - 2), Fin (27 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨5, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c06 (q : Σ d : Fin (27 - 6 - 2), Fin (27 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨6, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  exact ⟨519, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c07 (q : Σ d : Fin (27 - 7 - 2), Fin (27 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨7, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c08 (q : Σ d : Fin (27 - 8 - 2), Fin (27 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨8, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c09 (q : Σ d : Fin (27 - 9 - 2), Fin (27 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨9, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11791, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c10 (q : Σ d : Fin (27 - 10 - 2), Fin (27 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨10, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  exact ⟨7577, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c11 (q : Σ d : Fin (27 - 11 - 2), Fin (27 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨11, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  exact ⟨5275, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c12 (q : Σ d : Fin (27 - 12 - 2), Fin (27 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨12, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c13 (q : Σ d : Fin (27 - 13 - 2), Fin (27 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨13, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  exact ⟨5635, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c14 (q : Σ d : Fin (27 - 14 - 2), Fin (27 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨14, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6404, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c15 (q : Σ d : Fin (27 - 15 - 2), Fin (27 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨15, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12931, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c16 (q : Σ d : Fin (27 - 16 - 2), Fin (27 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨16, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  exact ⟨6403, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c17 (q : Σ d : Fin (27 - 17 - 2), Fin (27 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨17, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · fin_cases e
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨441, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨2705, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6499, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c18 (q : Σ d : Fin (27 - 18 - 2), Fin (27 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨18, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c19 (q : Σ d : Fin (27 - 19 - 2), Fin (27 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨19, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c20 (q : Σ d : Fin (27 - 20 - 2), Fin (27 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨20, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c21 (q : Σ d : Fin (27 - 21 - 2), Fin (27 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨21, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c22 (q : Σ d : Fin (27 - 22 - 2), Fin (27 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨22, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c23 (q : Σ d : Fin (27 - 23 - 2), Fin (27 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨23, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  exact ⟨7936, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b32_c24 (q : Σ d : Fin (27 - 24 - 2), Fin (27 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 ⟨(⟨24, by norm_num⟩ : Fin (27 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a04_b32 (q : IncreasingThree 27) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 39 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a04_b32_c00 q
  · exact certificate67_a04_b32_c01 q
  · exact certificate67_a04_b32_c02 q
  · exact certificate67_a04_b32_c03 q
  · exact certificate67_a04_b32_c04 q
  · exact certificate67_a04_b32_c05 q
  · exact certificate67_a04_b32_c06 q
  · exact certificate67_a04_b32_c07 q
  · exact certificate67_a04_b32_c08 q
  · exact certificate67_a04_b32_c09 q
  · exact certificate67_a04_b32_c10 q
  · exact certificate67_a04_b32_c11 q
  · exact certificate67_a04_b32_c12 q
  · exact certificate67_a04_b32_c13 q
  · exact certificate67_a04_b32_c14 q
  · exact certificate67_a04_b32_c15 q
  · exact certificate67_a04_b32_c16 q
  · exact certificate67_a04_b32_c17 q
  · exact certificate67_a04_b32_c18 q
  · exact certificate67_a04_b32_c19 q
  · exact certificate67_a04_b32_c20 q
  · exact certificate67_a04_b32_c21 q
  · exact certificate67_a04_b32_c22 q
  · exact certificate67_a04_b32_c23 q
  · exact certificate67_a04_b32_c24 q

end MinModulus.SHCSixCertificate.Generated
