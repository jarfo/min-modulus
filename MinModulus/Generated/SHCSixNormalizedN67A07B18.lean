import MinModulus.Generated.SHCSixNormalizedN67A07B16

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a07_b18_c00 (q : Σ d : Fin (38 - 0 - 2), Fin (38 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨0, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c01 (q : Σ d : Fin (38 - 1 - 2), Fin (38 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨1, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨14, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c02 (q : Σ d : Fin (38 - 2 - 2), Fin (38 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨2, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨897, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c03 (q : Σ d : Fin (38 - 3 - 2), Fin (38 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨3, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨9472, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c04 (q : Σ d : Fin (38 - 4 - 2), Fin (38 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨4, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c05 (q : Σ d : Fin (38 - 5 - 2), Fin (38 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨5, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨4483, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c06 (q : Σ d : Fin (38 - 6 - 2), Fin (38 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨6, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨6448, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c07 (q : Σ d : Fin (38 - 7 - 2), Fin (38 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨7, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c08 (q : Σ d : Fin (38 - 8 - 2), Fin (38 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨8, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c09 (q : Σ d : Fin (38 - 9 - 2), Fin (38 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨9, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨13, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c10 (q : Σ d : Fin (38 - 10 - 2), Fin (38 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨10, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨12, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c11 (q : Σ d : Fin (38 - 11 - 2), Fin (38 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨11, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨769, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c12 (q : Σ d : Fin (38 - 12 - 2), Fin (38 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨12, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨8704, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c13 (q : Σ d : Fin (38 - 13 - 2), Fin (38 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨13, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c14 (q : Σ d : Fin (38 - 14 - 2), Fin (38 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨14, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c15 (q : Σ d : Fin (38 - 15 - 2), Fin (38 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨15, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨8418, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c16 (q : Σ d : Fin (38 - 16 - 2), Fin (38 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨16, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨7577, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c17 (q : Σ d : Fin (38 - 17 - 2), Fin (38 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨17, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨8322, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c18 (q : Σ d : Fin (38 - 18 - 2), Fin (38 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨18, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c19 (q : Σ d : Fin (38 - 19 - 2), Fin (38 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨19, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c20 (q : Σ d : Fin (38 - 20 - 2), Fin (38 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨20, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c21 (q : Σ d : Fin (38 - 21 - 2), Fin (38 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨21, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c22 (q : Σ d : Fin (38 - 22 - 2), Fin (38 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨22, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨9185, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c23 (q : Σ d : Fin (38 - 23 - 2), Fin (38 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨23, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨6403, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c24 (q : Σ d : Fin (38 - 24 - 2), Fin (38 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨24, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c25 (q : Σ d : Fin (38 - 25 - 2), Fin (38 - (25 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨25, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨9185, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c26 (q : Σ d : Fin (38 - 26 - 2), Fin (38 - (26 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨26, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨7554, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c27 (q : Σ d : Fin (38 - 27 - 2), Fin (38 - (27 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨27, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨9089, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c28 (q : Σ d : Fin (38 - 28 - 2), Fin (38 - (28 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨28, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c29 (q : Σ d : Fin (38 - 29 - 2), Fin (38 - (29 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨29, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c30 (q : Σ d : Fin (38 - 30 - 2), Fin (38 - (30 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨30, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c31 (q : Σ d : Fin (38 - 31 - 2), Fin (38 - (31 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨31, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨7936, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c32 (q : Σ d : Fin (38 - 32 - 2), Fin (38 - (32 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨32, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c33 (q : Σ d : Fin (38 - 33 - 2), Fin (38 - (33 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨33, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c34 (q : Σ d : Fin (38 - 34 - 2), Fin (38 - (34 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨34, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b18_c35 (q : Σ d : Fin (38 - 35 - 2), Fin (38 - (35 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 ⟨(⟨35, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨7566, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a07_b18 (q : IncreasingThree 38) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 28 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a07_b18_c00 q
  · exact certificate67_a07_b18_c01 q
  · exact certificate67_a07_b18_c02 q
  · exact certificate67_a07_b18_c03 q
  · exact certificate67_a07_b18_c04 q
  · exact certificate67_a07_b18_c05 q
  · exact certificate67_a07_b18_c06 q
  · exact certificate67_a07_b18_c07 q
  · exact certificate67_a07_b18_c08 q
  · exact certificate67_a07_b18_c09 q
  · exact certificate67_a07_b18_c10 q
  · exact certificate67_a07_b18_c11 q
  · exact certificate67_a07_b18_c12 q
  · exact certificate67_a07_b18_c13 q
  · exact certificate67_a07_b18_c14 q
  · exact certificate67_a07_b18_c15 q
  · exact certificate67_a07_b18_c16 q
  · exact certificate67_a07_b18_c17 q
  · exact certificate67_a07_b18_c18 q
  · exact certificate67_a07_b18_c19 q
  · exact certificate67_a07_b18_c20 q
  · exact certificate67_a07_b18_c21 q
  · exact certificate67_a07_b18_c22 q
  · exact certificate67_a07_b18_c23 q
  · exact certificate67_a07_b18_c24 q
  · exact certificate67_a07_b18_c25 q
  · exact certificate67_a07_b18_c26 q
  · exact certificate67_a07_b18_c27 q
  · exact certificate67_a07_b18_c28 q
  · exact certificate67_a07_b18_c29 q
  · exact certificate67_a07_b18_c30 q
  · exact certificate67_a07_b18_c31 q
  · exact certificate67_a07_b18_c32 q
  · exact certificate67_a07_b18_c33 q
  · exact certificate67_a07_b18_c34 q
  · exact certificate67_a07_b18_c35 q

end MinModulus.SHCSixCertificate.Generated
