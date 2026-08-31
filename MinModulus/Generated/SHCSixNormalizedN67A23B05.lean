import MinModulus.Generated.SHCSixNormalizedN67A23B03

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a23_b05_c00 (q : Σ d : Fin (35 - 0 - 2), Fin (35 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨0, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c01 (q : Σ d : Fin (35 - 1 - 2), Fin (35 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨1, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c02 (q : Σ d : Fin (35 - 2 - 2), Fin (35 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨2, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨4483, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c03 (q : Σ d : Fin (35 - 3 - 2), Fin (35 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨3, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨13, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c04 (q : Σ d : Fin (35 - 4 - 2), Fin (35 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨4, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨12, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c05 (q : Σ d : Fin (35 - 5 - 2), Fin (35 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨5, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨769, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c06 (q : Σ d : Fin (35 - 6 - 2), Fin (35 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨6, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨8704, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c07 (q : Σ d : Fin (35 - 7 - 2), Fin (35 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨7, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14855, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c08 (q : Σ d : Fin (35 - 8 - 2), Fin (35 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨8, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c09 (q : Σ d : Fin (35 - 9 - 2), Fin (35 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨9, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c10 (q : Σ d : Fin (35 - 10 - 2), Fin (35 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨10, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c11 (q : Σ d : Fin (35 - 11 - 2), Fin (35 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨11, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c12 (q : Σ d : Fin (35 - 12 - 2), Fin (35 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨12, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨7936, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c13 (q : Σ d : Fin (35 - 13 - 2), Fin (35 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨13, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c14 (q : Σ d : Fin (35 - 14 - 2), Fin (35 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨14, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨4867, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c15 (q : Σ d : Fin (35 - 15 - 2), Fin (35 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨15, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c16 (q : Σ d : Fin (35 - 16 - 2), Fin (35 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨16, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨5347, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11779, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c17 (q : Σ d : Fin (35 - 17 - 2), Fin (35 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨17, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨6065, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c18 (q : Σ d : Fin (35 - 18 - 2), Fin (35 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨18, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨7169, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c19 (q : Σ d : Fin (35 - 19 - 2), Fin (35 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨19, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12592, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c20 (q : Σ d : Fin (35 - 20 - 2), Fin (35 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨20, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12592, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c21 (q : Σ d : Fin (35 - 21 - 2), Fin (35 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨21, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c22 (q : Σ d : Fin (35 - 22 - 2), Fin (35 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨22, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨6448, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c23 (q : Σ d : Fin (35 - 23 - 2), Fin (35 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨23, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c24 (q : Σ d : Fin (35 - 24 - 2), Fin (35 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨24, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c25 (q : Σ d : Fin (35 - 25 - 2), Fin (35 - (25 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨25, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨519, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c26 (q : Σ d : Fin (35 - 26 - 2), Fin (35 - (26 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨26, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c27 (q : Σ d : Fin (35 - 27 - 2), Fin (35 - (27 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨27, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c28 (q : Σ d : Fin (35 - 28 - 2), Fin (35 - (28 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨28, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c29 (q : Σ d : Fin (35 - 29 - 2), Fin (35 - (29 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨29, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c30 (q : Σ d : Fin (35 - 30 - 2), Fin (35 - (30 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨30, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c31 (q : Σ d : Fin (35 - 31 - 2), Fin (35 - (31 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨31, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a23_b05_c32 (q : Σ d : Fin (35 - 32 - 2), Fin (35 - (32 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 ⟨(⟨32, by norm_num⟩ : Fin (35 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a23_b05 (q : IncreasingThree 35) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 25 31 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a23_b05_c00 q
  · exact certificate67_a23_b05_c01 q
  · exact certificate67_a23_b05_c02 q
  · exact certificate67_a23_b05_c03 q
  · exact certificate67_a23_b05_c04 q
  · exact certificate67_a23_b05_c05 q
  · exact certificate67_a23_b05_c06 q
  · exact certificate67_a23_b05_c07 q
  · exact certificate67_a23_b05_c08 q
  · exact certificate67_a23_b05_c09 q
  · exact certificate67_a23_b05_c10 q
  · exact certificate67_a23_b05_c11 q
  · exact certificate67_a23_b05_c12 q
  · exact certificate67_a23_b05_c13 q
  · exact certificate67_a23_b05_c14 q
  · exact certificate67_a23_b05_c15 q
  · exact certificate67_a23_b05_c16 q
  · exact certificate67_a23_b05_c17 q
  · exact certificate67_a23_b05_c18 q
  · exact certificate67_a23_b05_c19 q
  · exact certificate67_a23_b05_c20 q
  · exact certificate67_a23_b05_c21 q
  · exact certificate67_a23_b05_c22 q
  · exact certificate67_a23_b05_c23 q
  · exact certificate67_a23_b05_c24 q
  · exact certificate67_a23_b05_c25 q
  · exact certificate67_a23_b05_c26 q
  · exact certificate67_a23_b05_c27 q
  · exact certificate67_a23_b05_c28 q
  · exact certificate67_a23_b05_c29 q
  · exact certificate67_a23_b05_c30 q
  · exact certificate67_a23_b05_c31 q
  · exact certificate67_a23_b05_c32 q

end MinModulus.SHCSixCertificate.Generated
