import MinModulus.Generated.SHCSixNormalizedN67A09B11

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a09_b13_c00 (q : Σ d : Fin (41 - 0 - 2), Fin (41 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨0, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c01 (q : Σ d : Fin (41 - 1 - 2), Fin (41 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨1, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨5275, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c02 (q : Σ d : Fin (41 - 2 - 2), Fin (41 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨2, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11011, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6499, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6883, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12592, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c03 (q : Σ d : Fin (41 - 3 - 2), Fin (41 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨3, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨5298, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c04 (q : Σ d : Fin (41 - 4 - 2), Fin (41 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨4, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨15, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c05 (q : Σ d : Fin (41 - 5 - 2), Fin (41 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨5, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨14, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c06 (q : Σ d : Fin (41 - 6 - 2), Fin (41 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨6, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨897, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c07 (q : Σ d : Fin (41 - 7 - 2), Fin (41 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨7, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨9472, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c08 (q : Σ d : Fin (41 - 8 - 2), Fin (41 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨8, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨6448, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c09 (q : Σ d : Fin (41 - 9 - 2), Fin (41 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨9, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c10 (q : Σ d : Fin (41 - 10 - 2), Fin (41 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨10, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c11 (q : Σ d : Fin (41 - 11 - 2), Fin (41 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨11, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨519, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c12 (q : Σ d : Fin (41 - 12 - 2), Fin (41 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨12, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨8322, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c13 (q : Σ d : Fin (41 - 13 - 2), Fin (41 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨13, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨7938, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c14 (q : Σ d : Fin (41 - 14 - 2), Fin (41 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨14, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨7944, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c15 (q : Σ d : Fin (41 - 15 - 2), Fin (41 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨15, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨13, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c16 (q : Σ d : Fin (41 - 16 - 2), Fin (41 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨16, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨12, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c17 (q : Σ d : Fin (41 - 17 - 2), Fin (41 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨17, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨769, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c18 (q : Σ d : Fin (41 - 18 - 2), Fin (41 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨18, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨8704, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c19 (q : Σ d : Fin (41 - 19 - 2), Fin (41 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨19, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨7568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14082, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c20 (q : Σ d : Fin (41 - 20 - 2), Fin (41 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨20, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨7577, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c21 (q : Σ d : Fin (41 - 21 - 2), Fin (41 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨21, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11783, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c22 (q : Σ d : Fin (41 - 22 - 2), Fin (41 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨22, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11777, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c23 (q : Σ d : Fin (41 - 23 - 2), Fin (41 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨23, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨7554, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c24 (q : Σ d : Fin (41 - 24 - 2), Fin (41 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨24, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨7170, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c25 (q : Σ d : Fin (41 - 25 - 2), Fin (41 - (25 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨25, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨6409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c26 (q : Σ d : Fin (41 - 26 - 2), Fin (41 - (26 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨26, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c27 (q : Σ d : Fin (41 - 27 - 2), Fin (41 - (27 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨27, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c28 (q : Σ d : Fin (41 - 28 - 2), Fin (41 - (28 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨28, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c29 (q : Σ d : Fin (41 - 29 - 2), Fin (41 - (29 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨29, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c30 (q : Σ d : Fin (41 - 30 - 2), Fin (41 - (30 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨30, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c31 (q : Σ d : Fin (41 - 31 - 2), Fin (41 - (31 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨31, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c32 (q : Σ d : Fin (41 - 32 - 2), Fin (41 - (32 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨32, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨7936, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c33 (q : Σ d : Fin (41 - 33 - 2), Fin (41 - (33 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨33, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c34 (q : Σ d : Fin (41 - 34 - 2), Fin (41 - (34 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨34, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨7566, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c35 (q : Σ d : Fin (41 - 35 - 2), Fin (41 - (35 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨35, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨9185, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c36 (q : Σ d : Fin (41 - 36 - 2), Fin (41 - (36 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨36, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11777, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨8801, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c37 (q : Σ d : Fin (41 - 37 - 2), Fin (41 - (37 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨37, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨9089, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a09_b13_c38 (q : Σ d : Fin (41 - 38 - 2), Fin (41 - (38 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 ⟨(⟨38, by norm_num⟩ : Fin (41 - 2)), q⟩) code = true := by
  exact ⟨8705, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a09_b13 (q : IncreasingThree 41) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 11 25 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a09_b13_c00 q
  · exact certificate67_a09_b13_c01 q
  · exact certificate67_a09_b13_c02 q
  · exact certificate67_a09_b13_c03 q
  · exact certificate67_a09_b13_c04 q
  · exact certificate67_a09_b13_c05 q
  · exact certificate67_a09_b13_c06 q
  · exact certificate67_a09_b13_c07 q
  · exact certificate67_a09_b13_c08 q
  · exact certificate67_a09_b13_c09 q
  · exact certificate67_a09_b13_c10 q
  · exact certificate67_a09_b13_c11 q
  · exact certificate67_a09_b13_c12 q
  · exact certificate67_a09_b13_c13 q
  · exact certificate67_a09_b13_c14 q
  · exact certificate67_a09_b13_c15 q
  · exact certificate67_a09_b13_c16 q
  · exact certificate67_a09_b13_c17 q
  · exact certificate67_a09_b13_c18 q
  · exact certificate67_a09_b13_c19 q
  · exact certificate67_a09_b13_c20 q
  · exact certificate67_a09_b13_c21 q
  · exact certificate67_a09_b13_c22 q
  · exact certificate67_a09_b13_c23 q
  · exact certificate67_a09_b13_c24 q
  · exact certificate67_a09_b13_c25 q
  · exact certificate67_a09_b13_c26 q
  · exact certificate67_a09_b13_c27 q
  · exact certificate67_a09_b13_c28 q
  · exact certificate67_a09_b13_c29 q
  · exact certificate67_a09_b13_c30 q
  · exact certificate67_a09_b13_c31 q
  · exact certificate67_a09_b13_c32 q
  · exact certificate67_a09_b13_c33 q
  · exact certificate67_a09_b13_c34 q
  · exact certificate67_a09_b13_c35 q
  · exact certificate67_a09_b13_c36 q
  · exact certificate67_a09_b13_c37 q
  · exact certificate67_a09_b13_c38 q

end MinModulus.SHCSixCertificate.Generated
