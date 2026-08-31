import MinModulus.Generated.SHCSixNormalizedN67A07B28

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a07_b30_c00 (q : Σ d : Fin (26 - 0 - 2), Fin (26 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨0, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c01 (q : Σ d : Fin (26 - 1 - 2), Fin (26 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨1, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11783, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c02 (q : Σ d : Fin (26 - 2 - 2), Fin (26 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨2, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11777, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11783, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c03 (q : Σ d : Fin (26 - 3 - 2), Fin (26 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨3, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  exact ⟨9089, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c04 (q : Σ d : Fin (26 - 4 - 2), Fin (26 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨4, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  exact ⟨8705, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c05 (q : Σ d : Fin (26 - 5 - 2), Fin (26 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨5, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  exact ⟨8711, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c06 (q : Σ d : Fin (26 - 6 - 2), Fin (26 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨6, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  exact ⟨6448, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c07 (q : Σ d : Fin (26 - 7 - 2), Fin (26 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨7, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c08 (q : Σ d : Fin (26 - 8 - 2), Fin (26 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨8, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c09 (q : Σ d : Fin (26 - 9 - 2), Fin (26 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨9, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  exact ⟨519, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c10 (q : Σ d : Fin (26 - 10 - 2), Fin (26 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨10, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14855, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c11 (q : Σ d : Fin (26 - 11 - 2), Fin (26 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨11, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  exact ⟨5275, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c12 (q : Σ d : Fin (26 - 12 - 2), Fin (26 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨12, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c13 (q : Σ d : Fin (26 - 13 - 2), Fin (26 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨13, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  exact ⟨6019, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c14 (q : Σ d : Fin (26 - 14 - 2), Fin (26 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨14, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c15 (q : Σ d : Fin (26 - 15 - 2), Fin (26 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨15, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12931, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c16 (q : Σ d : Fin (26 - 16 - 2), Fin (26 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨16, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c17 (q : Σ d : Fin (26 - 17 - 2), Fin (26 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨17, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c18 (q : Σ d : Fin (26 - 18 - 2), Fin (26 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨18, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c19 (q : Σ d : Fin (26 - 19 - 2), Fin (26 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨19, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  exact ⟨7936, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c20 (q : Σ d : Fin (26 - 20 - 2), Fin (26 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨20, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c21 (q : Σ d : Fin (26 - 21 - 2), Fin (26 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨21, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c22 (q : Σ d : Fin (26 - 22 - 2), Fin (26 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨22, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a07_b30_c23 (q : Σ d : Fin (26 - 23 - 2), Fin (26 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 ⟨(⟨23, by norm_num⟩ : Fin (26 - 2)), q⟩) code = true := by
  exact ⟨5298, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a07_b30 (q : IncreasingThree 26) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 9 40 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a07_b30_c00 q
  · exact certificate67_a07_b30_c01 q
  · exact certificate67_a07_b30_c02 q
  · exact certificate67_a07_b30_c03 q
  · exact certificate67_a07_b30_c04 q
  · exact certificate67_a07_b30_c05 q
  · exact certificate67_a07_b30_c06 q
  · exact certificate67_a07_b30_c07 q
  · exact certificate67_a07_b30_c08 q
  · exact certificate67_a07_b30_c09 q
  · exact certificate67_a07_b30_c10 q
  · exact certificate67_a07_b30_c11 q
  · exact certificate67_a07_b30_c12 q
  · exact certificate67_a07_b30_c13 q
  · exact certificate67_a07_b30_c14 q
  · exact certificate67_a07_b30_c15 q
  · exact certificate67_a07_b30_c16 q
  · exact certificate67_a07_b30_c17 q
  · exact certificate67_a07_b30_c18 q
  · exact certificate67_a07_b30_c19 q
  · exact certificate67_a07_b30_c20 q
  · exact certificate67_a07_b30_c21 q
  · exact certificate67_a07_b30_c22 q
  · exact certificate67_a07_b30_c23 q

end MinModulus.SHCSixCertificate.Generated
