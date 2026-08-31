import MinModulus.Generated.SHCSixNormalizedN67A17B08

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a17_b10_c00 (q : Σ d : Fin (36 - 0 - 2), Fin (36 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨0, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c01 (q : Σ d : Fin (36 - 1 - 2), Fin (36 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨1, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨25, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11825, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨8418, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨8800, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c02 (q : Σ d : Fin (36 - 2 - 2), Fin (36 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨2, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨8800, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c03 (q : Σ d : Fin (36 - 3 - 2), Fin (36 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨3, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨4483, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c04 (q : Σ d : Fin (36 - 4 - 2), Fin (36 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨4, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14855, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c05 (q : Σ d : Fin (36 - 5 - 2), Fin (36 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨5, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨13, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c06 (q : Σ d : Fin (36 - 6 - 2), Fin (36 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨6, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨12, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c07 (q : Σ d : Fin (36 - 7 - 2), Fin (36 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨7, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨769, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c08 (q : Σ d : Fin (36 - 8 - 2), Fin (36 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨8, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨8704, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c09 (q : Σ d : Fin (36 - 9 - 2), Fin (36 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨9, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨8322, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c10 (q : Σ d : Fin (36 - 10 - 2), Fin (36 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨10, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨7938, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c11 (q : Σ d : Fin (36 - 11 - 2), Fin (36 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨11, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨7944, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c12 (q : Σ d : Fin (36 - 12 - 2), Fin (36 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨12, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨4867, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c13 (q : Σ d : Fin (36 - 13 - 2), Fin (36 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨13, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨9482, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c14 (q : Σ d : Fin (36 - 14 - 2), Fin (36 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨14, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c15 (q : Σ d : Fin (36 - 15 - 2), Fin (36 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨15, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11825, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14466, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14082, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c16 (q : Σ d : Fin (36 - 16 - 2), Fin (36 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨16, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c17 (q : Σ d : Fin (36 - 17 - 2), Fin (36 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨17, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c18 (q : Σ d : Fin (36 - 18 - 2), Fin (36 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨18, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c19 (q : Σ d : Fin (36 - 19 - 2), Fin (36 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨19, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨519, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c20 (q : Σ d : Fin (36 - 20 - 2), Fin (36 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨20, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11825, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c21 (q : Σ d : Fin (36 - 21 - 2), Fin (36 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨21, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c22 (q : Σ d : Fin (36 - 22 - 2), Fin (36 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨22, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c23 (q : Σ d : Fin (36 - 23 - 2), Fin (36 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨23, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c24 (q : Σ d : Fin (36 - 24 - 2), Fin (36 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨24, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c25 (q : Σ d : Fin (36 - 25 - 2), Fin (36 - (25 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨25, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c26 (q : Σ d : Fin (36 - 26 - 2), Fin (36 - (26 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨26, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c27 (q : Σ d : Fin (36 - 27 - 2), Fin (36 - (27 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨27, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c28 (q : Σ d : Fin (36 - 28 - 2), Fin (36 - (28 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨28, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨7554, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c29 (q : Σ d : Fin (36 - 29 - 2), Fin (36 - (29 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨29, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨6065, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c30 (q : Σ d : Fin (36 - 30 - 2), Fin (36 - (30 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨30, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13698, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c31 (q : Σ d : Fin (36 - 31 - 2), Fin (36 - (31 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨31, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  exact ⟨5275, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c32 (q : Σ d : Fin (36 - 32 - 2), Fin (36 - (32 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨32, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13320, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a17_b10_c33 (q : Σ d : Fin (36 - 33 - 2), Fin (36 - (33 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 ⟨(⟨33, by norm_num⟩ : Fin (36 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a17_b10 (q : IncreasingThree 36) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 19 30 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a17_b10_c00 q
  · exact certificate67_a17_b10_c01 q
  · exact certificate67_a17_b10_c02 q
  · exact certificate67_a17_b10_c03 q
  · exact certificate67_a17_b10_c04 q
  · exact certificate67_a17_b10_c05 q
  · exact certificate67_a17_b10_c06 q
  · exact certificate67_a17_b10_c07 q
  · exact certificate67_a17_b10_c08 q
  · exact certificate67_a17_b10_c09 q
  · exact certificate67_a17_b10_c10 q
  · exact certificate67_a17_b10_c11 q
  · exact certificate67_a17_b10_c12 q
  · exact certificate67_a17_b10_c13 q
  · exact certificate67_a17_b10_c14 q
  · exact certificate67_a17_b10_c15 q
  · exact certificate67_a17_b10_c16 q
  · exact certificate67_a17_b10_c17 q
  · exact certificate67_a17_b10_c18 q
  · exact certificate67_a17_b10_c19 q
  · exact certificate67_a17_b10_c20 q
  · exact certificate67_a17_b10_c21 q
  · exact certificate67_a17_b10_c22 q
  · exact certificate67_a17_b10_c23 q
  · exact certificate67_a17_b10_c24 q
  · exact certificate67_a17_b10_c25 q
  · exact certificate67_a17_b10_c26 q
  · exact certificate67_a17_b10_c27 q
  · exact certificate67_a17_b10_c28 q
  · exact certificate67_a17_b10_c29 q
  · exact certificate67_a17_b10_c30 q
  · exact certificate67_a17_b10_c31 q
  · exact certificate67_a17_b10_c32 q
  · exact certificate67_a17_b10_c33 q

end MinModulus.SHCSixCertificate.Generated
