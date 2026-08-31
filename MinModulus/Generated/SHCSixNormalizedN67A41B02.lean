import MinModulus.Generated.SHCSixNormalizedN67A41B00

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a41_b02_c00 (q : Σ d : Fin (20 - 0 - 2), Fin (20 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨0, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c01 (q : Σ d : Fin (20 - 1 - 2), Fin (20 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨1, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨8322, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c02 (q : Σ d : Fin (20 - 2 - 2), Fin (20 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨2, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨7938, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c03 (q : Σ d : Fin (20 - 3 - 2), Fin (20 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨3, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨7944, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c04 (q : Σ d : Fin (20 - 4 - 2), Fin (20 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨4, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14855, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c05 (q : Σ d : Fin (20 - 5 - 2), Fin (20 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨5, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c06 (q : Σ d : Fin (20 - 6 - 2), Fin (20 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨6, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c07 (q : Σ d : Fin (20 - 7 - 2), Fin (20 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨7, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14082, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c08 (q : Σ d : Fin (20 - 8 - 2), Fin (20 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨8, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨4867, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c09 (q : Σ d : Fin (20 - 9 - 2), Fin (20 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨9, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c10 (q : Σ d : Fin (20 - 10 - 2), Fin (20 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨10, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨6019, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c11 (q : Σ d : Fin (20 - 11 - 2), Fin (20 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨11, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c12 (q : Σ d : Fin (20 - 12 - 2), Fin (20 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨12, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c13 (q : Σ d : Fin (20 - 13 - 2), Fin (20 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨13, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c14 (q : Σ d : Fin (20 - 14 - 2), Fin (20 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨14, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c15 (q : Σ d : Fin (20 - 15 - 2), Fin (20 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨15, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c16 (q : Σ d : Fin (20 - 16 - 2), Fin (20 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨16, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a41_b02_c17 (q : Σ d : Fin (20 - 17 - 2), Fin (20 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 ⟨(⟨17, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a41_b02 (q : IncreasingThree 20) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 43 46 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a41_b02_c00 q
  · exact certificate67_a41_b02_c01 q
  · exact certificate67_a41_b02_c02 q
  · exact certificate67_a41_b02_c03 q
  · exact certificate67_a41_b02_c04 q
  · exact certificate67_a41_b02_c05 q
  · exact certificate67_a41_b02_c06 q
  · exact certificate67_a41_b02_c07 q
  · exact certificate67_a41_b02_c08 q
  · exact certificate67_a41_b02_c09 q
  · exact certificate67_a41_b02_c10 q
  · exact certificate67_a41_b02_c11 q
  · exact certificate67_a41_b02_c12 q
  · exact certificate67_a41_b02_c13 q
  · exact certificate67_a41_b02_c14 q
  · exact certificate67_a41_b02_c15 q
  · exact certificate67_a41_b02_c16 q
  · exact certificate67_a41_b02_c17 q

end MinModulus.SHCSixCertificate.Generated
