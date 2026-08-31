import MinModulus.Generated.SHCSixN105A29B21

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a30_b01_c00 (q : Σ d : Fin (22 - 0 - 2), Fin (22 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1029, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11395, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨177, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2689, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨2074, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5636, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6499, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6883, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c01 (q : Σ d : Fin (22 - 1 - 2), Fin (22 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c02 (q : Σ d : Fin (22 - 2 - 2), Fin (22 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨7577, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c03 (q : Σ d : Fin (22 - 3 - 2), Fin (22 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨177, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2074, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5636, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2433, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨945, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5300, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c04 (q : Σ d : Fin (22 - 4 - 2), Fin (22 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨7944, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c05 (q : Σ d : Fin (22 - 5 - 2), Fin (22 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨7566, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c06 (q : Σ d : Fin (22 - 6 - 2), Fin (22 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2057, by decide, by decide⟩
    · exact ⟨177, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨693, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5636, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1039, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3457, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c07 (q : Σ d : Fin (22 - 7 - 2), Fin (22 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨169, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3465, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2189, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨185, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3086, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a30_b01_c08 (q : Σ d : Fin (22 - 8 - 2), Fin (22 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5636, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1039, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13710, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c09 (q : Σ d : Fin (22 - 9 - 2), Fin (22 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨4867, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c10 (q : Σ d : Fin (22 - 10 - 2), Fin (22 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨5635, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c11 (q : Σ d : Fin (22 - 11 - 2), Fin (22 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13710, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13326, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c12 (q : Σ d : Fin (22 - 12 - 2), Fin (22 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨15, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c13 (q : Σ d : Fin (22 - 13 - 2), Fin (22 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨14, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c14 (q : Σ d : Fin (22 - 14 - 2), Fin (22 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7964, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c15 (q : Σ d : Fin (22 - 15 - 2), Fin (22 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨897, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c16 (q : Σ d : Fin (22 - 16 - 2), Fin (22 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c17 (q : Σ d : Fin (22 - 17 - 2), Fin (22 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c18 (q : Σ d : Fin (22 - 18 - 2), Fin (22 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a30_b01_c19 (q : Σ d : Fin (22 - 19 - 2), Fin (22 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a30_b01 (q : IncreasingThree 22) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨30, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a30_b01_c00 q
  · exact certificate105_a30_b01_c01 q
  · exact certificate105_a30_b01_c02 q
  · exact certificate105_a30_b01_c03 q
  · exact certificate105_a30_b01_c04 q
  · exact certificate105_a30_b01_c05 q
  · exact certificate105_a30_b01_c06 q
  · exact certificate105_a30_b01_c07 q
  · exact certificate105_a30_b01_c08 q
  · exact certificate105_a30_b01_c09 q
  · exact certificate105_a30_b01_c10 q
  · exact certificate105_a30_b01_c11 q
  · exact certificate105_a30_b01_c12 q
  · exact certificate105_a30_b01_c13 q
  · exact certificate105_a30_b01_c14 q
  · exact certificate105_a30_b01_c15 q
  · exact certificate105_a30_b01_c16 q
  · exact certificate105_a30_b01_c17 q
  · exact certificate105_a30_b01_c18 q
  · exact certificate105_a30_b01_c19 q

end MinModulus.SHCSixExceptionalCertificate.Generated
