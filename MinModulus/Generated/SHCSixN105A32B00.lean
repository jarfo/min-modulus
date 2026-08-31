import MinModulus.Generated.SHCSixN105A31B18

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a32_b00_c00 (q : Σ d : Fin (21 - 0 - 2), Fin (21 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  exact ⟨515, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c01 (q : Σ d : Fin (21 - 1 - 2), Fin (21 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1291, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨42, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨441, by decide, by decide⟩
    · exact ⟨2433, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨169, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨441, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2433, by decide, by decide⟩
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨3339, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨3457, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10639, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1039, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c02 (q : Σ d : Fin (21 - 2 - 2), Fin (21 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  exact ⟨7944, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c03 (q : Σ d : Fin (21 - 3 - 2), Fin (21 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨2433, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨3075, by decide, by decide⟩
    · exact ⟨2961, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11017, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2201, by decide, by decide⟩
    · exact ⟨54, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c04 (q : Σ d : Fin (21 - 4 - 2), Fin (21 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨177, by decide, by decide⟩
    · exact ⟨2433, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨169, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨11395, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11011, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c05 (q : Σ d : Fin (21 - 5 - 2), Fin (21 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1291, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨177, by decide, by decide⟩
    · exact ⟨2433, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨693, by decide, by decide⟩
    · exact ⟨2201, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨693, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨54, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c06 (q : Σ d : Fin (21 - 6 - 2), Fin (21 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14855, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5300, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c07 (q : Σ d : Fin (21 - 7 - 2), Fin (21 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1291, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6068, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c08 (q : Σ d : Fin (21 - 8 - 2), Fin (21 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14082, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11395, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c09 (q : Σ d : Fin (21 - 9 - 2), Fin (21 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  exact ⟨4867, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c10 (q : Σ d : Fin (21 - 10 - 2), Fin (21 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  exact ⟨897, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c11 (q : Σ d : Fin (21 - 11 - 2), Fin (21 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨54, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨46, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2078, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨46, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨7964, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3213, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨46, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c12 (q : Σ d : Fin (21 - 12 - 2), Fin (21 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1291, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5347, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c13 (q : Σ d : Fin (21 - 13 - 2), Fin (21 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨46, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c14 (q : Σ d : Fin (21 - 14 - 2), Fin (21 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c15 (q : Σ d : Fin (21 - 15 - 2), Fin (21 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1291, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7964, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c16 (q : Σ d : Fin (21 - 16 - 2), Fin (21 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c17 (q : Σ d : Fin (21 - 17 - 2), Fin (21 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1291, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a32_b00_c18 (q : Σ d : Fin (21 - 18 - 2), Fin (21 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (21 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a32_b00 (q : IncreasingThree 21) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨32, by norm_num⟩ : Fin 55) (⟨33, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a32_b00_c00 q
  · exact certificate105_a32_b00_c01 q
  · exact certificate105_a32_b00_c02 q
  · exact certificate105_a32_b00_c03 q
  · exact certificate105_a32_b00_c04 q
  · exact certificate105_a32_b00_c05 q
  · exact certificate105_a32_b00_c06 q
  · exact certificate105_a32_b00_c07 q
  · exact certificate105_a32_b00_c08 q
  · exact certificate105_a32_b00_c09 q
  · exact certificate105_a32_b00_c10 q
  · exact certificate105_a32_b00_c11 q
  · exact certificate105_a32_b00_c12 q
  · exact certificate105_a32_b00_c13 q
  · exact certificate105_a32_b00_c14 q
  · exact certificate105_a32_b00_c15 q
  · exact certificate105_a32_b00_c16 q
  · exact certificate105_a32_b00_c17 q
  · exact certificate105_a32_b00_c18 q

end MinModulus.SHCSixExceptionalCertificate.Generated
