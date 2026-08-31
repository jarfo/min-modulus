import MinModulus.Generated.SHCSixN105A09B10

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a09_b12_c00 (q : Σ d : Fin (32 - 0 - 2), Fin (32 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c01 (q : Σ d : Fin (32 - 1 - 2), Fin (32 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8801, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6883, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12592, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11777, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c02 (q : Σ d : Fin (32 - 2 - 2), Fin (32 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨3073, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨169, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨1062, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨4484, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9482, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12592, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c03 (q : Σ d : Fin (32 - 3 - 2), Fin (32 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1953, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨2078, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨54, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨3457, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2449, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨8801, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨433, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨5636, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8800, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨15808, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨817, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c04 (q : Σ d : Fin (32 - 4 - 2), Fin (32 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  exact ⟨4483, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c05 (q : Σ d : Fin (32 - 5 - 2), Fin (32 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨13312, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨46, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨2078, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c06 (q : Σ d : Fin (32 - 6 - 2), Fin (32 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c07 (q : Σ d : Fin (32 - 7 - 2), Fin (32 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  exact ⟨13, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c08 (q : Σ d : Fin (32 - 8 - 2), Fin (32 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  exact ⟨12, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c09 (q : Σ d : Fin (32 - 9 - 2), Fin (32 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  exact ⟨769, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c10 (q : Σ d : Fin (32 - 10 - 2), Fin (32 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c11 (q : Σ d : Fin (32 - 11 - 2), Fin (32 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  exact ⟨8704, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c12 (q : Σ d : Fin (32 - 12 - 2), Fin (32 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10651, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5347, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11777, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c13 (q : Σ d : Fin (32 - 13 - 2), Fin (32 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  exact ⟨7938, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c14 (q : Σ d : Fin (32 - 14 - 2), Fin (32 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c15 (q : Σ d : Fin (32 - 15 - 2), Fin (32 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  exact ⟨5635, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c16 (q : Σ d : Fin (32 - 16 - 2), Fin (32 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c17 (q : Σ d : Fin (32 - 17 - 2), Fin (32 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2205, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c18 (q : Σ d : Fin (32 - 18 - 2), Fin (32 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c19 (q : Σ d : Fin (32 - 19 - 2), Fin (32 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11777, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c20 (q : Σ d : Fin (32 - 20 - 2), Fin (32 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨20, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨441, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨22576, by decide, by decide⟩
    · exact ⟨2205, by decide, by decide⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨11777, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c21 (q : Σ d : Fin (32 - 21 - 2), Fin (32 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨21, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c22 (q : Σ d : Fin (32 - 22 - 2), Fin (32 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨22, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  exact ⟨7554, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c23 (q : Σ d : Fin (32 - 23 - 2), Fin (32 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨23, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  exact ⟨7170, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c24 (q : Σ d : Fin (32 - 24 - 2), Fin (32 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨24, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  exact ⟨7936, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c25 (q : Σ d : Fin (32 - 25 - 2), Fin (32 - (25 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨25, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13698, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c26 (q : Σ d : Fin (32 - 26 - 2), Fin (32 - (26 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨26, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨8897, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨8801, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c27 (q : Σ d : Fin (32 - 27 - 2), Fin (32 - (27 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨27, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2057, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c28 (q : Σ d : Fin (32 - 28 - 2), Fin (32 - (28 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨28, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨15425, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨11777, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a09_b12_c29 (q : Σ d : Fin (32 - 29 - 2), Fin (32 - (29 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) ⟨(⟨29, by norm_num⟩ : Fin (32 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11777, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a09_b12 (q : IncreasingThree 32) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨9, by norm_num⟩ : Fin 55) (⟨22, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a09_b12_c00 q
  · exact certificate105_a09_b12_c01 q
  · exact certificate105_a09_b12_c02 q
  · exact certificate105_a09_b12_c03 q
  · exact certificate105_a09_b12_c04 q
  · exact certificate105_a09_b12_c05 q
  · exact certificate105_a09_b12_c06 q
  · exact certificate105_a09_b12_c07 q
  · exact certificate105_a09_b12_c08 q
  · exact certificate105_a09_b12_c09 q
  · exact certificate105_a09_b12_c10 q
  · exact certificate105_a09_b12_c11 q
  · exact certificate105_a09_b12_c12 q
  · exact certificate105_a09_b12_c13 q
  · exact certificate105_a09_b12_c14 q
  · exact certificate105_a09_b12_c15 q
  · exact certificate105_a09_b12_c16 q
  · exact certificate105_a09_b12_c17 q
  · exact certificate105_a09_b12_c18 q
  · exact certificate105_a09_b12_c19 q
  · exact certificate105_a09_b12_c20 q
  · exact certificate105_a09_b12_c21 q
  · exact certificate105_a09_b12_c22 q
  · exact certificate105_a09_b12_c23 q
  · exact certificate105_a09_b12_c24 q
  · exact certificate105_a09_b12_c25 q
  · exact certificate105_a09_b12_c26 q
  · exact certificate105_a09_b12_c27 q
  · exact certificate105_a09_b12_c28 q
  · exact certificate105_a09_b12_c29 q

end MinModulus.SHCSixExceptionalCertificate.Generated
