import MinModulus.Generated.SHCSixN105A11B07

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a11_b09_c00 (q : Σ d : Fin (33 - 0 - 2), Fin (33 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c01 (q : Σ d : Fin (33 - 1 - 2), Fin (33 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  exact ⟨7169, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c02 (q : Σ d : Fin (33 - 2 - 2), Fin (33 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨3589, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2078, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3086, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨169, by decide, by decide⟩
    · exact ⟨2201, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2705, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨46, by decide, by decide⟩
    · exact ⟨1569, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨3073, by decide, by decide⟩
    · exact ⟨37, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨169, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1062, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨46, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨4484, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11825, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14855, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨169, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨46, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3085, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a11_b09_c03 (q : Σ d : Fin (33 - 3 - 2), Fin (33 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨3073, by decide, by decide⟩
    · exact ⟨37, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3086, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1062, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2061, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1569, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨4484, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11825, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2061, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1069, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨2061, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨566, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨8418, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨62, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c04 (q : Σ d : Fin (33 - 4 - 2), Fin (33 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨565, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨37, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨2069, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨37, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨177, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨1062, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨53, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨53, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨53, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨566, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a11_b09_c05 (q : Σ d : Fin (33 - 5 - 2), Fin (33 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  exact ⟨4483, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c06 (q : Σ d : Fin (33 - 6 - 2), Fin (33 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨13312, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1069, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2061, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1069, by decide, by decide⟩
    · exact ⟨185, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨2061, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨62, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2061, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨566, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c07 (q : Σ d : Fin (33 - 7 - 2), Fin (33 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨1069, by decide, by decide⟩
    · exact ⟨169, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2705, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨2201, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3589, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c08 (q : Σ d : Fin (33 - 8 - 2), Fin (33 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  exact ⟨8322, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c09 (q : Σ d : Fin (33 - 9 - 2), Fin (33 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  exact ⟨13, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c10 (q : Σ d : Fin (33 - 10 - 2), Fin (33 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  exact ⟨12, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c11 (q : Σ d : Fin (33 - 11 - 2), Fin (33 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨45, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2705, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6068, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨45, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c12 (q : Σ d : Fin (33 - 12 - 2), Fin (33 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c13 (q : Σ d : Fin (33 - 13 - 2), Fin (33 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  exact ⟨519, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c14 (q : Σ d : Fin (33 - 14 - 2), Fin (33 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨45, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a11_b09_c15 (q : Σ d : Fin (33 - 15 - 2), Fin (33 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨53, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨3589, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨689, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a11_b09_c16 (q : Σ d : Fin (33 - 16 - 2), Fin (33 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  exact ⟨6019, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c17 (q : Σ d : Fin (33 - 17 - 2), Fin (33 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14466, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨8720, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c18 (q : Σ d : Fin (33 - 18 - 2), Fin (33 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c19 (q : Σ d : Fin (33 - 19 - 2), Fin (33 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a11_b09_c20 (q : Σ d : Fin (33 - 20 - 2), Fin (33 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨20, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c21 (q : Σ d : Fin (33 - 21 - 2), Fin (33 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨21, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c22 (q : Σ d : Fin (33 - 22 - 2), Fin (33 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨22, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11825, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2074, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1697, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c23 (q : Σ d : Fin (33 - 23 - 2), Fin (33 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨23, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c24 (q : Σ d : Fin (33 - 24 - 2), Fin (33 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨24, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c25 (q : Σ d : Fin (33 - 25 - 2), Fin (33 - (25 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨25, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2689, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a11_b09_c26 (q : Σ d : Fin (33 - 26 - 2), Fin (33 - (26 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨26, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c27 (q : Σ d : Fin (33 - 27 - 2), Fin (33 - (27 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨27, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2057, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c28 (q : Σ d : Fin (33 - 28 - 2), Fin (33 - (28 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨28, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2057, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a11_b09_c29 (q : Σ d : Fin (33 - 29 - 2), Fin (33 - (29 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨29, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b09_c30 (q : Σ d : Fin (33 - 30 - 2), Fin (33 - (30 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) ⟨(⟨30, by norm_num⟩ : Fin (33 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

theorem certificate105_a11_b09 (q : IncreasingThree 33) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨21, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a11_b09_c00 q
  · exact certificate105_a11_b09_c01 q
  · exact certificate105_a11_b09_c02 q
  · exact certificate105_a11_b09_c03 q
  · exact certificate105_a11_b09_c04 q
  · exact certificate105_a11_b09_c05 q
  · exact certificate105_a11_b09_c06 q
  · exact certificate105_a11_b09_c07 q
  · exact certificate105_a11_b09_c08 q
  · exact certificate105_a11_b09_c09 q
  · exact certificate105_a11_b09_c10 q
  · exact certificate105_a11_b09_c11 q
  · exact certificate105_a11_b09_c12 q
  · exact certificate105_a11_b09_c13 q
  · exact certificate105_a11_b09_c14 q
  · exact certificate105_a11_b09_c15 q
  · exact certificate105_a11_b09_c16 q
  · exact certificate105_a11_b09_c17 q
  · exact certificate105_a11_b09_c18 q
  · exact certificate105_a11_b09_c19 q
  · exact certificate105_a11_b09_c20 q
  · exact certificate105_a11_b09_c21 q
  · exact certificate105_a11_b09_c22 q
  · exact certificate105_a11_b09_c23 q
  · exact certificate105_a11_b09_c24 q
  · exact certificate105_a11_b09_c25 q
  · exact certificate105_a11_b09_c26 q
  · exact certificate105_a11_b09_c27 q
  · exact certificate105_a11_b09_c28 q
  · exact certificate105_a11_b09_c29 q
  · exact certificate105_a11_b09_c30 q

end MinModulus.SHCSixExceptionalCertificate.Generated
