import MinModulus.Generated.SHCSixN105A14B03

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a14_b05_c00 (q : Σ d : Fin (34 - 0 - 2), Fin (34 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨3589, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨3086, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨3591, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨1062, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨17932, by decide, by decide⟩
    · exact ⟨46, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨25, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13312, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10243, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8418, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c01 (q : Σ d : Fin (34 - 1 - 2), Fin (34 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11779, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13312, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8720, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨689, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨51, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10627, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8708, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c02 (q : Σ d : Fin (34 - 2 - 2), Fin (34 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  exact ⟨5275, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c03 (q : Σ d : Fin (34 - 3 - 2), Fin (34 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  exact ⟨8322, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c04 (q : Σ d : Fin (34 - 4 - 2), Fin (34 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨16385, by decide, by decide⟩
    · exact ⟨3073, by decide, by decide⟩
    · exact ⟨1315, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨2693, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨3075, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨1569, by decide, by decide⟩
    · exact ⟨17932, by decide, by decide⟩
    · exact ⟨3843, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨4484, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11779, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11825, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11395, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12175, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨17932, by decide, by decide⟩
    · exact ⟨1315, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10243, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c05 (q : Σ d : Fin (34 - 5 - 2), Fin (34 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨2563, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2563, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨17932, by decide, by decide⟩
    · exact ⟨689, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨8720, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12175, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5300, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8708, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c06 (q : Σ d : Fin (34 - 6 - 2), Fin (34 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  exact ⟨4483, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c07 (q : Σ d : Fin (34 - 7 - 2), Fin (34 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  exact ⟨7944, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c08 (q : Σ d : Fin (34 - 8 - 2), Fin (34 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  exact ⟨7169, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c09 (q : Σ d : Fin (34 - 9 - 2), Fin (34 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7964, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
    · exact ⟨185, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨2061, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8720, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7940, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6068, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c10 (q : Σ d : Fin (34 - 10 - 2), Fin (34 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  exact ⟨6031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c11 (q : Σ d : Fin (34 - 11 - 2), Fin (34 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨693, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2078, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨53, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨2705, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13313, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c12 (q : Σ d : Fin (34 - 12 - 2), Fin (34 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  exact ⟨12, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c13 (q : Σ d : Fin (34 - 13 - 2), Fin (34 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨19480, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13313, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c14 (q : Σ d : Fin (34 - 14 - 2), Fin (34 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨693, by decide, by decide⟩
    · exact ⟨17969, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨185, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11825, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c15 (q : Σ d : Fin (34 - 15 - 2), Fin (34 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14466, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14082, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13313, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c16 (q : Σ d : Fin (34 - 16 - 2), Fin (34 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3587, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨2705, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c17 (q : Σ d : Fin (34 - 17 - 2), Fin (34 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨693, by decide, by decide⟩
    · exact ⟨3587, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11825, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c18 (q : Σ d : Fin (34 - 18 - 2), Fin (34 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c19 (q : Σ d : Fin (34 - 19 - 2), Fin (34 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2074, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨3589, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2077, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨12931, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c20 (q : Σ d : Fin (34 - 20 - 2), Fin (34 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨20, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c21 (q : Σ d : Fin (34 - 21 - 2), Fin (34 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨21, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6410, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7964, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12931, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6836, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c22 (q : Σ d : Fin (34 - 22 - 2), Fin (34 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨22, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1697, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11825, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c23 (q : Σ d : Fin (34 - 23 - 2), Fin (34 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨23, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  exact ⟨6409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c24 (q : Σ d : Fin (34 - 24 - 2), Fin (34 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨24, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨42, by decide, by decide⟩
    · exact ⟨803, by decide, by decide⟩
    · exact ⟨1697, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c25 (q : Σ d : Fin (34 - 25 - 2), Fin (34 - (25 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨25, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c26 (q : Σ d : Fin (34 - 26 - 2), Fin (34 - (26 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨26, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6836, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c27 (q : Σ d : Fin (34 - 27 - 2), Fin (34 - (27 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨27, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c28 (q : Σ d : Fin (34 - 28 - 2), Fin (34 - (28 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨28, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c29 (q : Σ d : Fin (34 - 29 - 2), Fin (34 - (29 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨29, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c30 (q : Σ d : Fin (34 - 30 - 2), Fin (34 - (30 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨30, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b05_c31 (q : Σ d : Fin (34 - 31 - 2), Fin (34 - (31 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) ⟨(⟨31, by norm_num⟩ : Fin (34 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a14_b05 (q : IncreasingThree 34) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨20, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a14_b05_c00 q
  · exact certificate105_a14_b05_c01 q
  · exact certificate105_a14_b05_c02 q
  · exact certificate105_a14_b05_c03 q
  · exact certificate105_a14_b05_c04 q
  · exact certificate105_a14_b05_c05 q
  · exact certificate105_a14_b05_c06 q
  · exact certificate105_a14_b05_c07 q
  · exact certificate105_a14_b05_c08 q
  · exact certificate105_a14_b05_c09 q
  · exact certificate105_a14_b05_c10 q
  · exact certificate105_a14_b05_c11 q
  · exact certificate105_a14_b05_c12 q
  · exact certificate105_a14_b05_c13 q
  · exact certificate105_a14_b05_c14 q
  · exact certificate105_a14_b05_c15 q
  · exact certificate105_a14_b05_c16 q
  · exact certificate105_a14_b05_c17 q
  · exact certificate105_a14_b05_c18 q
  · exact certificate105_a14_b05_c19 q
  · exact certificate105_a14_b05_c20 q
  · exact certificate105_a14_b05_c21 q
  · exact certificate105_a14_b05_c22 q
  · exact certificate105_a14_b05_c23 q
  · exact certificate105_a14_b05_c24 q
  · exact certificate105_a14_b05_c25 q
  · exact certificate105_a14_b05_c26 q
  · exact certificate105_a14_b05_c27 q
  · exact certificate105_a14_b05_c28 q
  · exact certificate105_a14_b05_c29 q
  · exact certificate105_a14_b05_c30 q
  · exact certificate105_a14_b05_c31 q

end MinModulus.SHCSixExceptionalCertificate.Generated
