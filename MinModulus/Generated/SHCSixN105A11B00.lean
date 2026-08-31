import MinModulus.Generated.SHCSixN105A10B39

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a11_b00_c00 (q : Σ d : Fin (42 - 0 - 2), Fin (42 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨515, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c01 (q : Σ d : Fin (42 - 1 - 2), Fin (42 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c02 (q : Σ d : Fin (42 - 2 - 2), Fin (42 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11779, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11011, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11017, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨42, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨49, by decide, by decide⟩
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨565, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨2069, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨37, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨2074, by decide, by decide⟩
    · exact ⟨1062, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨10625, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10243, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨37, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨1569, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨54, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨5636, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5252, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨25, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3086, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2201, by decide, by decide⟩
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c03 (q : Σ d : Fin (42 - 3 - 2), Fin (42 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1291, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11395, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11011, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10627, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11791, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5347, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨25, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1039, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨169, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨2201, by decide, by decide⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12592, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14855, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c04 (q : Σ d : Fin (42 - 4 - 2), Fin (42 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨45, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2061, by decide, by decide⟩
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨1569, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨37, by decide, by decide⟩
    · exact ⟨3337, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1062, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8800, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5636, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1039, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14855, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c05 (q : Σ d : Fin (42 - 5 - 2), Fin (42 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8800, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨25, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13312, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12592, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c06 (q : Σ d : Fin (42 - 6 - 2), Fin (42 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11395, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5347, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13312, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10627, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10651, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c07 (q : Σ d : Fin (42 - 7 - 2), Fin (42 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1291, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10625, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨37, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨13504, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨4484, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11779, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6452, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨37, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨21377, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14855, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c08 (q : Σ d : Fin (42 - 8 - 2), Fin (42 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨3073, by decide, by decide⟩
    · exact ⟨41, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2061, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨37, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨4484, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨41, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨2819, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨3337, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨1069, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2073, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11395, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨25, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨37, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨3086, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c09 (q : Σ d : Fin (42 - 9 - 2), Fin (42 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨7553, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c10 (q : Σ d : Fin (42 - 10 - 2), Fin (42 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨7169, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c11 (q : Σ d : Fin (42 - 11 - 2), Fin (42 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c12 (q : Σ d : Fin (42 - 12 - 2), Fin (42 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨7170, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c13 (q : Σ d : Fin (42 - 13 - 2), Fin (42 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13312, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨37, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨54, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨5636, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5252, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8800, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7940, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨2961, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨5300, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c14 (q : Σ d : Fin (42 - 14 - 2), Fin (42 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨4483, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c15 (q : Σ d : Fin (42 - 15 - 2), Fin (42 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1291, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨24449, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨3337, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨2323, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨5636, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5252, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7580, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨13889, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨5300, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨425, by decide, by decide⟩
    · exact ⟨9664, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨21856, by decide, by decide⟩
    · exact ⟨2457, by decide, by decide⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c16 (q : Σ d : Fin (42 - 16 - 2), Fin (42 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨14, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c17 (q : Σ d : Fin (42 - 17 - 2), Fin (42 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨3337, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨12547, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5252, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11011, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2961, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨2567, by decide, by decide⟩
    · exact ⟨2457, by decide, by decide⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13698, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13313, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13314, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c18 (q : Σ d : Fin (42 - 18 - 2), Fin (42 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13313, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13314, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11017, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a11_b00_c19 (q : Σ d : Fin (42 - 19 - 2), Fin (42 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1291, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨37, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨46, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7940, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11395, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a11_b00_c20 (q : Σ d : Fin (42 - 20 - 2), Fin (42 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨20, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨5635, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c21 (q : Σ d : Fin (42 - 21 - 2), Fin (42 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨21, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨5251, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c22 (q : Σ d : Fin (42 - 22 - 2), Fin (42 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨22, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3337, by decide, by decide⟩
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5347, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c23 (q : Σ d : Fin (42 - 23 - 2), Fin (42 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨23, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨7577, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c24 (q : Σ d : Fin (42 - 24 - 2), Fin (42 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨24, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8800, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11058, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c25 (q : Σ d : Fin (42 - 25 - 2), Fin (42 - (25 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨25, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8348, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11825, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c26 (q : Σ d : Fin (42 - 26 - 2), Fin (42 - (26 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨26, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨13, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c27 (q : Σ d : Fin (42 - 27 - 2), Fin (42 - (27 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨27, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c28 (q : Σ d : Fin (42 - 28 - 2), Fin (42 - (28 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨28, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨12, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c29 (q : Σ d : Fin (42 - 29 - 2), Fin (42 - (29 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨29, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c30 (q : Σ d : Fin (42 - 30 - 2), Fin (42 - (30 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨30, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c31 (q : Σ d : Fin (42 - 31 - 2), Fin (42 - (31 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨31, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨6065, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c32 (q : Σ d : Fin (42 - 32 - 2), Fin (42 - (32 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨32, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  exact ⟨7936, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c33 (q : Σ d : Fin (42 - 33 - 2), Fin (42 - (33 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨33, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a11_b00_c34 (q : Σ d : Fin (42 - 34 - 2), Fin (42 - (34 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨34, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1291, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2689, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10651, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c35 (q : Σ d : Fin (42 - 35 - 2), Fin (42 - (35 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨35, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8348, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c36 (q : Σ d : Fin (42 - 36 - 2), Fin (42 - (36 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨36, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c37 (q : Σ d : Fin (42 - 37 - 2), Fin (42 - (37 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨37, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1291, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c38 (q : Σ d : Fin (42 - 38 - 2), Fin (42 - (38 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨38, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1291, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b00_c39 (q : Σ d : Fin (42 - 39 - 2), Fin (42 - (39 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) ⟨(⟨39, by norm_num⟩ : Fin (42 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a11_b00 (q : IncreasingThree 42) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨12, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a11_b00_c00 q
  · exact certificate105_a11_b00_c01 q
  · exact certificate105_a11_b00_c02 q
  · exact certificate105_a11_b00_c03 q
  · exact certificate105_a11_b00_c04 q
  · exact certificate105_a11_b00_c05 q
  · exact certificate105_a11_b00_c06 q
  · exact certificate105_a11_b00_c07 q
  · exact certificate105_a11_b00_c08 q
  · exact certificate105_a11_b00_c09 q
  · exact certificate105_a11_b00_c10 q
  · exact certificate105_a11_b00_c11 q
  · exact certificate105_a11_b00_c12 q
  · exact certificate105_a11_b00_c13 q
  · exact certificate105_a11_b00_c14 q
  · exact certificate105_a11_b00_c15 q
  · exact certificate105_a11_b00_c16 q
  · exact certificate105_a11_b00_c17 q
  · exact certificate105_a11_b00_c18 q
  · exact certificate105_a11_b00_c19 q
  · exact certificate105_a11_b00_c20 q
  · exact certificate105_a11_b00_c21 q
  · exact certificate105_a11_b00_c22 q
  · exact certificate105_a11_b00_c23 q
  · exact certificate105_a11_b00_c24 q
  · exact certificate105_a11_b00_c25 q
  · exact certificate105_a11_b00_c26 q
  · exact certificate105_a11_b00_c27 q
  · exact certificate105_a11_b00_c28 q
  · exact certificate105_a11_b00_c29 q
  · exact certificate105_a11_b00_c30 q
  · exact certificate105_a11_b00_c31 q
  · exact certificate105_a11_b00_c32 q
  · exact certificate105_a11_b00_c33 q
  · exact certificate105_a11_b00_c34 q
  · exact certificate105_a11_b00_c35 q
  · exact certificate105_a11_b00_c36 q
  · exact certificate105_a11_b00_c37 q
  · exact certificate105_a11_b00_c38 q
  · exact certificate105_a11_b00_c39 q

end MinModulus.SHCSixExceptionalCertificate.Generated
