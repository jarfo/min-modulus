import MinModulus.Generated.SHCSixN105A11B11

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a11_b13_c00 (q : Σ d : Fin (29 - 0 - 2), Fin (29 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9185, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13312, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨46, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨7964, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5252, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13710, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7940, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5300, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8800, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c01 (q : Σ d : Fin (29 - 1 - 2), Fin (29 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨4483, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c02 (q : Σ d : Fin (29 - 2 - 2), Fin (29 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨12, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c03 (q : Σ d : Fin (29 - 3 - 2), Fin (29 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨7580, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨189, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨693, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨1062, by decide, by decide⟩
    · exact ⟨2331, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6836, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13710, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5252, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8348, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11017, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12592, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8800, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c04 (q : Σ d : Fin (29 - 4 - 2), Fin (29 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5252, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨2077, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨1953, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨45, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11011, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13313, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c05 (q : Σ d : Fin (29 - 5 - 2), Fin (29 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9185, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11779, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13313, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11017, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c06 (q : Σ d : Fin (29 - 6 - 2), Fin (29 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨1825, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7940, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11395, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c07 (q : Σ d : Fin (29 - 7 - 2), Fin (29 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨25612, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11779, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c08 (q : Σ d : Fin (29 - 8 - 2), Fin (29 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨5251, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c09 (q : Σ d : Fin (29 - 9 - 2), Fin (29 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10651, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5347, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c10 (q : Σ d : Fin (29 - 10 - 2), Fin (29 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9185, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c11 (q : Σ d : Fin (29 - 11 - 2), Fin (29 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c12 (q : Σ d : Fin (29 - 12 - 2), Fin (29 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c13 (q : Σ d : Fin (29 - 13 - 2), Fin (29 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨519, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c14 (q : Σ d : Fin (29 - 14 - 2), Fin (29 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c15 (q : Σ d : Fin (29 - 15 - 2), Fin (29 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨24076, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨425, by decide, by decide⟩
    · exact ⟨8128, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨20320, by decide, by decide⟩
    · exact ⟨2457, by decide, by decide⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c16 (q : Σ d : Fin (29 - 16 - 2), Fin (29 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c17 (q : Σ d : Fin (29 - 17 - 2), Fin (29 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c18 (q : Σ d : Fin (29 - 18 - 2), Fin (29 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c19 (q : Σ d : Fin (29 - 19 - 2), Fin (29 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨7936, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c20 (q : Σ d : Fin (29 - 20 - 2), Fin (29 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨20, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9185, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c21 (q : Σ d : Fin (29 - 21 - 2), Fin (29 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨21, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨6787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c22 (q : Σ d : Fin (29 - 22 - 2), Fin (29 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨22, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9185, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c23 (q : Σ d : Fin (29 - 23 - 2), Fin (29 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨23, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨7577, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c24 (q : Σ d : Fin (29 - 24 - 2), Fin (29 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨24, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨8801, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c25 (q : Σ d : Fin (29 - 25 - 2), Fin (29 - (25 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨25, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨26368, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b13_c26 (q : Σ d : Fin (29 - 26 - 2), Fin (29 - (26 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨26, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a11_b13 (q : IncreasingThree 29) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a11_b13_c00 q
  · exact certificate105_a11_b13_c01 q
  · exact certificate105_a11_b13_c02 q
  · exact certificate105_a11_b13_c03 q
  · exact certificate105_a11_b13_c04 q
  · exact certificate105_a11_b13_c05 q
  · exact certificate105_a11_b13_c06 q
  · exact certificate105_a11_b13_c07 q
  · exact certificate105_a11_b13_c08 q
  · exact certificate105_a11_b13_c09 q
  · exact certificate105_a11_b13_c10 q
  · exact certificate105_a11_b13_c11 q
  · exact certificate105_a11_b13_c12 q
  · exact certificate105_a11_b13_c13 q
  · exact certificate105_a11_b13_c14 q
  · exact certificate105_a11_b13_c15 q
  · exact certificate105_a11_b13_c16 q
  · exact certificate105_a11_b13_c17 q
  · exact certificate105_a11_b13_c18 q
  · exact certificate105_a11_b13_c19 q
  · exact certificate105_a11_b13_c20 q
  · exact certificate105_a11_b13_c21 q
  · exact certificate105_a11_b13_c22 q
  · exact certificate105_a11_b13_c23 q
  · exact certificate105_a11_b13_c24 q
  · exact certificate105_a11_b13_c25 q
  · exact certificate105_a11_b13_c26 q

end MinModulus.SHCSixExceptionalCertificate.Generated
