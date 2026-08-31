import MinModulus.Generated.SHCSixN105A11B18

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a11_b20_c00 (q : Σ d : Fin (22 - 0 - 2), Fin (22 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1062, by decide, by decide⟩
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨2449, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11783, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6404, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c01 (q : Σ d : Fin (22 - 1 - 2), Fin (22 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c02 (q : Σ d : Fin (22 - 2 - 2), Fin (22 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c03 (q : Σ d : Fin (22 - 3 - 2), Fin (22 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11783, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6404, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a11_b20_c04 (q : Σ d : Fin (22 - 4 - 2), Fin (22 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c05 (q : Σ d : Fin (22 - 5 - 2), Fin (22 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2057, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨3086, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1062, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨2449, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨1062, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨433, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨313, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a11_b20_c06 (q : Σ d : Fin (22 - 6 - 2), Fin (22 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11419, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11783, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6404, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c07 (q : Σ d : Fin (22 - 7 - 2), Fin (22 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c08 (q : Σ d : Fin (22 - 8 - 2), Fin (22 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11783, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6404, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c09 (q : Σ d : Fin (22 - 9 - 2), Fin (22 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c10 (q : Σ d : Fin (22 - 10 - 2), Fin (22 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c11 (q : Σ d : Fin (22 - 11 - 2), Fin (22 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8418, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11783, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6404, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c12 (q : Σ d : Fin (22 - 12 - 2), Fin (22 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c13 (q : Σ d : Fin (22 - 13 - 2), Fin (22 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨519, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c14 (q : Σ d : Fin (22 - 14 - 2), Fin (22 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11783, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6404, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a11_b20_c15 (q : Σ d : Fin (22 - 15 - 2), Fin (22 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨8711, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c16 (q : Σ d : Fin (22 - 16 - 2), Fin (22 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨6404, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c17 (q : Σ d : Fin (22 - 17 - 2), Fin (22 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨6403, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c18 (q : Σ d : Fin (22 - 18 - 2), Fin (22 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14855, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a11_b20_c19 (q : Σ d : Fin (22 - 19 - 2), Fin (22 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (22 - 2)), q⟩) code = true := by
  exact ⟨8322, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a11_b20 (q : IncreasingThree 22) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨11, by norm_num⟩ : Fin 55) (⟨32, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a11_b20_c00 q
  · exact certificate105_a11_b20_c01 q
  · exact certificate105_a11_b20_c02 q
  · exact certificate105_a11_b20_c03 q
  · exact certificate105_a11_b20_c04 q
  · exact certificate105_a11_b20_c05 q
  · exact certificate105_a11_b20_c06 q
  · exact certificate105_a11_b20_c07 q
  · exact certificate105_a11_b20_c08 q
  · exact certificate105_a11_b20_c09 q
  · exact certificate105_a11_b20_c10 q
  · exact certificate105_a11_b20_c11 q
  · exact certificate105_a11_b20_c12 q
  · exact certificate105_a11_b20_c13 q
  · exact certificate105_a11_b20_c14 q
  · exact certificate105_a11_b20_c15 q
  · exact certificate105_a11_b20_c16 q
  · exact certificate105_a11_b20_c17 q
  · exact certificate105_a11_b20_c18 q
  · exact certificate105_a11_b20_c19 q

end MinModulus.SHCSixExceptionalCertificate.Generated
