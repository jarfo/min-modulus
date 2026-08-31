import MinModulus.Generated.SHCSixN105A00B26

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a00_b28_c00 (q : Σ d : Fin (25 - 0 - 2), Fin (25 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c01 (q : Σ d : Fin (25 - 1 - 2), Fin (25 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c02 (q : Σ d : Fin (25 - 2 - 2), Fin (25 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨7577, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c03 (q : Σ d : Fin (25 - 3 - 2), Fin (25 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11056, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3457, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨18832, by decide, by decide⟩
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨1953, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨425, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨11785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10651, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨1825, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1953, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c04 (q : Σ d : Fin (25 - 4 - 2), Fin (25 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨25600, by decide, by decide⟩
    · exact ⟨3457, by decide, by decide⟩
    · exact ⟨1827, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨1953, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨11419, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨24832, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2457, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨1825, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1953, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨12175, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11791, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨1825, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c05 (q : Σ d : Fin (25 - 5 - 2), Fin (25 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11056, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3457, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2077, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨46, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨3331, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨1825, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11419, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c06 (q : Σ d : Fin (25 - 6 - 2), Fin (25 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨425, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨1825, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c07 (q : Σ d : Fin (25 - 7 - 2), Fin (25 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨433, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨2819, by decide, by decide⟩
    · exact ⟨425, by decide, by decide⟩
    · exact ⟨1827, by decide, by decide⟩
    · exact ⟨18832, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨1825, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3589, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c08 (q : Σ d : Fin (25 - 8 - 2), Fin (25 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨441, by decide, by decide⟩
    · exact ⟨3589, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10651, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11791, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c09 (q : Σ d : Fin (25 - 9 - 2), Fin (25 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12547, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12553, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11779, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c10 (q : Σ d : Fin (25 - 10 - 2), Fin (25 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12547, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨12553, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11419, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c11 (q : Σ d : Fin (25 - 11 - 2), Fin (25 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨441, by decide, by decide⟩
    · exact ⟨3589, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨441, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨25624, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨7940, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12931, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨17248, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨12547, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c12 (q : Σ d : Fin (25 - 12 - 2), Fin (25 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨5275, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c13 (q : Σ d : Fin (25 - 13 - 2), Fin (25 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨563, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2067, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6836, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3083, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c14 (q : Σ d : Fin (25 - 14 - 2), Fin (25 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3591, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7946, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨17248, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c15 (q : Σ d : Fin (25 - 15 - 2), Fin (25 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c16 (q : Σ d : Fin (25 - 16 - 2), Fin (25 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11056, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c17 (q : Σ d : Fin (25 - 17 - 2), Fin (25 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c18 (q : Σ d : Fin (25 - 18 - 2), Fin (25 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c19 (q : Σ d : Fin (25 - 19 - 2), Fin (25 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11056, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c20 (q : Σ d : Fin (25 - 20 - 2), Fin (25 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨20, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c21 (q : Σ d : Fin (25 - 21 - 2), Fin (25 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨21, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11056, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a00_b28_c22 (q : Σ d : Fin (25 - 22 - 2), Fin (25 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨22, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a00_b28 (q : IncreasingThree 25) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨0, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a00_b28_c00 q
  · exact certificate105_a00_b28_c01 q
  · exact certificate105_a00_b28_c02 q
  · exact certificate105_a00_b28_c03 q
  · exact certificate105_a00_b28_c04 q
  · exact certificate105_a00_b28_c05 q
  · exact certificate105_a00_b28_c06 q
  · exact certificate105_a00_b28_c07 q
  · exact certificate105_a00_b28_c08 q
  · exact certificate105_a00_b28_c09 q
  · exact certificate105_a00_b28_c10 q
  · exact certificate105_a00_b28_c11 q
  · exact certificate105_a00_b28_c12 q
  · exact certificate105_a00_b28_c13 q
  · exact certificate105_a00_b28_c14 q
  · exact certificate105_a00_b28_c15 q
  · exact certificate105_a00_b28_c16 q
  · exact certificate105_a00_b28_c17 q
  · exact certificate105_a00_b28_c18 q
  · exact certificate105_a00_b28_c19 q
  · exact certificate105_a00_b28_c20 q
  · exact certificate105_a00_b28_c21 q
  · exact certificate105_a00_b28_c22 q

end MinModulus.SHCSixExceptionalCertificate.Generated
