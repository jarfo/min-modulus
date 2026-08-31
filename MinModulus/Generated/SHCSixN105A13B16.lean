import MinModulus.Generated.SHCSixN105A13B14

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a13_b16_c00 (q : Σ d : Fin (24 - 0 - 2), Fin (24 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c01 (q : Σ d : Fin (24 - 1 - 2), Fin (24 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨3969, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨433, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
    · exact ⟨566, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2189, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a13_b16_c02 (q : Σ d : Fin (24 - 2 - 2), Fin (24 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨1825, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨2583, by decide, by decide⟩
    · exact ⟨181, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6410, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c03 (q : Σ d : Fin (24 - 3 - 2), Fin (24 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  exact ⟨4867, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c04 (q : Σ d : Fin (24 - 4 - 2), Fin (24 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  exact ⟨6031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c05 (q : Σ d : Fin (24 - 5 - 2), Fin (24 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9476, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5300, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6410, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c06 (q : Σ d : Fin (24 - 6 - 2), Fin (24 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c07 (q : Σ d : Fin (24 - 7 - 2), Fin (24 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c08 (q : Σ d : Fin (24 - 8 - 2), Fin (24 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6410, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c09 (q : Σ d : Fin (24 - 9 - 2), Fin (24 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c10 (q : Σ d : Fin (24 - 10 - 2), Fin (24 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2074, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2205, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6410, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6068, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c11 (q : Σ d : Fin (24 - 11 - 2), Fin (24 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c12 (q : Σ d : Fin (24 - 12 - 2), Fin (24 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c13 (q : Σ d : Fin (24 - 13 - 2), Fin (24 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9185, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6410, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c14 (q : Σ d : Fin (24 - 14 - 2), Fin (24 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  exact ⟨519, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c15 (q : Σ d : Fin (24 - 15 - 2), Fin (24 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  exact ⟨7944, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c16 (q : Σ d : Fin (24 - 16 - 2), Fin (24 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨6410, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a13_b16_c17 (q : Σ d : Fin (24 - 17 - 2), Fin (24 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  exact ⟨6409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c18 (q : Σ d : Fin (24 - 18 - 2), Fin (24 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨6788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c19 (q : Σ d : Fin (24 - 19 - 2), Fin (24 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  exact ⟨6787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a13_b16_c20 (q : Σ d : Fin (24 - 20 - 2), Fin (24 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨20, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a13_b16_c21 (q : Σ d : Fin (24 - 21 - 2), Fin (24 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) ⟨(⟨21, by norm_num⟩ : Fin (24 - 2)), q⟩) code = true := by
  exact ⟨9089, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a13_b16 (q : IncreasingThree 24) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨13, by norm_num⟩ : Fin 55) (⟨30, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a13_b16_c00 q
  · exact certificate105_a13_b16_c01 q
  · exact certificate105_a13_b16_c02 q
  · exact certificate105_a13_b16_c03 q
  · exact certificate105_a13_b16_c04 q
  · exact certificate105_a13_b16_c05 q
  · exact certificate105_a13_b16_c06 q
  · exact certificate105_a13_b16_c07 q
  · exact certificate105_a13_b16_c08 q
  · exact certificate105_a13_b16_c09 q
  · exact certificate105_a13_b16_c10 q
  · exact certificate105_a13_b16_c11 q
  · exact certificate105_a13_b16_c12 q
  · exact certificate105_a13_b16_c13 q
  · exact certificate105_a13_b16_c14 q
  · exact certificate105_a13_b16_c15 q
  · exact certificate105_a13_b16_c16 q
  · exact certificate105_a13_b16_c17 q
  · exact certificate105_a13_b16_c18 q
  · exact certificate105_a13_b16_c19 q
  · exact certificate105_a13_b16_c20 q
  · exact certificate105_a13_b16_c21 q

end MinModulus.SHCSixExceptionalCertificate.Generated
