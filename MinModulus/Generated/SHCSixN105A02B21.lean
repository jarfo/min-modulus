import MinModulus.Generated.SHCSixN105A02B19

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a02_b21_c00 (q : Σ d : Fin (30 - 0 - 2), Fin (30 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  exact ⟨6448, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c01 (q : Σ d : Fin (30 - 1 - 2), Fin (30 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11777, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3457, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨35, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2693, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5636, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7946, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨181, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨2067, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨35, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2693, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨2961, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨35, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2693, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨35, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2693, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c02 (q : Σ d : Fin (30 - 2 - 2), Fin (30 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  exact ⟨4483, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c03 (q : Σ d : Fin (30 - 3 - 2), Fin (30 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  exact ⟨9472, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c04 (q : Σ d : Fin (30 - 4 - 2), Fin (30 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  exact ⟨12, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c05 (q : Σ d : Fin (30 - 5 - 2), Fin (30 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11777, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11791, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5636, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨433, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨181, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨35, by decide, by decide⟩
    · exact ⟨803, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
  · fin_cases e
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨2457, by decide, by decide⟩
    · exact ⟨1953, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨2693, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨803, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨2693, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
  · fin_cases e
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨35, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c06 (q : Σ d : Fin (30 - 6 - 2), Fin (30 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c07 (q : Σ d : Fin (30 - 7 - 2), Fin (30 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c08 (q : Σ d : Fin (30 - 8 - 2), Fin (30 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11777, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12553, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2693, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3331, by decide, by decide⟩
    · exact ⟨1953, by decide, by decide⟩
    · exact ⟨35, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨11779, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7946, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5347, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c09 (q : Σ d : Fin (30 - 9 - 2), Fin (30 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c10 (q : Σ d : Fin (30 - 10 - 2), Fin (30 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c11 (q : Σ d : Fin (30 - 11 - 2), Fin (30 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  exact ⟨8705, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c12 (q : Σ d : Fin (30 - 12 - 2), Fin (30 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5636, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨3331, by decide, by decide⟩
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨35, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2457, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨35, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨35, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2205, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c13 (q : Σ d : Fin (30 - 13 - 2), Fin (30 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  exact ⟨6031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c14 (q : Σ d : Fin (30 - 14 - 2), Fin (30 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  exact ⟨5635, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c15 (q : Σ d : Fin (30 - 15 - 2), Fin (30 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨173, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3969, by decide, by decide⟩
    · exact ⟨2205, by decide, by decide⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨11200, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨14855, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c16 (q : Σ d : Fin (30 - 16 - 2), Fin (30 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6452, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7940, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨11200, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a02_b21_c17 (q : Σ d : Fin (30 - 17 - 2), Fin (30 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11419, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c18 (q : Σ d : Fin (30 - 18 - 2), Fin (30 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨35, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3083, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a02_b21_c19 (q : Σ d : Fin (30 - 19 - 2), Fin (30 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14855, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c20 (q : Σ d : Fin (30 - 20 - 2), Fin (30 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨20, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a02_b21_c21 (q : Σ d : Fin (30 - 21 - 2), Fin (30 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨21, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c22 (q : Σ d : Fin (30 - 22 - 2), Fin (30 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨22, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  exact ⟨7938, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c23 (q : Σ d : Fin (30 - 23 - 2), Fin (30 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨23, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c24 (q : Σ d : Fin (30 - 24 - 2), Fin (30 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨24, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c25 (q : Σ d : Fin (30 - 25 - 2), Fin (30 - (25 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨25, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c26 (q : Σ d : Fin (30 - 26 - 2), Fin (30 - (26 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨26, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a02_b21_c27 (q : Σ d : Fin (30 - 27 - 2), Fin (30 - (27 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) ⟨(⟨27, by norm_num⟩ : Fin (30 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a02_b21 (q : IncreasingThree 30) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨2, by norm_num⟩ : Fin 55) (⟨24, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a02_b21_c00 q
  · exact certificate105_a02_b21_c01 q
  · exact certificate105_a02_b21_c02 q
  · exact certificate105_a02_b21_c03 q
  · exact certificate105_a02_b21_c04 q
  · exact certificate105_a02_b21_c05 q
  · exact certificate105_a02_b21_c06 q
  · exact certificate105_a02_b21_c07 q
  · exact certificate105_a02_b21_c08 q
  · exact certificate105_a02_b21_c09 q
  · exact certificate105_a02_b21_c10 q
  · exact certificate105_a02_b21_c11 q
  · exact certificate105_a02_b21_c12 q
  · exact certificate105_a02_b21_c13 q
  · exact certificate105_a02_b21_c14 q
  · exact certificate105_a02_b21_c15 q
  · exact certificate105_a02_b21_c16 q
  · exact certificate105_a02_b21_c17 q
  · exact certificate105_a02_b21_c18 q
  · exact certificate105_a02_b21_c19 q
  · exact certificate105_a02_b21_c20 q
  · exact certificate105_a02_b21_c21 q
  · exact certificate105_a02_b21_c22 q
  · exact certificate105_a02_b21_c23 q
  · exact certificate105_a02_b21_c24 q
  · exact certificate105_a02_b21_c25 q
  · exact certificate105_a02_b21_c26 q
  · exact certificate105_a02_b21_c27 q

end MinModulus.SHCSixExceptionalCertificate.Generated
