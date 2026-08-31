import MinModulus.Generated.SHCSixN105A34B00

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a34_b02_c00 (q : Σ d : Fin (17 - 0 - 2), Fin (17 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨897, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a34_b02_c01 (q : Σ d : Fin (17 - 1 - 2), Fin (17 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨3457, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5252, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · fin_cases e
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a34_b02_c02 (q : Σ d : Fin (17 - 2 - 2), Fin (17 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨9472, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a34_b02_c03 (q : Σ d : Fin (17 - 3 - 2), Fin (17 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨3457, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5252, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · fin_cases e
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨185, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1953, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a34_b02_c04 (q : Σ d : Fin (17 - 4 - 2), Fin (17 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨7944, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a34_b02_c05 (q : Σ d : Fin (17 - 5 - 2), Fin (17 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3457, by decide, by decide⟩
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1953, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a34_b02_c06 (q : Σ d : Fin (17 - 6 - 2), Fin (17 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨5252, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6068, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a34_b02_c07 (q : Σ d : Fin (17 - 7 - 2), Fin (17 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨5251, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a34_b02_c08 (q : Σ d : Fin (17 - 8 - 2), Fin (17 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨6019, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a34_b02_c09 (q : Σ d : Fin (17 - 9 - 2), Fin (17 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨313, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a34_b02_c10 (q : Σ d : Fin (17 - 10 - 2), Fin (17 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2189, by decide, by decide⟩

private theorem certificate105_a34_b02_c11 (q : Σ d : Fin (17 - 11 - 2), Fin (17 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a34_b02_c12 (q : Σ d : Fin (17 - 12 - 2), Fin (17 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a34_b02_c13 (q : Σ d : Fin (17 - 13 - 2), Fin (17 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8348, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a34_b02_c14 (q : Σ d : Fin (17 - 14 - 2), Fin (17 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (17 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a34_b02 (q : IncreasingThree 17) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨37, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a34_b02_c00 q
  · exact certificate105_a34_b02_c01 q
  · exact certificate105_a34_b02_c02 q
  · exact certificate105_a34_b02_c03 q
  · exact certificate105_a34_b02_c04 q
  · exact certificate105_a34_b02_c05 q
  · exact certificate105_a34_b02_c06 q
  · exact certificate105_a34_b02_c07 q
  · exact certificate105_a34_b02_c08 q
  · exact certificate105_a34_b02_c09 q
  · exact certificate105_a34_b02_c10 q
  · exact certificate105_a34_b02_c11 q
  · exact certificate105_a34_b02_c12 q
  · exact certificate105_a34_b02_c13 q
  · exact certificate105_a34_b02_c14 q

end MinModulus.SHCSixExceptionalCertificate.Generated
