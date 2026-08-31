import MinModulus.Generated.SHCSixN105A04B18

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a04_b20_c00 (q : Σ d : Fin (29 - 0 - 2), Fin (29 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨9472, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c01 (q : Σ d : Fin (29 - 1 - 2), Fin (29 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨6448, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c02 (q : Σ d : Fin (29 - 2 - 2), Fin (29 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨12, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c03 (q : Σ d : Fin (29 - 3 - 2), Fin (29 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨1953, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨689, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11777, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11783, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨21760, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6410, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨15808, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1953, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨21760, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c04 (q : Σ d : Fin (29 - 4 - 2), Fin (29 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c05 (q : Σ d : Fin (29 - 5 - 2), Fin (29 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c06 (q : Σ d : Fin (29 - 6 - 2), Fin (29 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨519, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c07 (q : Σ d : Fin (29 - 7 - 2), Fin (29 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c08 (q : Σ d : Fin (29 - 8 - 2), Fin (29 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12161, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11777, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2205, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨433, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨181, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨425, by decide, by decide⟩
    · exact ⟨2078, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨11783, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨46, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1953, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨14296, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c09 (q : Σ d : Fin (29 - 9 - 2), Fin (29 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11419, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11777, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10651, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5347, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c10 (q : Σ d : Fin (29 - 10 - 2), Fin (29 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c11 (q : Σ d : Fin (29 - 11 - 2), Fin (29 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨9089, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c12 (q : Σ d : Fin (29 - 12 - 2), Fin (29 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨8705, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c13 (q : Σ d : Fin (29 - 13 - 2), Fin (29 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c14 (q : Σ d : Fin (29 - 14 - 2), Fin (29 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨8711, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c15 (q : Σ d : Fin (29 - 15 - 2), Fin (29 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2819, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨441, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨27136, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c16 (q : Σ d : Fin (29 - 16 - 2), Fin (29 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨6409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c17 (q : Σ d : Fin (29 - 17 - 2), Fin (29 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨6787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c18 (q : Σ d : Fin (29 - 18 - 2), Fin (29 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨11200, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨8130, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨8034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c19 (q : Σ d : Fin (29 - 19 - 2), Fin (29 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨8322, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c20 (q : Σ d : Fin (29 - 20 - 2), Fin (29 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨20, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨7938, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c21 (q : Σ d : Fin (29 - 21 - 2), Fin (29 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨21, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c22 (q : Σ d : Fin (29 - 22 - 2), Fin (29 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨22, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨7944, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c23 (q : Σ d : Fin (29 - 23 - 2), Fin (29 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨23, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c24 (q : Σ d : Fin (29 - 24 - 2), Fin (29 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨24, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c25 (q : Σ d : Fin (29 - 25 - 2), Fin (29 - (25 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨25, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a04_b20_c26 (q : Σ d : Fin (29 - 26 - 2), Fin (29 - (26 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) ⟨(⟨26, by norm_num⟩ : Fin (29 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a04_b20 (q : IncreasingThree 29) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨4, by norm_num⟩ : Fin 55) (⟨25, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a04_b20_c00 q
  · exact certificate105_a04_b20_c01 q
  · exact certificate105_a04_b20_c02 q
  · exact certificate105_a04_b20_c03 q
  · exact certificate105_a04_b20_c04 q
  · exact certificate105_a04_b20_c05 q
  · exact certificate105_a04_b20_c06 q
  · exact certificate105_a04_b20_c07 q
  · exact certificate105_a04_b20_c08 q
  · exact certificate105_a04_b20_c09 q
  · exact certificate105_a04_b20_c10 q
  · exact certificate105_a04_b20_c11 q
  · exact certificate105_a04_b20_c12 q
  · exact certificate105_a04_b20_c13 q
  · exact certificate105_a04_b20_c14 q
  · exact certificate105_a04_b20_c15 q
  · exact certificate105_a04_b20_c16 q
  · exact certificate105_a04_b20_c17 q
  · exact certificate105_a04_b20_c18 q
  · exact certificate105_a04_b20_c19 q
  · exact certificate105_a04_b20_c20 q
  · exact certificate105_a04_b20_c21 q
  · exact certificate105_a04_b20_c22 q
  · exact certificate105_a04_b20_c23 q
  · exact certificate105_a04_b20_c24 q
  · exact certificate105_a04_b20_c25 q
  · exact certificate105_a04_b20_c26 q

end MinModulus.SHCSixExceptionalCertificate.Generated
