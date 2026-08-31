import MinModulus.Generated.SHCSixN105A14B06

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a14_b08_c00 (q : Σ d : Fin (31 - 0 - 2), Fin (31 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨13320, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1029, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10627, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10243, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c01 (q : Σ d : Fin (31 - 1 - 2), Fin (31 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1029, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14855, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11395, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c02 (q : Σ d : Fin (31 - 2 - 2), Fin (31 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c03 (q : Σ d : Fin (31 - 3 - 2), Fin (31 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  exact ⟨13, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c04 (q : Σ d : Fin (31 - 4 - 2), Fin (31 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨13312, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13710, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13326, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12592, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c05 (q : Σ d : Fin (31 - 5 - 2), Fin (31 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  exact ⟨7169, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c06 (q : Σ d : Fin (31 - 6 - 2), Fin (31 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  exact ⟨12, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c07 (q : Σ d : Fin (31 - 7 - 2), Fin (31 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  exact ⟨769, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c08 (q : Σ d : Fin (31 - 8 - 2), Fin (31 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  exact ⟨8704, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c09 (q : Σ d : Fin (31 - 9 - 2), Fin (31 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  exact ⟨8322, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c10 (q : Σ d : Fin (31 - 10 - 2), Fin (31 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10651, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1825, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨62, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c11 (q : Σ d : Fin (31 - 11 - 2), Fin (31 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10651, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c12 (q : Σ d : Fin (31 - 12 - 2), Fin (31 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  exact ⟨6448, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c13 (q : Σ d : Fin (31 - 13 - 2), Fin (31 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c14 (q : Σ d : Fin (31 - 14 - 2), Fin (31 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c15 (q : Σ d : Fin (31 - 15 - 2), Fin (31 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c16 (q : Σ d : Fin (31 - 16 - 2), Fin (31 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  exact ⟨6019, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c17 (q : Σ d : Fin (31 - 17 - 2), Fin (31 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c18 (q : Σ d : Fin (31 - 18 - 2), Fin (31 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6068, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c19 (q : Σ d : Fin (31 - 19 - 2), Fin (31 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨42, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c20 (q : Σ d : Fin (31 - 20 - 2), Fin (31 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨20, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c21 (q : Σ d : Fin (31 - 21 - 2), Fin (31 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨21, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c22 (q : Σ d : Fin (31 - 22 - 2), Fin (31 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨22, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c23 (q : Σ d : Fin (31 - 23 - 2), Fin (31 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨23, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c24 (q : Σ d : Fin (31 - 24 - 2), Fin (31 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨24, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  exact ⟨7554, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c25 (q : Σ d : Fin (31 - 25 - 2), Fin (31 - (25 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨25, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6883, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c26 (q : Σ d : Fin (31 - 26 - 2), Fin (31 - (26 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨26, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  exact ⟨7170, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c27 (q : Σ d : Fin (31 - 27 - 2), Fin (31 - (27 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨27, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨6209, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a14_b08_c28 (q : Σ d : Fin (31 - 28 - 2), Fin (31 - (28 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) ⟨(⟨28, by norm_num⟩ : Fin (31 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a14_b08 (q : IncreasingThree 31) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨14, by norm_num⟩ : Fin 55) (⟨23, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a14_b08_c00 q
  · exact certificate105_a14_b08_c01 q
  · exact certificate105_a14_b08_c02 q
  · exact certificate105_a14_b08_c03 q
  · exact certificate105_a14_b08_c04 q
  · exact certificate105_a14_b08_c05 q
  · exact certificate105_a14_b08_c06 q
  · exact certificate105_a14_b08_c07 q
  · exact certificate105_a14_b08_c08 q
  · exact certificate105_a14_b08_c09 q
  · exact certificate105_a14_b08_c10 q
  · exact certificate105_a14_b08_c11 q
  · exact certificate105_a14_b08_c12 q
  · exact certificate105_a14_b08_c13 q
  · exact certificate105_a14_b08_c14 q
  · exact certificate105_a14_b08_c15 q
  · exact certificate105_a14_b08_c16 q
  · exact certificate105_a14_b08_c17 q
  · exact certificate105_a14_b08_c18 q
  · exact certificate105_a14_b08_c19 q
  · exact certificate105_a14_b08_c20 q
  · exact certificate105_a14_b08_c21 q
  · exact certificate105_a14_b08_c22 q
  · exact certificate105_a14_b08_c23 q
  · exact certificate105_a14_b08_c24 q
  · exact certificate105_a14_b08_c25 q
  · exact certificate105_a14_b08_c26 q
  · exact certificate105_a14_b08_c27 q
  · exact certificate105_a14_b08_c28 q

end MinModulus.SHCSixExceptionalCertificate.Generated
