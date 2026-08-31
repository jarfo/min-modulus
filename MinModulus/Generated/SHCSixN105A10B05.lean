import MinModulus.Generated.SHCSixN105A10B03

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a10_b05_c00 (q : Σ d : Fin (38 - 0 - 2), Fin (38 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1029, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10625, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5346, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11442, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11058, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8418, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c01 (q : Σ d : Fin (38 - 1 - 2), Fin (38 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c02 (q : Σ d : Fin (38 - 2 - 2), Fin (38 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨7553, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c03 (q : Σ d : Fin (38 - 3 - 2), Fin (38 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5346, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11058, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c04 (q : Σ d : Fin (38 - 4 - 2), Fin (38 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨7169, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c05 (q : Σ d : Fin (38 - 5 - 2), Fin (38 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨7938, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c06 (q : Σ d : Fin (38 - 6 - 2), Fin (38 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨15, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c07 (q : Σ d : Fin (38 - 7 - 2), Fin (38 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨14860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5346, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11442, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13313, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c08 (q : Σ d : Fin (38 - 8 - 2), Fin (38 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5346, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8800, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11058, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c09 (q : Σ d : Fin (38 - 9 - 2), Fin (38 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨14, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c10 (q : Σ d : Fin (38 - 10 - 2), Fin (38 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c11 (q : Σ d : Fin (38 - 11 - 2), Fin (38 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨13312, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5346, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11058, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c12 (q : Σ d : Fin (38 - 12 - 2), Fin (38 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5346, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13313, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11442, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c13 (q : Σ d : Fin (38 - 13 - 2), Fin (38 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨519, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c14 (q : Σ d : Fin (38 - 14 - 2), Fin (38 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨6031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c15 (q : Σ d : Fin (38 - 15 - 2), Fin (38 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨5298, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c16 (q : Σ d : Fin (38 - 16 - 2), Fin (38 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c17 (q : Σ d : Fin (38 - 17 - 2), Fin (38 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨7170, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c18 (q : Σ d : Fin (38 - 18 - 2), Fin (38 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨13, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c19 (q : Σ d : Fin (38 - 19 - 2), Fin (38 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13313, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13698, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c20 (q : Σ d : Fin (38 - 20 - 2), Fin (38 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨20, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨12, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c21 (q : Σ d : Fin (38 - 21 - 2), Fin (38 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨21, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨769, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c22 (q : Σ d : Fin (38 - 22 - 2), Fin (38 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨22, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11776, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13698, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c23 (q : Σ d : Fin (38 - 23 - 2), Fin (38 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨23, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨8704, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c24 (q : Σ d : Fin (38 - 24 - 2), Fin (38 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨24, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10651, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13314, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c25 (q : Σ d : Fin (38 - 25 - 2), Fin (38 - (25 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨25, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c26 (q : Σ d : Fin (38 - 26 - 2), Fin (38 - (26 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨26, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c27 (q : Σ d : Fin (38 - 27 - 2), Fin (38 - (27 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨27, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c28 (q : Σ d : Fin (38 - 28 - 2), Fin (38 - (28 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨28, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c29 (q : Σ d : Fin (38 - 29 - 2), Fin (38 - (29 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨29, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c30 (q : Σ d : Fin (38 - 30 - 2), Fin (38 - (30 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨30, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c31 (q : Σ d : Fin (38 - 31 - 2), Fin (38 - (31 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨31, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c32 (q : Σ d : Fin (38 - 32 - 2), Fin (38 - (32 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨32, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c33 (q : Σ d : Fin (38 - 33 - 2), Fin (38 - (33 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨33, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c34 (q : Σ d : Fin (38 - 34 - 2), Fin (38 - (34 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨34, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a10_b05_c35 (q : Σ d : Fin (38 - 35 - 2), Fin (38 - (35 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) ⟨(⟨35, by norm_num⟩ : Fin (38 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a10_b05 (q : IncreasingThree 38) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨10, by norm_num⟩ : Fin 55) (⟨16, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a10_b05_c00 q
  · exact certificate105_a10_b05_c01 q
  · exact certificate105_a10_b05_c02 q
  · exact certificate105_a10_b05_c03 q
  · exact certificate105_a10_b05_c04 q
  · exact certificate105_a10_b05_c05 q
  · exact certificate105_a10_b05_c06 q
  · exact certificate105_a10_b05_c07 q
  · exact certificate105_a10_b05_c08 q
  · exact certificate105_a10_b05_c09 q
  · exact certificate105_a10_b05_c10 q
  · exact certificate105_a10_b05_c11 q
  · exact certificate105_a10_b05_c12 q
  · exact certificate105_a10_b05_c13 q
  · exact certificate105_a10_b05_c14 q
  · exact certificate105_a10_b05_c15 q
  · exact certificate105_a10_b05_c16 q
  · exact certificate105_a10_b05_c17 q
  · exact certificate105_a10_b05_c18 q
  · exact certificate105_a10_b05_c19 q
  · exact certificate105_a10_b05_c20 q
  · exact certificate105_a10_b05_c21 q
  · exact certificate105_a10_b05_c22 q
  · exact certificate105_a10_b05_c23 q
  · exact certificate105_a10_b05_c24 q
  · exact certificate105_a10_b05_c25 q
  · exact certificate105_a10_b05_c26 q
  · exact certificate105_a10_b05_c27 q
  · exact certificate105_a10_b05_c28 q
  · exact certificate105_a10_b05_c29 q
  · exact certificate105_a10_b05_c30 q
  · exact certificate105_a10_b05_c31 q
  · exact certificate105_a10_b05_c32 q
  · exact certificate105_a10_b05_c33 q
  · exact certificate105_a10_b05_c34 q
  · exact certificate105_a10_b05_c35 q

end MinModulus.SHCSixExceptionalCertificate.Generated
