import MinModulus.Generated.SHCSixN105A21B05

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a21_b07_c00 (q : Σ d : Fin (25 - 0 - 2), Fin (25 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11008, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12592, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11011, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11017, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2449, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
  · fin_cases e
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1062, by decide, by decide⟩
    · exact ⟨2705, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11825, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c01 (q : Σ d : Fin (25 - 1 - 2), Fin (25 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c02 (q : Σ d : Fin (25 - 2 - 2), Fin (25 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c03 (q : Σ d : Fin (25 - 3 - 2), Fin (25 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨535, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12592, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10625, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨566, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3465, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c04 (q : Σ d : Fin (25 - 4 - 2), Fin (25 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c05 (q : Σ d : Fin (25 - 5 - 2), Fin (25 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨7936, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c06 (q : Σ d : Fin (25 - 6 - 2), Fin (25 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨7938, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c07 (q : Σ d : Fin (25 - 7 - 2), Fin (25 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨2449, by decide, by decide⟩
    · exact ⟨945, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨2689, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨42, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨2689, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11825, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c08 (q : Σ d : Fin (25 - 8 - 2), Fin (25 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨5251, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c09 (q : Σ d : Fin (25 - 9 - 2), Fin (25 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2817, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1062, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨3587, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨945, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨3587, by decide, by decide⟩
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨1697, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12592, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨3465, by decide, by decide⟩
    · exact ⟨1062, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6068, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6410, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c10 (q : Σ d : Fin (25 - 10 - 2), Fin (25 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5347, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c11 (q : Σ d : Fin (25 - 11 - 2), Fin (25 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨6065, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c12 (q : Σ d : Fin (25 - 12 - 2), Fin (25 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨7553, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c13 (q : Σ d : Fin (25 - 13 - 2), Fin (25 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨7169, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c14 (q : Σ d : Fin (25 - 14 - 2), Fin (25 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨14466, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14082, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6410, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c15 (q : Σ d : Fin (25 - 15 - 2), Fin (25 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨417, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨2054, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1062, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12592, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c16 (q : Σ d : Fin (25 - 16 - 2), Fin (25 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13313, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c17 (q : Σ d : Fin (25 - 17 - 2), Fin (25 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c18 (q : Σ d : Fin (25 - 18 - 2), Fin (25 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13319, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c19 (q : Σ d : Fin (25 - 19 - 2), Fin (25 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c20 (q : Σ d : Fin (25 - 20 - 2), Fin (25 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨20, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c21 (q : Σ d : Fin (25 - 21 - 2), Fin (25 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨21, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b07_c22 (q : Σ d : Fin (25 - 22 - 2), Fin (25 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) ⟨(⟨22, by norm_num⟩ : Fin (25 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a21_b07 (q : IncreasingThree 25) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨29, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a21_b07_c00 q
  · exact certificate105_a21_b07_c01 q
  · exact certificate105_a21_b07_c02 q
  · exact certificate105_a21_b07_c03 q
  · exact certificate105_a21_b07_c04 q
  · exact certificate105_a21_b07_c05 q
  · exact certificate105_a21_b07_c06 q
  · exact certificate105_a21_b07_c07 q
  · exact certificate105_a21_b07_c08 q
  · exact certificate105_a21_b07_c09 q
  · exact certificate105_a21_b07_c10 q
  · exact certificate105_a21_b07_c11 q
  · exact certificate105_a21_b07_c12 q
  · exact certificate105_a21_b07_c13 q
  · exact certificate105_a21_b07_c14 q
  · exact certificate105_a21_b07_c15 q
  · exact certificate105_a21_b07_c16 q
  · exact certificate105_a21_b07_c17 q
  · exact certificate105_a21_b07_c18 q
  · exact certificate105_a21_b07_c19 q
  · exact certificate105_a21_b07_c20 q
  · exact certificate105_a21_b07_c21 q
  · exact certificate105_a21_b07_c22 q

end MinModulus.SHCSixExceptionalCertificate.Generated
