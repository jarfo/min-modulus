import MinModulus.Generated.SHCSixN105A29B02

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a29_b04_c00 (q : Σ d : Fin (20 - 0 - 2), Fin (20 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c01 (q : Σ d : Fin (20 - 1 - 2), Fin (20 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨7577, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c02 (q : Σ d : Fin (20 - 2 - 2), Fin (20 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨177, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨2689, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2961, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨14848, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2689, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2433, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨945, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨54, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a29_b04_c03 (q : Σ d : Fin (20 - 3 - 2), Fin (20 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨6499, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11779, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c04 (q : Σ d : Fin (20 - 4 - 2), Fin (20 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2689, by decide, by decide⟩
    · exact ⟨169, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨1315, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨3465, by decide, by decide⟩
    · exact ⟨929, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨14272, by decide, by decide⟩
    · exact ⟨2201, by decide, by decide⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨54, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5300, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c05 (q : Σ d : Fin (20 - 5 - 2), Fin (20 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3465, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨2433, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c06 (q : Σ d : Fin (20 - 6 - 2), Fin (20 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨7566, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c07 (q : Σ d : Fin (20 - 7 - 2), Fin (20 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14082, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c08 (q : Σ d : Fin (20 - 8 - 2), Fin (20 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c09 (q : Σ d : Fin (20 - 9 - 2), Fin (20 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨15, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c10 (q : Σ d : Fin (20 - 10 - 2), Fin (20 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨6019, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c11 (q : Σ d : Fin (20 - 11 - 2), Fin (20 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2078, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c12 (q : Σ d : Fin (20 - 12 - 2), Fin (20 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨897, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c13 (q : Σ d : Fin (20 - 13 - 2), Fin (20 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c14 (q : Σ d : Fin (20 - 14 - 2), Fin (20 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c15 (q : Σ d : Fin (20 - 15 - 2), Fin (20 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c16 (q : Σ d : Fin (20 - 16 - 2), Fin (20 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a29_b04_c17 (q : Σ d : Fin (20 - 17 - 2), Fin (20 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (20 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a29_b04 (q : IncreasingThree 20) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨29, by norm_num⟩ : Fin 55) (⟨34, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a29_b04_c00 q
  · exact certificate105_a29_b04_c01 q
  · exact certificate105_a29_b04_c02 q
  · exact certificate105_a29_b04_c03 q
  · exact certificate105_a29_b04_c04 q
  · exact certificate105_a29_b04_c05 q
  · exact certificate105_a29_b04_c06 q
  · exact certificate105_a29_b04_c07 q
  · exact certificate105_a29_b04_c08 q
  · exact certificate105_a29_b04_c09 q
  · exact certificate105_a29_b04_c10 q
  · exact certificate105_a29_b04_c11 q
  · exact certificate105_a29_b04_c12 q
  · exact certificate105_a29_b04_c13 q
  · exact certificate105_a29_b04_c14 q
  · exact certificate105_a29_b04_c15 q
  · exact certificate105_a29_b04_c16 q
  · exact certificate105_a29_b04_c17 q

end MinModulus.SHCSixExceptionalCertificate.Generated
