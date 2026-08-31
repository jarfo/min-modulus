import MinModulus.Generated.SHCSixN105A23B13

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a23_b15_c00 (q : Σ d : Fin (15 - 0 - 2), Fin (15 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨23, by norm_num⟩ : Fin 55) (⟨39, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨5251, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a23_b15_c01 (q : Σ d : Fin (15 - 1 - 2), Fin (15 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨23, by norm_num⟩ : Fin 55) (⟨39, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a23_b15_c02 (q : Σ d : Fin (15 - 2 - 2), Fin (15 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨23, by norm_num⟩ : Fin 55) (⟨39, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5300, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5347, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a23_b15_c03 (q : Σ d : Fin (15 - 3 - 2), Fin (15 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨23, by norm_num⟩ : Fin 55) (⟨39, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨54, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10625, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a23_b15_c04 (q : Σ d : Fin (15 - 4 - 2), Fin (15 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨23, by norm_num⟩ : Fin 55) (⟨39, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨14, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a23_b15_c05 (q : Σ d : Fin (15 - 5 - 2), Fin (15 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨23, by norm_num⟩ : Fin 55) (⟨39, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10625, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a23_b15_c06 (q : Σ d : Fin (15 - 6 - 2), Fin (15 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨23, by norm_num⟩ : Fin 55) (⟨39, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a23_b15_c07 (q : Σ d : Fin (15 - 7 - 2), Fin (15 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨23, by norm_num⟩ : Fin 55) (⟨39, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨9472, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a23_b15_c08 (q : Σ d : Fin (15 - 8 - 2), Fin (15 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨23, by norm_num⟩ : Fin 55) (⟨39, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨7553, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a23_b15_c09 (q : Σ d : Fin (15 - 9 - 2), Fin (15 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨23, by norm_num⟩ : Fin 55) (⟨39, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨19553, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a23_b15_c10 (q : Σ d : Fin (15 - 10 - 2), Fin (15 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨23, by norm_num⟩ : Fin 55) (⟨39, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  exact ⟨7169, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a23_b15_c11 (q : Σ d : Fin (15 - 11 - 2), Fin (15 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨23, by norm_num⟩ : Fin 55) (⟨39, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11058, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a23_b15_c12 (q : Σ d : Fin (15 - 12 - 2), Fin (15 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨23, by norm_num⟩ : Fin 55) (⟨39, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (15 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨13710, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a23_b15 (q : IncreasingThree 15) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨23, by norm_num⟩ : Fin 55) (⟨39, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a23_b15_c00 q
  · exact certificate105_a23_b15_c01 q
  · exact certificate105_a23_b15_c02 q
  · exact certificate105_a23_b15_c03 q
  · exact certificate105_a23_b15_c04 q
  · exact certificate105_a23_b15_c05 q
  · exact certificate105_a23_b15_c06 q
  · exact certificate105_a23_b15_c07 q
  · exact certificate105_a23_b15_c08 q
  · exact certificate105_a23_b15_c09 q
  · exact certificate105_a23_b15_c10 q
  · exact certificate105_a23_b15_c11 q
  · exact certificate105_a23_b15_c12 q

end MinModulus.SHCSixExceptionalCertificate.Generated
