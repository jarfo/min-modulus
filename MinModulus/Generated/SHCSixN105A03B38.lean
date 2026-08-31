import MinModulus.Generated.SHCSixN105A03B36

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a03_b38_c00 (q : Σ d : Fin (12 - 0 - 2), Fin (12 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b38_c01 (q : Σ d : Fin (12 - 1 - 2), Fin (12 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b38_c02 (q : Σ d : Fin (12 - 2 - 2), Fin (12 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b38_c03 (q : Σ d : Fin (12 - 3 - 2), Fin (12 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b38_c04 (q : Σ d : Fin (12 - 4 - 2), Fin (12 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨19, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b38_c05 (q : Σ d : Fin (12 - 5 - 2), Fin (12 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b38_c06 (q : Σ d : Fin (12 - 6 - 2), Fin (12 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b38_c07 (q : Σ d : Fin (12 - 7 - 2), Fin (12 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b38_c08 (q : Σ d : Fin (12 - 8 - 2), Fin (12 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b38_c09 (q : Σ d : Fin (12 - 9 - 2), Fin (12 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a03_b38 (q : IncreasingThree 12) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a03_b38_c00 q
  · exact certificate105_a03_b38_c01 q
  · exact certificate105_a03_b38_c02 q
  · exact certificate105_a03_b38_c03 q
  · exact certificate105_a03_b38_c04 q
  · exact certificate105_a03_b38_c05 q
  · exact certificate105_a03_b38_c06 q
  · exact certificate105_a03_b38_c07 q
  · exact certificate105_a03_b38_c08 q
  · exact certificate105_a03_b38_c09 q

end MinModulus.SHCSixExceptionalCertificate.Generated
