import MinModulus.Generated.SHCSixN105A21B16

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a21_b18_c00 (q : Σ d : Fin (14 - 0 - 2), Fin (14 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1029, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10241, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1039, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5346, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b18_c01 (q : Σ d : Fin (14 - 1 - 2), Fin (14 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b18_c02 (q : Σ d : Fin (14 - 2 - 2), Fin (14 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  exact ⟨7169, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b18_c03 (q : Σ d : Fin (14 - 3 - 2), Fin (14 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11825, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5346, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b18_c04 (q : Σ d : Fin (14 - 4 - 2), Fin (14 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  exact ⟨15, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b18_c05 (q : Σ d : Fin (14 - 5 - 2), Fin (14 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  exact ⟨14, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b18_c06 (q : Σ d : Fin (14 - 6 - 2), Fin (14 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5346, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b18_c07 (q : Σ d : Fin (14 - 7 - 2), Fin (14 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  exact ⟨897, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b18_c08 (q : Σ d : Fin (14 - 8 - 2), Fin (14 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5346, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b18_c09 (q : Σ d : Fin (14 - 9 - 2), Fin (14 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  exact ⟨9472, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b18_c10 (q : Σ d : Fin (14 - 10 - 2), Fin (14 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨5346, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a21_b18_c11 (q : Σ d : Fin (14 - 11 - 2), Fin (14 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  exact ⟨5298, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a21_b18 (q : IncreasingThree 14) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨21, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a21_b18_c00 q
  · exact certificate105_a21_b18_c01 q
  · exact certificate105_a21_b18_c02 q
  · exact certificate105_a21_b18_c03 q
  · exact certificate105_a21_b18_c04 q
  · exact certificate105_a21_b18_c05 q
  · exact certificate105_a21_b18_c06 q
  · exact certificate105_a21_b18_c07 q
  · exact certificate105_a21_b18_c08 q
  · exact certificate105_a21_b18_c09 q
  · exact certificate105_a21_b18_c10 q
  · exact certificate105_a21_b18_c11 q

end MinModulus.SHCSixExceptionalCertificate.Generated
