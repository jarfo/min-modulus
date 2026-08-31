import MinModulus.Generated.SHCSixN105A35B02

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a35_b04_c00 (q : Σ d : Fin (14 - 0 - 2), Fin (14 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1029, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6883, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b04_c01 (q : Σ d : Fin (14 - 1 - 2), Fin (14 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b04_c02 (q : Σ d : Fin (14 - 2 - 2), Fin (14 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  exact ⟨8322, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b04_c03 (q : Σ d : Fin (14 - 3 - 2), Fin (14 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3213, by decide, by decide⟩

private theorem certificate105_a35_b04_c04 (q : Σ d : Fin (14 - 4 - 2), Fin (14 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  exact ⟨7938, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b04_c05 (q : Σ d : Fin (14 - 5 - 2), Fin (14 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  exact ⟨7944, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b04_c06 (q : Σ d : Fin (14 - 6 - 2), Fin (14 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b04_c07 (q : Σ d : Fin (14 - 7 - 2), Fin (14 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b04_c08 (q : Σ d : Fin (14 - 8 - 2), Fin (14 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b04_c09 (q : Σ d : Fin (14 - 9 - 2), Fin (14 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b04_c10 (q : Σ d : Fin (14 - 10 - 2), Fin (14 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b04_c11 (q : Σ d : Fin (14 - 11 - 2), Fin (14 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (14 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a35_b04 (q : IncreasingThree 14) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨40, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a35_b04_c00 q
  · exact certificate105_a35_b04_c01 q
  · exact certificate105_a35_b04_c02 q
  · exact certificate105_a35_b04_c03 q
  · exact certificate105_a35_b04_c04 q
  · exact certificate105_a35_b04_c05 q
  · exact certificate105_a35_b04_c06 q
  · exact certificate105_a35_b04_c07 q
  · exact certificate105_a35_b04_c08 q
  · exact certificate105_a35_b04_c09 q
  · exact certificate105_a35_b04_c10 q
  · exact certificate105_a35_b04_c11 q

end MinModulus.SHCSixExceptionalCertificate.Generated
