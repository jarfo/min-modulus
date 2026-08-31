import MinModulus.Generated.SHCSixN105A17B22

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a17_b24_c00 (q : Σ d : Fin (12 - 0 - 2), Fin (12 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨17, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a17_b24_c01 (q : Σ d : Fin (12 - 1 - 2), Fin (12 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨17, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨27, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1039, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a17_b24_c02 (q : Σ d : Fin (12 - 2 - 2), Fin (12 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨17, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11779, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a17_b24_c03 (q : Σ d : Fin (12 - 3 - 2), Fin (12 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨17, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a17_b24_c04 (q : Σ d : Fin (12 - 4 - 2), Fin (12 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨17, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨15, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a17_b24_c05 (q : Σ d : Fin (12 - 5 - 2), Fin (12 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨17, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨5635, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a17_b24_c06 (q : Σ d : Fin (12 - 6 - 2), Fin (12 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨17, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2961, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13710, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a17_b24_c07 (q : Σ d : Fin (12 - 7 - 2), Fin (12 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨17, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨13710, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a17_b24_c08 (q : Σ d : Fin (12 - 8 - 2), Fin (12 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨17, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨13326, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a17_b24_c09 (q : Σ d : Fin (12 - 9 - 2), Fin (12 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨17, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a17_b24 (q : IncreasingThree 12) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨17, by norm_num⟩ : Fin 55) (⟨42, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a17_b24_c00 q
  · exact certificate105_a17_b24_c01 q
  · exact certificate105_a17_b24_c02 q
  · exact certificate105_a17_b24_c03 q
  · exact certificate105_a17_b24_c04 q
  · exact certificate105_a17_b24_c05 q
  · exact certificate105_a17_b24_c06 q
  · exact certificate105_a17_b24_c07 q
  · exact certificate105_a17_b24_c08 q
  · exact certificate105_a17_b24_c09 q

end MinModulus.SHCSixExceptionalCertificate.Generated
