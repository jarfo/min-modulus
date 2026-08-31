import MinModulus.Generated.SHCSixN105A18B22

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a18_b24_c00 (q : Σ d : Fin (11 - 0 - 2), Fin (11 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1029, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2433, by decide, by decide⟩
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10639, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a18_b24_c01 (q : Σ d : Fin (11 - 1 - 2), Fin (11 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a18_b24_c02 (q : Σ d : Fin (11 - 2 - 2), Fin (11 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨14, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a18_b24_c03 (q : Σ d : Fin (11 - 3 - 2), Fin (11 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2078, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a18_b24_c04 (q : Σ d : Fin (11 - 4 - 2), Fin (11 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨897, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a18_b24_c05 (q : Σ d : Fin (11 - 5 - 2), Fin (11 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a18_b24_c06 (q : Σ d : Fin (11 - 6 - 2), Fin (11 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨9472, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a18_b24_c07 (q : Σ d : Fin (11 - 7 - 2), Fin (11 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2945, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a18_b24_c08 (q : Σ d : Fin (11 - 8 - 2), Fin (11 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

theorem certificate105_a18_b24 (q : IncreasingThree 11) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a18_b24_c00 q
  · exact certificate105_a18_b24_c01 q
  · exact certificate105_a18_b24_c02 q
  · exact certificate105_a18_b24_c03 q
  · exact certificate105_a18_b24_c04 q
  · exact certificate105_a18_b24_c05 q
  · exact certificate105_a18_b24_c06 q
  · exact certificate105_a18_b24_c07 q
  · exact certificate105_a18_b24_c08 q

end MinModulus.SHCSixExceptionalCertificate.Generated
