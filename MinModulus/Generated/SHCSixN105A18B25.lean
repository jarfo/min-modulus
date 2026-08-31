import MinModulus.Generated.SHCSixN105A18B23

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a18_b25_c00 (q : Σ d : Fin (10 - 0 - 2), Fin (10 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨18688, by decide, by decide⟩
    · exact ⟨2961, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨929, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨929, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a18_b25_c01 (q : Σ d : Fin (10 - 1 - 2), Fin (10 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2961, by decide, by decide⟩
    · exact ⟨59, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨54, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a18_b25_c02 (q : Σ d : Fin (10 - 2 - 2), Fin (10 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a18_b25_c03 (q : Σ d : Fin (10 - 3 - 2), Fin (10 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a18_b25_c04 (q : Σ d : Fin (10 - 4 - 2), Fin (10 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  exact ⟨9472, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a18_b25_c05 (q : Σ d : Fin (10 - 5 - 2), Fin (10 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a18_b25_c06 (q : Σ d : Fin (10 - 6 - 2), Fin (10 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  exact ⟨7566, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a18_b25_c07 (q : Σ d : Fin (10 - 7 - 2), Fin (10 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a18_b25 (q : IncreasingThree 10) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨18, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a18_b25_c00 q
  · exact certificate105_a18_b25_c01 q
  · exact certificate105_a18_b25_c02 q
  · exact certificate105_a18_b25_c03 q
  · exact certificate105_a18_b25_c04 q
  · exact certificate105_a18_b25_c05 q
  · exact certificate105_a18_b25_c06 q
  · exact certificate105_a18_b25_c07 q

end MinModulus.SHCSixExceptionalCertificate.Generated
