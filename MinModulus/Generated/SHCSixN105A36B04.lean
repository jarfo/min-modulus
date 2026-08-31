import MinModulus.Generated.SHCSixN105A36B02

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a36_b04_c00 (q : Σ d : Fin (13 - 0 - 2), Fin (13 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨36, by norm_num⟩ : Fin 55) (⟨41, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8418, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a36_b04_c01 (q : Σ d : Fin (13 - 1 - 2), Fin (13 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨36, by norm_num⟩ : Fin 55) (⟨41, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3213, by decide, by decide⟩

private theorem certificate105_a36_b04_c02 (q : Σ d : Fin (13 - 2 - 2), Fin (13 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨36, by norm_num⟩ : Fin 55) (⟨41, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1539, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13324, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5300, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a36_b04_c03 (q : Σ d : Fin (13 - 3 - 2), Fin (13 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨36, by norm_num⟩ : Fin 55) (⟨41, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨8322, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a36_b04_c04 (q : Σ d : Fin (13 - 4 - 2), Fin (13 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨36, by norm_num⟩ : Fin 55) (⟨41, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨7938, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a36_b04_c05 (q : Σ d : Fin (13 - 5 - 2), Fin (13 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨36, by norm_num⟩ : Fin 55) (⟨41, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5300, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a36_b04_c06 (q : Σ d : Fin (13 - 6 - 2), Fin (13 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨36, by norm_num⟩ : Fin 55) (⟨41, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨7944, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a36_b04_c07 (q : Σ d : Fin (13 - 7 - 2), Fin (13 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨36, by norm_num⟩ : Fin 55) (⟨41, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a36_b04_c08 (q : Σ d : Fin (13 - 8 - 2), Fin (13 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨36, by norm_num⟩ : Fin 55) (⟨41, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a36_b04_c09 (q : Σ d : Fin (13 - 9 - 2), Fin (13 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨36, by norm_num⟩ : Fin 55) (⟨41, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a36_b04_c10 (q : Σ d : Fin (13 - 10 - 2), Fin (13 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨36, by norm_num⟩ : Fin 55) (⟨41, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11419, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a36_b04 (q : IncreasingThree 13) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨36, by norm_num⟩ : Fin 55) (⟨41, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a36_b04_c00 q
  · exact certificate105_a36_b04_c01 q
  · exact certificate105_a36_b04_c02 q
  · exact certificate105_a36_b04_c03 q
  · exact certificate105_a36_b04_c04 q
  · exact certificate105_a36_b04_c05 q
  · exact certificate105_a36_b04_c06 q
  · exact certificate105_a36_b04_c07 q
  · exact certificate105_a36_b04_c08 q
  · exact certificate105_a36_b04_c09 q
  · exact certificate105_a36_b04_c10 q

end MinModulus.SHCSixExceptionalCertificate.Generated
