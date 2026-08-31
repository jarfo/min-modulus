import MinModulus.Generated.SHCSixN105A35B06

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a35_b08_c00 (q : Σ d : Fin (10 - 0 - 2), Fin (10 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  exact ⟨4867, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b08_c01 (q : Σ d : Fin (10 - 1 - 2), Fin (10 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5300, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11394, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b08_c02 (q : Σ d : Fin (10 - 2 - 2), Fin (10 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8418, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b08_c03 (q : Σ d : Fin (10 - 3 - 2), Fin (10 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11788, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b08_c04 (q : Σ d : Fin (10 - 4 - 2), Fin (10 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b08_c05 (q : Σ d : Fin (10 - 5 - 2), Fin (10 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b08_c06 (q : Σ d : Fin (10 - 6 - 2), Fin (10 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  exact ⟨8322, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a35_b08_c07 (q : Σ d : Fin (10 - 7 - 2), Fin (10 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a35_b08 (q : IncreasingThree 10) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨35, by norm_num⟩ : Fin 55) (⟨44, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a35_b08_c00 q
  · exact certificate105_a35_b08_c01 q
  · exact certificate105_a35_b08_c02 q
  · exact certificate105_a35_b08_c03 q
  · exact certificate105_a35_b08_c04 q
  · exact certificate105_a35_b08_c05 q
  · exact certificate105_a35_b08_c06 q
  · exact certificate105_a35_b08_c07 q

end MinModulus.SHCSixExceptionalCertificate.Generated
