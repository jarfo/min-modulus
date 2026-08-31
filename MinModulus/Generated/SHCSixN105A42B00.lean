import MinModulus.Generated.SHCSixN105A41B08

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a42_b00_c00 (q : Σ d : Fin (11 - 0 - 2), Fin (11 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨42, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨259, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a42_b00_c01 (q : Σ d : Fin (11 - 1 - 2), Fin (11 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨42, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a42_b00_c02 (q : Σ d : Fin (11 - 2 - 2), Fin (11 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨42, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨259, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a42_b00_c03 (q : Σ d : Fin (11 - 3 - 2), Fin (11 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨42, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨259, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a42_b00_c04 (q : Σ d : Fin (11 - 4 - 2), Fin (11 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨42, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨259, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a42_b00_c05 (q : Σ d : Fin (11 - 5 - 2), Fin (11 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨42, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨259, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a42_b00_c06 (q : Σ d : Fin (11 - 6 - 2), Fin (11 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨42, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨259, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a42_b00_c07 (q : Σ d : Fin (11 - 7 - 2), Fin (11 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨42, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨259, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a42_b00_c08 (q : Σ d : Fin (11 - 8 - 2), Fin (11 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨42, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a42_b00 (q : IncreasingThree 11) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨42, by norm_num⟩ : Fin 55) (⟨43, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a42_b00_c00 q
  · exact certificate105_a42_b00_c01 q
  · exact certificate105_a42_b00_c02 q
  · exact certificate105_a42_b00_c03 q
  · exact certificate105_a42_b00_c04 q
  · exact certificate105_a42_b00_c05 q
  · exact certificate105_a42_b00_c06 q
  · exact certificate105_a42_b00_c07 q
  · exact certificate105_a42_b00_c08 q

end MinModulus.SHCSixExceptionalCertificate.Generated
