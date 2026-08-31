import MinModulus.Generated.SHCSixN105A34B12

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a34_b14_c00 (q : Σ d : Fin (5 - 0 - 2), Fin (5 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨49, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (5 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1029, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a34_b14_c01 (q : Σ d : Fin (5 - 1 - 2), Fin (5 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨49, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (5 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a34_b14_c02 (q : Σ d : Fin (5 - 2 - 2), Fin (5 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨49, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (5 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨12163, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a34_b14 (q : IncreasingThree 5) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨34, by norm_num⟩ : Fin 55) (⟨49, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a34_b14_c00 q
  · exact certificate105_a34_b14_c01 q
  · exact certificate105_a34_b14_c02 q

end MinModulus.SHCSixExceptionalCertificate.Generated
