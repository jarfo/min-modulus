import MinModulus.Generated.SHCSixNormalizedN69A55B04

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate69_a55_b06_c00 (q : Σ d : Fin (4 - 0 - 2), Fin (4 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 57 64 ⟨(⟨0, by norm_num⟩ : Fin (4 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a55_b06_c01 (q : Σ d : Fin (4 - 1 - 2), Fin (4 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 57 64 ⟨(⟨1, by norm_num⟩ : Fin (4 - 2)), q⟩) code = true := by
  exact ⟨5275, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate69_a55_b06 (q : IncreasingThree 4) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 57 64 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate69_a55_b06_c00 q
  · exact certificate69_a55_b06_c01 q

end MinModulus.SHCSixCertificate.Generated
