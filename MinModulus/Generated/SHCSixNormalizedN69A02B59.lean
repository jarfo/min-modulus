import MinModulus.Generated.SHCSixNormalizedN69A02B57

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate69_a02_b59_c00 (q : Σ d : Fin (4 - 0 - 2), Fin (4 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 4 64 ⟨(⟨0, by norm_num⟩ : Fin (4 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a02_b59_c01 (q : Σ d : Fin (4 - 1 - 2), Fin (4 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 4 64 ⟨(⟨1, by norm_num⟩ : Fin (4 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate69_a02_b59 (q : IncreasingThree 4) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 4 64 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate69_a02_b59_c00 q
  · exact certificate69_a02_b59_c01 q

end MinModulus.SHCSixCertificate.Generated
