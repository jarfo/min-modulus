import MinModulus.Generated.SHCSixNormalizedN67A04B50

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a04_b52_c00 (q : Σ d : Fin (7 - 0 - 2), Fin (7 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 59 ⟨(⟨0, by norm_num⟩ : Fin (7 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b52_c01 (q : Σ d : Fin (7 - 1 - 2), Fin (7 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 59 ⟨(⟨1, by norm_num⟩ : Fin (7 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b52_c02 (q : Σ d : Fin (7 - 2 - 2), Fin (7 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 59 ⟨(⟨2, by norm_num⟩ : Fin (7 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b52_c03 (q : Σ d : Fin (7 - 3 - 2), Fin (7 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 59 ⟨(⟨3, by norm_num⟩ : Fin (7 - 2)), q⟩) code = true := by
  exact ⟨6448, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a04_b52_c04 (q : Σ d : Fin (7 - 4 - 2), Fin (7 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 59 ⟨(⟨4, by norm_num⟩ : Fin (7 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a04_b52 (q : IncreasingThree 7) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 6 59 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a04_b52_c00 q
  · exact certificate67_a04_b52_c01 q
  · exact certificate67_a04_b52_c02 q
  · exact certificate67_a04_b52_c03 q
  · exact certificate67_a04_b52_c04 q

end MinModulus.SHCSixCertificate.Generated
