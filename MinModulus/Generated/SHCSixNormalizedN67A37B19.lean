import MinModulus.Generated.SHCSixNormalizedN67A37B17

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a37_b19_c00 (q : Σ d : Fin (7 - 0 - 2), Fin (7 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 39 59 ⟨(⟨0, by norm_num⟩ : Fin (7 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a37_b19_c01 (q : Σ d : Fin (7 - 1 - 2), Fin (7 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 39 59 ⟨(⟨1, by norm_num⟩ : Fin (7 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11779, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a37_b19_c02 (q : Σ d : Fin (7 - 2 - 2), Fin (7 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 39 59 ⟨(⟨2, by norm_num⟩ : Fin (7 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a37_b19_c03 (q : Σ d : Fin (7 - 3 - 2), Fin (7 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 39 59 ⟨(⟨3, by norm_num⟩ : Fin (7 - 2)), q⟩) code = true := by
  exact ⟨5635, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a37_b19_c04 (q : Σ d : Fin (7 - 4 - 2), Fin (7 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 39 59 ⟨(⟨4, by norm_num⟩ : Fin (7 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a37_b19 (q : IncreasingThree 7) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 39 59 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a37_b19_c00 q
  · exact certificate67_a37_b19_c01 q
  · exact certificate67_a37_b19_c02 q
  · exact certificate67_a37_b19_c03 q
  · exact certificate67_a37_b19_c04 q

end MinModulus.SHCSixCertificate.Generated
