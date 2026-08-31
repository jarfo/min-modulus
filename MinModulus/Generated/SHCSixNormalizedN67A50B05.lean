import MinModulus.Generated.SHCSixNormalizedN67A50B03

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a50_b05_c00 (q : Σ d : Fin (8 - 0 - 2), Fin (8 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 52 58 ⟨(⟨0, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a50_b05_c01 (q : Σ d : Fin (8 - 1 - 2), Fin (8 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 52 58 ⟨(⟨1, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a50_b05_c02 (q : Σ d : Fin (8 - 2 - 2), Fin (8 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 52 58 ⟨(⟨2, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a50_b05_c03 (q : Σ d : Fin (8 - 3 - 2), Fin (8 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 52 58 ⟨(⟨3, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a50_b05_c04 (q : Σ d : Fin (8 - 4 - 2), Fin (8 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 52 58 ⟨(⟨4, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a50_b05_c05 (q : Σ d : Fin (8 - 5 - 2), Fin (8 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 52 58 ⟨(⟨5, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  exact ⟨7938, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a50_b05 (q : IncreasingThree 8) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 52 58 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a50_b05_c00 q
  · exact certificate67_a50_b05_c01 q
  · exact certificate67_a50_b05_c02 q
  · exact certificate67_a50_b05_c03 q
  · exact certificate67_a50_b05_c04 q
  · exact certificate67_a50_b05_c05 q

end MinModulus.SHCSixCertificate.Generated
