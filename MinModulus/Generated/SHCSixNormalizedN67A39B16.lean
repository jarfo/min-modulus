import MinModulus.Generated.SHCSixNormalizedN67A39B14

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a39_b16_c00 (q : Σ d : Fin (8 - 0 - 2), Fin (8 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 41 58 ⟨(⟨0, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a39_b16_c01 (q : Σ d : Fin (8 - 1 - 2), Fin (8 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 41 58 ⟨(⟨1, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  exact ⟨5298, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a39_b16_c02 (q : Σ d : Fin (8 - 2 - 2), Fin (8 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 41 58 ⟨(⟨2, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a39_b16_c03 (q : Σ d : Fin (8 - 3 - 2), Fin (8 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 41 58 ⟨(⟨3, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a39_b16_c04 (q : Σ d : Fin (8 - 4 - 2), Fin (8 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 41 58 ⟨(⟨4, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  exact ⟨6019, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a39_b16_c05 (q : Σ d : Fin (8 - 5 - 2), Fin (8 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 41 58 ⟨(⟨5, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a39_b16 (q : IncreasingThree 8) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 41 58 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a39_b16_c00 q
  · exact certificate67_a39_b16_c01 q
  · exact certificate67_a39_b16_c02 q
  · exact certificate67_a39_b16_c03 q
  · exact certificate67_a39_b16_c04 q
  · exact certificate67_a39_b16_c05 q

end MinModulus.SHCSixCertificate.Generated
