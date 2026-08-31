import MinModulus.Generated.SHCSixNormalizedN67A12B38

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a12_b40_c00 (q : Σ d : Fin (11 - 0 - 2), Fin (11 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 14 55 ⟨(⟨0, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a12_b40_c01 (q : Σ d : Fin (11 - 1 - 2), Fin (11 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 14 55 ⟨(⟨1, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨6400, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a12_b40_c02 (q : Σ d : Fin (11 - 2 - 2), Fin (11 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 14 55 ⟨(⟨2, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨6400, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a12_b40_c03 (q : Σ d : Fin (11 - 3 - 2), Fin (11 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 14 55 ⟨(⟨3, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨6400, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a12_b40_c04 (q : Σ d : Fin (11 - 4 - 2), Fin (11 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 14 55 ⟨(⟨4, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨6400, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a12_b40_c05 (q : Σ d : Fin (11 - 5 - 2), Fin (11 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 14 55 ⟨(⟨5, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨6400, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a12_b40_c06 (q : Σ d : Fin (11 - 6 - 2), Fin (11 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 14 55 ⟨(⟨6, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨6400, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a12_b40_c07 (q : Σ d : Fin (11 - 7 - 2), Fin (11 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 14 55 ⟨(⟨7, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨6400, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a12_b40_c08 (q : Σ d : Fin (11 - 8 - 2), Fin (11 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 14 55 ⟨(⟨8, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨15, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a12_b40 (q : IncreasingThree 11) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 14 55 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a12_b40_c00 q
  · exact certificate67_a12_b40_c01 q
  · exact certificate67_a12_b40_c02 q
  · exact certificate67_a12_b40_c03 q
  · exact certificate67_a12_b40_c04 q
  · exact certificate67_a12_b40_c05 q
  · exact certificate67_a12_b40_c06 q
  · exact certificate67_a12_b40_c07 q
  · exact certificate67_a12_b40_c08 q

end MinModulus.SHCSixCertificate.Generated
