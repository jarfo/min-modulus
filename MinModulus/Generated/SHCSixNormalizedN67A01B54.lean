import MinModulus.Generated.SHCSixNormalizedN67A01B52

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a01_b54_c00 (q : Σ d : Fin (8 - 0 - 2), Fin (8 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 3 58 ⟨(⟨0, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a01_b54_c01 (q : Σ d : Fin (8 - 1 - 2), Fin (8 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 3 58 ⟨(⟨1, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a01_b54_c02 (q : Σ d : Fin (8 - 2 - 2), Fin (8 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 3 58 ⟨(⟨2, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a01_b54_c03 (q : Σ d : Fin (8 - 3 - 2), Fin (8 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 3 58 ⟨(⟨3, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  exact ⟨519, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a01_b54_c04 (q : Σ d : Fin (8 - 4 - 2), Fin (8 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 3 58 ⟨(⟨4, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  exact ⟨11, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a01_b54_c05 (q : Σ d : Fin (8 - 5 - 2), Fin (8 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 3 58 ⟨(⟨5, by norm_num⟩ : Fin (8 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a01_b54 (q : IncreasingThree 8) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 3 58 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a01_b54_c00 q
  · exact certificate67_a01_b54_c01 q
  · exact certificate67_a01_b54_c02 q
  · exact certificate67_a01_b54_c03 q
  · exact certificate67_a01_b54_c04 q
  · exact certificate67_a01_b54_c05 q

end MinModulus.SHCSixCertificate.Generated
