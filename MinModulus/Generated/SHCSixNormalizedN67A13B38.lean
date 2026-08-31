import MinModulus.Generated.SHCSixNormalizedN67A13B36

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a13_b38_c00 (q : Σ d : Fin (12 - 0 - 2), Fin (12 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 15 54 ⟨(⟨0, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a13_b38_c01 (q : Σ d : Fin (12 - 1 - 2), Fin (12 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 15 54 ⟨(⟨1, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨6400, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a13_b38_c02 (q : Σ d : Fin (12 - 2 - 2), Fin (12 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 15 54 ⟨(⟨2, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨6400, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a13_b38_c03 (q : Σ d : Fin (12 - 3 - 2), Fin (12 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 15 54 ⟨(⟨3, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨6400, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a13_b38_c04 (q : Σ d : Fin (12 - 4 - 2), Fin (12 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 15 54 ⟨(⟨4, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨6400, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a13_b38_c05 (q : Σ d : Fin (12 - 5 - 2), Fin (12 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 15 54 ⟨(⟨5, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨6400, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a13_b38_c06 (q : Σ d : Fin (12 - 6 - 2), Fin (12 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 15 54 ⟨(⟨6, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨6400, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a13_b38_c07 (q : Σ d : Fin (12 - 7 - 2), Fin (12 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 15 54 ⟨(⟨7, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨6400, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a13_b38_c08 (q : Σ d : Fin (12 - 8 - 2), Fin (12 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 15 54 ⟨(⟨8, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨6400, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a13_b38_c09 (q : Σ d : Fin (12 - 9 - 2), Fin (12 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 15 54 ⟨(⟨9, by norm_num⟩ : Fin (12 - 2)), q⟩) code = true := by
  exact ⟨15, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a13_b38 (q : IncreasingThree 12) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 15 54 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a13_b38_c00 q
  · exact certificate67_a13_b38_c01 q
  · exact certificate67_a13_b38_c02 q
  · exact certificate67_a13_b38_c03 q
  · exact certificate67_a13_b38_c04 q
  · exact certificate67_a13_b38_c05 q
  · exact certificate67_a13_b38_c06 q
  · exact certificate67_a13_b38_c07 q
  · exact certificate67_a13_b38_c08 q
  · exact certificate67_a13_b38_c09 q

end MinModulus.SHCSixCertificate.Generated
