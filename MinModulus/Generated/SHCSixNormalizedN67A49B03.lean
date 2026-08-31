import MinModulus.Generated.SHCSixNormalizedN67A49B01

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a49_b03_c00 (q : Σ d : Fin (11 - 0 - 2), Fin (11 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 51 55 ⟨(⟨0, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a49_b03_c01 (q : Σ d : Fin (11 - 1 - 2), Fin (11 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 51 55 ⟨(⟨1, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨11010, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a49_b03_c02 (q : Σ d : Fin (11 - 2 - 2), Fin (11 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 51 55 ⟨(⟨2, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨8322, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a49_b03_c03 (q : Σ d : Fin (11 - 3 - 2), Fin (11 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 51 55 ⟨(⟨3, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨7938, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a49_b03_c04 (q : Σ d : Fin (11 - 4 - 2), Fin (11 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 51 55 ⟨(⟨4, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨7944, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a49_b03_c05 (q : Σ d : Fin (11 - 5 - 2), Fin (11 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 51 55 ⟨(⟨5, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨5635, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a49_b03_c06 (q : Σ d : Fin (11 - 6 - 2), Fin (11 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 51 55 ⟨(⟨6, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a49_b03_c07 (q : Σ d : Fin (11 - 7 - 2), Fin (11 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 51 55 ⟨(⟨7, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a49_b03_c08 (q : Σ d : Fin (11 - 8 - 2), Fin (11 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 51 55 ⟨(⟨8, by norm_num⟩ : Fin (11 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a49_b03 (q : IncreasingThree 11) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 51 55 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a49_b03_c00 q
  · exact certificate67_a49_b03_c01 q
  · exact certificate67_a49_b03_c02 q
  · exact certificate67_a49_b03_c03 q
  · exact certificate67_a49_b03_c04 q
  · exact certificate67_a49_b03_c05 q
  · exact certificate67_a49_b03_c06 q
  · exact certificate67_a49_b03_c07 q
  · exact certificate67_a49_b03_c08 q

end MinModulus.SHCSixCertificate.Generated
