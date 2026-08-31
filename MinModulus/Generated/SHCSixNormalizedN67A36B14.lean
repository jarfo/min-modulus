import MinModulus.Generated.SHCSixNormalizedN67A36B12

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a36_b14_c00 (q : Σ d : Fin (13 - 0 - 2), Fin (13 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 38 53 ⟨(⟨0, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a36_b14_c01 (q : Σ d : Fin (13 - 1 - 2), Fin (13 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 38 53 ⟨(⟨1, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨5250, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a36_b14_c02 (q : Σ d : Fin (13 - 2 - 2), Fin (13 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 38 53 ⟨(⟨2, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨5250, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a36_b14_c03 (q : Σ d : Fin (13 - 3 - 2), Fin (13 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 38 53 ⟨(⟨3, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨5250, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a36_b14_c04 (q : Σ d : Fin (13 - 4 - 2), Fin (13 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 38 53 ⟨(⟨4, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨5250, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a36_b14_c05 (q : Σ d : Fin (13 - 5 - 2), Fin (13 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 38 53 ⟨(⟨5, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨5250, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a36_b14_c06 (q : Σ d : Fin (13 - 6 - 2), Fin (13 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 38 53 ⟨(⟨6, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨5250, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a36_b14_c07 (q : Σ d : Fin (13 - 7 - 2), Fin (13 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 38 53 ⟨(⟨7, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨7577, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a36_b14_c08 (q : Σ d : Fin (13 - 8 - 2), Fin (13 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 38 53 ⟨(⟨8, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨5250, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a36_b14_c09 (q : Σ d : Fin (13 - 9 - 2), Fin (13 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 38 53 ⟨(⟨9, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨5250, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a36_b14_c10 (q : Σ d : Fin (13 - 10 - 2), Fin (13 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 38 53 ⟨(⟨10, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨5250, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a36_b14 (q : IncreasingThree 13) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 38 53 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a36_b14_c00 q
  · exact certificate67_a36_b14_c01 q
  · exact certificate67_a36_b14_c02 q
  · exact certificate67_a36_b14_c03 q
  · exact certificate67_a36_b14_c04 q
  · exact certificate67_a36_b14_c05 q
  · exact certificate67_a36_b14_c06 q
  · exact certificate67_a36_b14_c07 q
  · exact certificate67_a36_b14_c08 q
  · exact certificate67_a36_b14_c09 q
  · exact certificate67_a36_b14_c10 q

end MinModulus.SHCSixCertificate.Generated
