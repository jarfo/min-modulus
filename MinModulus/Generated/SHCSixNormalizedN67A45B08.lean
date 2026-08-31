import MinModulus.Generated.SHCSixNormalizedN67A45B06

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate67_a45_b08_c00 (q : Σ d : Fin (10 - 0 - 2), Fin (10 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 47 56 ⟨(⟨0, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a45_b08_c01 (q : Σ d : Fin (10 - 1 - 2), Fin (10 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 47 56 ⟨(⟨1, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a45_b08_c02 (q : Σ d : Fin (10 - 2 - 2), Fin (10 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 47 56 ⟨(⟨2, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a45_b08_c03 (q : Σ d : Fin (10 - 3 - 2), Fin (10 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 47 56 ⟨(⟨3, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  exact ⟨8716, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a45_b08_c04 (q : Σ d : Fin (10 - 4 - 2), Fin (10 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 47 56 ⟨(⟨4, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a45_b08_c05 (q : Σ d : Fin (10 - 5 - 2), Fin (10 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 47 56 ⟨(⟨5, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  exact ⟨6019, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a45_b08_c06 (q : Σ d : Fin (10 - 6 - 2), Fin (10 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 47 56 ⟨(⟨6, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  exact ⟨5275, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate67_a45_b08_c07 (q : Σ d : Fin (10 - 7 - 2), Fin (10 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 47 56 ⟨(⟨7, by norm_num⟩ : Fin (10 - 2)), q⟩) code = true := by
  exact ⟨8322, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate67_a45_b08 (q : IncreasingThree 10) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 67 (blockValues 47 56 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate67_a45_b08_c00 q
  · exact certificate67_a45_b08_c01 q
  · exact certificate67_a45_b08_c02 q
  · exact certificate67_a45_b08_c03 q
  · exact certificate67_a45_b08_c04 q
  · exact certificate67_a45_b08_c05 q
  · exact certificate67_a45_b08_c06 q
  · exact certificate67_a45_b08_c07 q

end MinModulus.SHCSixCertificate.Generated
