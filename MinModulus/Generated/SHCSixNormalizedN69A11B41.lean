import MinModulus.Generated.SHCSixNormalizedN69A11B39

namespace MinModulus.SHCSixCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate69_a11_b41_c00 (q : Σ d : Fin (13 - 0 - 2), Fin (13 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 13 55 ⟨(⟨0, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a11_b41_c01 (q : Σ d : Fin (13 - 1 - 2), Fin (13 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 13 55 ⟨(⟨1, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a11_b41_c02 (q : Σ d : Fin (13 - 2 - 2), Fin (13 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 13 55 ⟨(⟨2, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨7, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a11_b41_c03 (q : Σ d : Fin (13 - 3 - 2), Fin (13 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 13 55 ⟨(⟨3, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨7, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a11_b41_c04 (q : Σ d : Fin (13 - 4 - 2), Fin (13 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 13 55 ⟨(⟨4, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨7, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a11_b41_c05 (q : Σ d : Fin (13 - 5 - 2), Fin (13 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 13 55 ⟨(⟨5, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨7, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a11_b41_c06 (q : Σ d : Fin (13 - 6 - 2), Fin (13 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 13 55 ⟨(⟨6, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨7, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a11_b41_c07 (q : Σ d : Fin (13 - 7 - 2), Fin (13 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 13 55 ⟨(⟨7, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨7, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a11_b41_c08 (q : Σ d : Fin (13 - 8 - 2), Fin (13 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 13 55 ⟨(⟨8, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨7, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a11_b41_c09 (q : Σ d : Fin (13 - 9 - 2), Fin (13 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 13 55 ⟨(⟨9, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨7, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

private theorem certificate69_a11_b41_c10 (q : Σ d : Fin (13 - 10 - 2), Fin (13 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 13 55 ⟨(⟨10, by norm_num⟩ : Fin (13 - 2)), q⟩) code = true := by
  exact ⟨7, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat]⟩

theorem certificate69_a11_b41 (q : IncreasingThree 13) : ∃ code,
    validRelationCode code ∧
    relationZeroNat 69 (blockValues 13 55 q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate69_a11_b41_c00 q
  · exact certificate69_a11_b41_c01 q
  · exact certificate69_a11_b41_c02 q
  · exact certificate69_a11_b41_c03 q
  · exact certificate69_a11_b41_c04 q
  · exact certificate69_a11_b41_c05 q
  · exact certificate69_a11_b41_c06 q
  · exact certificate69_a11_b41_c07 q
  · exact certificate69_a11_b41_c08 q
  · exact certificate69_a11_b41_c09 q
  · exact certificate69_a11_b41_c10 q

end MinModulus.SHCSixCertificate.Generated
