import MinModulus.Generated.SHCSixN105A03B05

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a03_b07_c00 (q : Σ d : Fin (43 - 0 - 2), Fin (43 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1029, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11791, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨41, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨2074, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3205, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨41, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1697, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2693, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨41, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3086, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨25, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c01 (q : Σ d : Fin (43 - 1 - 2), Fin (43 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨517, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c02 (q : Σ d : Fin (43 - 2 - 2), Fin (43 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨401, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1030, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨2819, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨1697, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨62, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3205, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨1569, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨2693, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2074, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨817, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨945, by decide, by decide⟩
    · exact ⟨2693, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨550, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6883, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨534, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c03 (q : Σ d : Fin (43 - 3 - 2), Fin (43 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨393, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c04 (q : Σ d : Fin (43 - 4 - 2), Fin (43 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨518, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c05 (q : Σ d : Fin (43 - 5 - 2), Fin (43 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨566, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨62, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨2074, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3205, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨189, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨817, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨945, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨54, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c06 (q : Σ d : Fin (43 - 6 - 2), Fin (43 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨519, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c07 (q : Σ d : Fin (43 - 7 - 2), Fin (43 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨7577, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c08 (q : Σ d : Fin (43 - 8 - 2), Fin (43 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨11016, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10626, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨42, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨299, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2074, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3205, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨62, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨3969, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5300, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7650, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c09 (q : Σ d : Fin (43 - 9 - 2), Fin (43 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨7944, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c10 (q : Σ d : Fin (43 - 10 - 2), Fin (43 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨7554, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c11 (q : Σ d : Fin (43 - 11 - 2), Fin (43 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨7170, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c12 (q : Σ d : Fin (43 - 12 - 2), Fin (43 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨566, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨62, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3205, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1039, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨945, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a03_b07_c13 (q : Σ d : Fin (43 - 13 - 2), Fin (43 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3205, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6836, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13698, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c14 (q : Σ d : Fin (43 - 14 - 2), Fin (43 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨177, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨62, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨1315, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨689, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨54, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2307, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3086, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3331, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a03_b07_c15 (q : Σ d : Fin (43 - 15 - 2), Fin (43 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨7566, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c16 (q : Σ d : Fin (43 - 16 - 2), Fin (43 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3205, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1039, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13698, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13314, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10674, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c17 (q : Σ d : Fin (43 - 17 - 2), Fin (43 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨4868, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3205, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11058, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3331, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13320, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c18 (q : Σ d : Fin (43 - 18 - 2), Fin (43 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨4867, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c19 (q : Σ d : Fin (43 - 19 - 2), Fin (43 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨38, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨693, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2834, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨54, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨689, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2062, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3086, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a03_b07_c20 (q : Σ d : Fin (43 - 20 - 2), Fin (43 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨20, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨566, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨2961, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨693, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨929, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨693, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨929, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨929, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨929, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨929, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨929, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨817, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2177, by decide, by decide⟩
    · exact ⟨945, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨33, by decide, by decide⟩

private theorem certificate105_a03_b07_c21 (q : Σ d : Fin (43 - 21 - 2), Fin (43 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨21, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨6020, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨23, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨787, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13698, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13320, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12553, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c22 (q : Σ d : Fin (43 - 22 - 2), Fin (43 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨22, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨6019, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c23 (q : Σ d : Fin (43 - 23 - 2), Fin (43 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨23, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨15, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c24 (q : Σ d : Fin (43 - 24 - 2), Fin (43 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨24, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨22, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13698, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8720, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8714, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c25 (q : Σ d : Fin (43 - 25 - 2), Fin (43 - (25 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨25, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨14, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c26 (q : Σ d : Fin (43 - 26 - 2), Fin (43 - (26 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨26, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨897, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c27 (q : Σ d : Fin (43 - 27 - 2), Fin (43 - (27 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨27, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨21, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13326, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c28 (q : Σ d : Fin (43 - 28 - 2), Fin (43 - (28 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨28, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨13, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c29 (q : Σ d : Fin (43 - 29 - 2), Fin (43 - (29 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨29, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7964, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2077, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨2078, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c30 (q : Σ d : Fin (43 - 30 - 2), Fin (43 - (30 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨30, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨12, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c31 (q : Σ d : Fin (43 - 31 - 2), Fin (43 - (31 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨31, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨769, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c32 (q : Σ d : Fin (43 - 32 - 2), Fin (43 - (32 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨32, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c33 (q : Σ d : Fin (43 - 33 - 2), Fin (43 - (33 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨33, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c34 (q : Σ d : Fin (43 - 34 - 2), Fin (43 - (34 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨34, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c35 (q : Σ d : Fin (43 - 35 - 2), Fin (43 - (35 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨35, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1283, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c36 (q : Σ d : Fin (43 - 36 - 2), Fin (43 - (36 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨36, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨771, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c37 (q : Σ d : Fin (43 - 37 - 2), Fin (43 - (37 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨37, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c38 (q : Σ d : Fin (43 - 38 - 2), Fin (43 - (38 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨38, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c39 (q : Σ d : Fin (43 - 39 - 2), Fin (43 - (39 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨39, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1795, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a03_b07_c40 (q : Σ d : Fin (43 - 40 - 2), Fin (43 - (40 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) ⟨(⟨40, by norm_num⟩ : Fin (43 - 2)), q⟩) code = true := by
  exact ⟨641, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a03_b07 (q : IncreasingThree 43) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨3, by norm_num⟩ : Fin 55) (⟨11, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a03_b07_c00 q
  · exact certificate105_a03_b07_c01 q
  · exact certificate105_a03_b07_c02 q
  · exact certificate105_a03_b07_c03 q
  · exact certificate105_a03_b07_c04 q
  · exact certificate105_a03_b07_c05 q
  · exact certificate105_a03_b07_c06 q
  · exact certificate105_a03_b07_c07 q
  · exact certificate105_a03_b07_c08 q
  · exact certificate105_a03_b07_c09 q
  · exact certificate105_a03_b07_c10 q
  · exact certificate105_a03_b07_c11 q
  · exact certificate105_a03_b07_c12 q
  · exact certificate105_a03_b07_c13 q
  · exact certificate105_a03_b07_c14 q
  · exact certificate105_a03_b07_c15 q
  · exact certificate105_a03_b07_c16 q
  · exact certificate105_a03_b07_c17 q
  · exact certificate105_a03_b07_c18 q
  · exact certificate105_a03_b07_c19 q
  · exact certificate105_a03_b07_c20 q
  · exact certificate105_a03_b07_c21 q
  · exact certificate105_a03_b07_c22 q
  · exact certificate105_a03_b07_c23 q
  · exact certificate105_a03_b07_c24 q
  · exact certificate105_a03_b07_c25 q
  · exact certificate105_a03_b07_c26 q
  · exact certificate105_a03_b07_c27 q
  · exact certificate105_a03_b07_c28 q
  · exact certificate105_a03_b07_c29 q
  · exact certificate105_a03_b07_c30 q
  · exact certificate105_a03_b07_c31 q
  · exact certificate105_a03_b07_c32 q
  · exact certificate105_a03_b07_c33 q
  · exact certificate105_a03_b07_c34 q
  · exact certificate105_a03_b07_c35 q
  · exact certificate105_a03_b07_c36 q
  · exact certificate105_a03_b07_c37 q
  · exact certificate105_a03_b07_c38 q
  · exact certificate105_a03_b07_c39 q
  · exact certificate105_a03_b07_c40 q

end MinModulus.SHCSixExceptionalCertificate.Generated
