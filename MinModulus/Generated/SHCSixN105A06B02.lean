import MinModulus.Generated.SHCSixN105A06B00

namespace MinModulus.SHCSixExceptionalCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private theorem certificate105_a06_b02_c00 (q : Σ d : Fin (45 - 0 - 2), Fin (45 - (0 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨0, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10625, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13326, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11791, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10627, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10243, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4484, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7964, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨42, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3969, by decide, by decide⟩
    · exact ⟨3086, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2074, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨8720, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1569, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2693, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨173, by decide, by decide⟩
    · exact ⟨3085, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨63, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨2205, by decide, by decide⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5347, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨25, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c01 (q : Σ d : Fin (45 - 1 - 2), Fin (45 - (1 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨1, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨10625, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨1569, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨2070, by decide, by decide⟩
    · exact ⟨173, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨1825, by decide, by decide⟩
    · exact ⟨3205, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨693, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨2693, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2441, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨433, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
  · exact ⟨12175, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11791, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10243, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7580, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨173, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2205, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2074, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨945, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨8348, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10651, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨25, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6115, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1417, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c02 (q : Σ d : Fin (45 - 2 - 2), Fin (45 - (2 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨2, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  exact ⟨7553, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c03 (q : Σ d : Fin (45 - 3 - 2), Fin (45 - (3 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨3, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨6496, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨12784, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨26392, by decide, by decide⟩
    · exact ⟨14296, by decide, by decide⟩
    · exact ⟨3201, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨1569, by decide, by decide⟩
    · exact ⟨24880, by decide, by decide⟩
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨173, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨3205, by decide, by decide⟩
    · exact ⟨1697, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨3078, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨181, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨1701, by decide, by decide⟩
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨2069, by decide, by decide⟩
    · exact ⟨1569, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨1697, by decide, by decide⟩
    · exact ⟨693, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2693, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11791, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨13889, by decide, by decide⟩
    · exact ⟨18401, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨11200, by decide, by decide⟩
    · exact ⟨441, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨2201, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨41, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨433, by decide, by decide⟩
    · exact ⟨2074, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨62, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10243, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6452, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11419, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7964, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10639, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨25, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨54, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c04 (q : Σ d : Fin (45 - 4 - 2), Fin (45 - (4 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨4, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  exact ⟨6448, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c05 (q : Σ d : Fin (45 - 5 - 2), Fin (45 - (5 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨5, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨50, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨181, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨49, by decide, by decide⟩
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨2069, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨565, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨305, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨2693, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨3465, by decide, by decide⟩
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨3073, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨3205, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨3337, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2076, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1069, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨11017, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11791, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11058, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10627, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10243, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11419, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1449, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨41, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨3079, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨21377, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨817, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3085, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨6209, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨41, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨25, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨185, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c06 (q : Σ d : Fin (45 - 6 - 2), Fin (45 - (6 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨6, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2582, by decide, by decide⟩
    · exact ⟨2457, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨441, by decide, by decide⟩
    · exact ⟨566, by decide, by decide⟩
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨3073, by decide, by decide⟩
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨41, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨3077, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨2074, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨3969, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4484, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12175, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11791, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨41, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨3079, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨20993, by decide, by decide⟩
    · exact ⟨3969, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨817, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨1441, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1071, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨25, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1039, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨185, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2457, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c07 (q : Σ d : Fin (45 - 7 - 2), Fin (45 - (7 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨7, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10649, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨42, by decide, by decide⟩
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨3073, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨929, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨3337, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨1569, by decide, by decide⟩
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2961, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨62, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨3969, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1825, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4484, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨1574, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨3084, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨3085, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1039, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8708, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13313, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c08 (q : Σ d : Fin (45 - 8 - 2), Fin (45 - (8 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨8, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨44, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨3330, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨42, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨173, by decide, by decide⟩
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨3205, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2330, by decide, by decide⟩
    · exact ⟨169, by decide, by decide⟩
    · exact ⟨1569, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨1826, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3969, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2074, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨425, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4484, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨25, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨3457, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨24832, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨425, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨2457, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2457, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨425, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c09 (q : Σ d : Fin (45 - 9 - 2), Fin (45 - (9 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨9, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨10242, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4484, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1665, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨25, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11058, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11419, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2457, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2457, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨313, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2566, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c10 (q : Σ d : Fin (45 - 10 - 2), Fin (45 - (10 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨10, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  exact ⟨7170, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c11 (q : Σ d : Fin (45 - 11 - 2), Fin (45 - (11 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨11, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨26, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨157, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨25, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11791, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10627, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10243, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11419, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11035, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨3589, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · exact ⟨10639, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2567, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c12 (q : Σ d : Fin (45 - 12 - 2), Fin (45 - (12 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨12, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  exact ⟨7577, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c13 (q : Σ d : Fin (45 - 13 - 2), Fin (45 - (13 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨13, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨14080, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2818, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨48, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨177, by decide, by decide⟩
    · exact ⟨3074, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨3465, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨3969, by decide, by decide⟩
    · exact ⟨1570, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨2705, by decide, by decide⟩
    · exact ⟨2072, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨306, by decide, by decide⟩
    · exact ⟨40, by decide, by decide⟩
    · exact ⟨2561, by decide, by decide⟩
    · exact ⟨298, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨3076, by decide, by decide⟩
    · exact ⟨2457, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨1573, by decide, by decide⟩
    · exact ⟨2961, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1569, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1537, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨60, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨3713, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2457, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨2961, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨817, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2565, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨2961, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨8348, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3717, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨3457, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨945, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12175, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11791, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10627, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9860, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6452, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c14 (q : Σ d : Fin (45 - 14 - 2), Fin (45 - (14 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨14, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1794, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1669, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11058, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11779, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13313, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10627, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10243, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c15 (q : Σ d : Fin (45 - 15 - 2), Fin (45 - (15 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨15, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨10638, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨4484, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨24, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15233, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨169, by decide, by decide⟩
    · exact ⟨2562, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨297, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨3079, by decide, by decide⟩
    · exact ⟨3841, by decide, by decide⟩
    · exact ⟨19841, by decide, by decide⟩
    · exact ⟨58, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2329, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1039, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨18401, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨11200, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9482, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13314, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13320, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c16 (q : Σ d : Fin (45 - 16 - 2), Fin (45 - (16 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨16, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  exact ⟨7566, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c17 (q : Σ d : Fin (45 - 17 - 2), Fin (45 - (17 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨17, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  exact ⟨4483, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c18 (q : Σ d : Fin (45 - 18 - 2), Fin (45 - (18 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨18, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨673, by decide, by decide⟩
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨2564, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨3079, by decide, by decide⟩
    · exact ⟨3337, by decide, by decide⟩
    · exact ⟨16817, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨3842, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨57, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1572, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13314, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13320, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c19 (q : Σ d : Fin (45 - 19 - 2), Fin (45 - (19 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨19, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨14849, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨153, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1538, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨281, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1039, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11395, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11011, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c20 (q : Σ d : Fin (45 - 20 - 2), Fin (45 - (20 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨20, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  exact ⟨6031, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c21 (q : Σ d : Fin (45 - 21 - 2), Fin (45 - (21 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨21, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1540, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13697, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨56, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨313, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
  · fin_cases e
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨3585, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨3589, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1069, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8348, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨6209, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9482, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c22 (q : Σ d : Fin (45 - 22 - 2), Fin (45 - (22 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨22, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1541, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13313, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2058, by decide, by decide⟩
    · exact ⟨314, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨693, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2069, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨185, by decide, by decide⟩
    · exact ⟨693, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7964, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13710, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12553, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2063, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1039, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c23 (q : Σ d : Fin (45 - 23 - 2), Fin (45 - (23 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨23, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨13336, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨14088, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨2567, by decide, by decide⟩
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨11200, by decide, by decide⟩
    · exact ⟨2961, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨313, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨929, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1575, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · fin_cases e
    · exact ⟨2567, by decide, by decide⟩
    · exact ⟨3337, by decide, by decide⟩
    · exact ⟨18401, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨313, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3589, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨929, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨6209, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨19458, by decide, by decide⟩
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3588, by decide, by decide⟩
    · exact ⟨3589, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨9664, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨929, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨6209, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨13314, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨5300, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6068, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3591, by decide, by decide⟩
    · exact ⟨929, by decide, by decide⟩
    · exact ⟨1185, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨817, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8708, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨9760, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c24 (q : Σ d : Fin (45 - 24 - 2), Fin (45 - (24 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨24, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨409, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3586, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨561, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1313, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨3590, by decide, by decide⟩
    · exact ⟨3213, by decide, by decide⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3081, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨3457, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13710, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13326, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12931, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12547, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1038, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c25 (q : Σ d : Fin (45 - 25 - 2), Fin (45 - (25 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨25, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1542, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13337, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13710, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13326, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨3082, by decide, by decide⟩
    · exact ⟨165, by decide, by decide⟩
    · exact ⟨2961, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨929, by decide, by decide⟩
    · exact ⟨2197, by decide, by decide⟩
  · exact ⟨11058, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1070, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨913, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c26 (q : Σ d : Fin (45 - 26 - 2), Fin (45 - (26 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨26, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1543, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13721, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨10673, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c27 (q : Σ d : Fin (45 - 27 - 2), Fin (45 - (27 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨27, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13710, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨13326, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9104, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨11058, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨9568, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c28 (q : Σ d : Fin (45 - 28 - 2), Fin (45 - (28 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨28, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨12544, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7964, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8720, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1037, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c29 (q : Σ d : Fin (45 - 29 - 2), Fin (45 - (29 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨29, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  exact ⟨9472, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c30 (q : Σ d : Fin (45 - 30 - 2), Fin (45 - (30 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨30, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨2057, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨1066, by decide, by decide⟩
    · exact ⟨801, by decide, by decide⟩
    · exact ⟨54, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2068, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8348, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7556, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨785, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c31 (q : Σ d : Fin (45 - 31 - 2), Fin (45 - (31 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨31, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨564, by decide, by decide⟩
    · exact ⟨36, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨562, by decide, by decide⟩
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨3209, by decide, by decide⟩
    · exact ⟨2066, by decide, by decide⟩
    · exact ⟨46, by decide, by decide⟩
    · exact ⟨3338, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨2060, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨6499, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6883, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨34, by decide, by decide⟩
    · exact ⟨2065, by decide, by decide⟩
    · exact ⟨3080, by decide, by decide⟩
    · exact ⟨1314, by decide, by decide⟩
    · exact ⟨2833, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨52, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨31, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · fin_cases e
    · exact ⟨818, by decide, by decide⟩
    · exact ⟨3329, by decide, by decide⟩
    · exact ⟨2306, by decide, by decide⟩
    · exact ⟨1068, by decide, by decide⟩
    · exact ⟨33, by decide, by decide⟩
  · exact ⟨30, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7946, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1036, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c32 (q : Σ d : Fin (45 - 32 - 2), Fin (45 - (32 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨32, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨7172, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c33 (q : Σ d : Fin (45 - 33 - 2), Fin (45 - (33 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨33, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨20, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1165, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1921, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1034, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c34 (q : Σ d : Fin (45 - 34 - 2), Fin (45 - (34 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨34, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  exact ⟨12, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c35 (q : Σ d : Fin (45 - 35 - 2), Fin (45 - (35 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨35, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨15616, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨657, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨29, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c36 (q : Σ d : Fin (45 - 36 - 2), Fin (45 - (36 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨36, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨18, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1033, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨8032, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨28, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c37 (q : Σ d : Fin (45 - 37 - 2), Fin (45 - (37 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨37, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  exact ⟨10, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c38 (q : Σ d : Fin (45 - 38 - 2), Fin (45 - (38 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨38, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · fin_cases e
    · exact ⟨3969, by decide, by decide⟩
    · exact ⟨1197, by decide, by decide⟩
    · exact ⟨802, by decide, by decide⟩
    · exact ⟨1825, by decide, by decide⟩
    · exact ⟨2189, by decide, by decide⟩
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨12209, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨786, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c39 (q : Σ d : Fin (45 - 39 - 2), Fin (45 - (39 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨39, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨149, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1793, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c40 (q : Σ d : Fin (45 - 40 - 2), Fin (45 - (40 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨40, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  exact ⟨141, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c41 (q : Σ d : Fin (45 - 41 - 2), Fin (45 - (41 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨41, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  rcases q with ⟨d, e⟩
  fin_cases d
  · exact ⟨1282, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩
  · exact ⟨6113, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

private theorem certificate105_a06_b02_c42 (q : Σ d : Fin (45 - 42 - 2), Fin (45 - (42 + 1 + d.val) - 1)) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) ⟨(⟨42, by norm_num⟩ : Fin (45 - 2)), q⟩) code = true := by
  exact ⟨770, by decide, by simp +decide [relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩

theorem certificate105_a06_b02 (q : IncreasingThree 45) : ∃ code,
    validRelationCode code ∧
    relationZeroNat (blockValues (⟨6, by norm_num⟩ : Fin 55) (⟨9, by norm_num⟩ : Fin 55) q) code = true := by
  rcases q with ⟨c, q⟩
  fin_cases c
  · exact certificate105_a06_b02_c00 q
  · exact certificate105_a06_b02_c01 q
  · exact certificate105_a06_b02_c02 q
  · exact certificate105_a06_b02_c03 q
  · exact certificate105_a06_b02_c04 q
  · exact certificate105_a06_b02_c05 q
  · exact certificate105_a06_b02_c06 q
  · exact certificate105_a06_b02_c07 q
  · exact certificate105_a06_b02_c08 q
  · exact certificate105_a06_b02_c09 q
  · exact certificate105_a06_b02_c10 q
  · exact certificate105_a06_b02_c11 q
  · exact certificate105_a06_b02_c12 q
  · exact certificate105_a06_b02_c13 q
  · exact certificate105_a06_b02_c14 q
  · exact certificate105_a06_b02_c15 q
  · exact certificate105_a06_b02_c16 q
  · exact certificate105_a06_b02_c17 q
  · exact certificate105_a06_b02_c18 q
  · exact certificate105_a06_b02_c19 q
  · exact certificate105_a06_b02_c20 q
  · exact certificate105_a06_b02_c21 q
  · exact certificate105_a06_b02_c22 q
  · exact certificate105_a06_b02_c23 q
  · exact certificate105_a06_b02_c24 q
  · exact certificate105_a06_b02_c25 q
  · exact certificate105_a06_b02_c26 q
  · exact certificate105_a06_b02_c27 q
  · exact certificate105_a06_b02_c28 q
  · exact certificate105_a06_b02_c29 q
  · exact certificate105_a06_b02_c30 q
  · exact certificate105_a06_b02_c31 q
  · exact certificate105_a06_b02_c32 q
  · exact certificate105_a06_b02_c33 q
  · exact certificate105_a06_b02_c34 q
  · exact certificate105_a06_b02_c35 q
  · exact certificate105_a06_b02_c36 q
  · exact certificate105_a06_b02_c37 q
  · exact certificate105_a06_b02_c38 q
  · exact certificate105_a06_b02_c39 q
  · exact certificate105_a06_b02_c40 q
  · exact certificate105_a06_b02_c41 q
  · exact certificate105_a06_b02_c42 q

end MinModulus.SHCSixExceptionalCertificate.Generated
