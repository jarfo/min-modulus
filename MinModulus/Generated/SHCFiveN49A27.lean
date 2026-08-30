import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_27 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 589, 403, 4387, 4227, 4232, 2786, 2631, 2308, 85, 153, 773, 643, 386, 1347, 1667, 770, 3907, 387, 1827]

private theorem valid49_27 : ∀ code ∈ codes49_27, validRelationCode code := by
  decide

private theorem cover49_27 : ∀ q : IncreasingFourTail 47 (⟨27, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_27 (increasingFourValues (N := 49) ⟨⟨27, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a27
    (q : IncreasingFourTail 47 (⟨27, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨27, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_27 _ valid49_27 (cover49_27 q)

end MinModulus.SHCFiveCertificate.Generated
