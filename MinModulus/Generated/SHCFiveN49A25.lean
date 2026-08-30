import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_25 : List ℕ := [17, 521, 261, 131, 3785, 2485, 4227, 642, 85, 643, 772, 2626, 402, 153, 773, 2786, 2308, 2631, 403, 589, 2468, 4232, 4387, 4234, 4884, 3756, 1347, 526, 93, 5045, 2958, 386, 22, 387, 1346, 5191]

private theorem valid49_25 : ∀ code ∈ codes49_25, validRelationCode code := by
  decide

private theorem cover49_25 : ∀ q : IncreasingFourTail 47 (⟨25, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_25 (increasingFourValues (N := 49) ⟨⟨25, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a25
    (q : IncreasingFourTail 47 (⟨25, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨25, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_25 _ valid49_25 (cover49_25 q)

end MinModulus.SHCFiveCertificate.Generated
