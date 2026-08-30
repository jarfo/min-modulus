import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_26 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 3785, 2485, 85, 153, 589, 4232, 403, 643, 2786, 4387, 773, 2631, 2468, 4234, 3765, 4884, 5191, 770, 5346, 3912, 14, 899]

private theorem valid49_26 : ∀ code ∈ codes49_26, validRelationCode code := by
  decide

private theorem cover49_26 : ∀ q : IncreasingFourTail 47 (⟨26, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_26 (increasingFourValues (N := 49) ⟨⟨26, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a26
    (q : IncreasingFourTail 47 (⟨26, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨26, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_26 _ valid49_26 (cover49_26 q)

end MinModulus.SHCFiveCertificate.Generated
