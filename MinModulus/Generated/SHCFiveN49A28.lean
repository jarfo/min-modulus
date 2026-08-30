import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_28 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 773, 403, 643, 4387, 2786, 2631, 2468, 89, 2866, 5191, 898, 387]

private theorem valid49_28 : ∀ code ∈ codes49_28, validRelationCode code := by
  decide

private theorem cover49_28 : ∀ q : IncreasingFourTail 47 (⟨28, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_28 (increasingFourValues (N := 49) ⟨⟨28, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a28
    (q : IncreasingFourTail 47 (⟨28, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨28, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_28 _ valid49_28 (cover49_28 q)

end MinModulus.SHCFiveCertificate.Generated
