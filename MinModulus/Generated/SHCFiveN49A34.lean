import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_34 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308]

private theorem valid49_34 : ∀ code ∈ codes49_34, validRelationCode code := by
  decide

private theorem cover49_34 : ∀ q : IncreasingFourTail 47 (⟨34, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_34 (increasingFourValues (N := 49) ⟨⟨34, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a34
    (q : IncreasingFourTail 47 (⟨34, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨34, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_34 _ valid49_34 (cover49_34 q)

end MinModulus.SHCFiveCertificate.Generated
