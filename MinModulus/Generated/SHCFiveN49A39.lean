import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_39 : List ℕ := [17, 521, 261, 131, 772]

private theorem valid49_39 : ∀ code ∈ codes49_39, validRelationCode code := by
  decide

private theorem cover49_39 : ∀ q : IncreasingFourTail 47 (⟨39, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_39 (increasingFourValues (N := 49) ⟨⟨39, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a39
    (q : IncreasingFourTail 47 (⟨39, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨39, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_39 _ valid49_39 (cover49_39 q)

end MinModulus.SHCFiveCertificate.Generated
