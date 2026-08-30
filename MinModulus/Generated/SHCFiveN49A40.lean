import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_40 : List ℕ := [17, 521, 261, 772]

private theorem valid49_40 : ∀ code ∈ codes49_40, validRelationCode code := by
  decide

private theorem cover49_40 : ∀ q : IncreasingFourTail 47 (⟨40, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_40 (increasingFourValues (N := 49) ⟨⟨40, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a40
    (q : IncreasingFourTail 47 (⟨40, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨40, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_40 _ valid49_40 (cover49_40 q)

end MinModulus.SHCFiveCertificate.Generated
