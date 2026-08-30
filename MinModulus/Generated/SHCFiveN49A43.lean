import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_43 : List ℕ := [772]

private theorem valid49_43 : ∀ code ∈ codes49_43, validRelationCode code := by
  decide

private theorem cover49_43 : ∀ q : IncreasingFourTail 47 (⟨43, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_43 (increasingFourValues (N := 49) ⟨⟨43, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a43
    (q : IncreasingFourTail 47 (⟨43, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨43, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_43 _ valid49_43 (cover49_43 q)

end MinModulus.SHCFiveCertificate.Generated
