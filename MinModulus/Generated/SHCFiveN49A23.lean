import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_23 : List ℕ := [1185]

private theorem valid49_23 : ∀ code ∈ codes49_23, validRelationCode code := by
  decide

private theorem cover49_23 : ∀ q : IncreasingFourTail 47 (⟨23, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_23 (increasingFourValues (N := 49) ⟨⟨23, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a23
    (q : IncreasingFourTail 47 (⟨23, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨23, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_23 _ valid49_23 (cover49_23 q)

end MinModulus.SHCFiveCertificate.Generated
