import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_00 : List ℕ := [1344]

private theorem valid49_00 : ∀ code ∈ codes49_00, validRelationCode code := by
  decide

private theorem cover49_00 : ∀ q : IncreasingFourTail 47 (⟨0, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_00 (increasingFourValues (N := 49) ⟨⟨0, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a00
    (q : IncreasingFourTail 47 (⟨0, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨0, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_00 _ valid49_00 (cover49_00 q)

end MinModulus.SHCFiveCertificate.Generated
