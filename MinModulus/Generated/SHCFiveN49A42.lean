import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_42 : List ℕ := [17, 402]

private theorem valid49_42 : ∀ code ∈ codes49_42, validRelationCode code := by
  decide

private theorem cover49_42 : ∀ q : IncreasingFourTail 47 (⟨42, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_42 (increasingFourValues (N := 49) ⟨⟨42, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a42
    (q : IncreasingFourTail 47 (⟨42, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨42, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_42 _ valid49_42 (cover49_42 q)

end MinModulus.SHCFiveCertificate.Generated
