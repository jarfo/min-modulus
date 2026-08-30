import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_41 : List ℕ := [17, 521, 770]

private theorem valid49_41 : ∀ code ∈ codes49_41, validRelationCode code := by
  decide

private theorem cover49_41 : ∀ q : IncreasingFourTail 47 (⟨41, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_41 (increasingFourValues (N := 49) ⟨⟨41, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a41
    (q : IncreasingFourTail 47 (⟨41, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨41, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_41 _ valid49_41 (cover49_41 q)

end MinModulus.SHCFiveCertificate.Generated
