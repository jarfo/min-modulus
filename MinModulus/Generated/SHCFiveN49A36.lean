import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_36 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 85, 77, 386, 770]

private theorem valid49_36 : ∀ code ∈ codes49_36, validRelationCode code := by
  decide

private theorem cover49_36 : ∀ q : IncreasingFourTail 47 (⟨36, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_36 (increasingFourValues (N := 49) ⟨⟨36, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a36
    (q : IncreasingFourTail 47 (⟨36, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨36, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_36 _ valid49_36 (cover49_36 q)

end MinModulus.SHCFiveCertificate.Generated
