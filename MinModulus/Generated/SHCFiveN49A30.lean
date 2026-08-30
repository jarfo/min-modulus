import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_30 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 386, 403, 643, 773, 4387, 770, 2954, 3907]

private theorem valid49_30 : ∀ code ∈ codes49_30, validRelationCode code := by
  decide

private theorem cover49_30 : ∀ q : IncreasingFourTail 47 (⟨30, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_30 (increasingFourValues (N := 49) ⟨⟨30, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a30
    (q : IncreasingFourTail 47 (⟨30, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨30, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_30 _ valid49_30 (cover49_30 q)

end MinModulus.SHCFiveCertificate.Generated
