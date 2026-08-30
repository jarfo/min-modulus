import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_31 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 4227, 2308, 85, 589, 2631, 403, 643, 2786, 386, 93, 4387]

private theorem valid49_31 : ∀ code ∈ codes49_31, validRelationCode code := by
  decide

private theorem cover49_31 : ∀ q : IncreasingFourTail 47 (⟨31, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_31 (increasingFourValues (N := 49) ⟨⟨31, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a31
    (q : IncreasingFourTail 47 (⟨31, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨31, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_31 _ valid49_31 (cover49_31 q)

end MinModulus.SHCFiveCertificate.Generated
