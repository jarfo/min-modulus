import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_32 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 77, 2631, 3911, 153, 773]

private theorem valid49_32 : ∀ code ∈ codes49_32, validRelationCode code := by
  decide

private theorem cover49_32 : ∀ q : IncreasingFourTail 47 (⟨32, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_32 (increasingFourValues (N := 49) ⟨⟨32, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a32
    (q : IncreasingFourTail 47 (⟨32, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨32, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_32 _ valid49_32 (cover49_32 q)

end MinModulus.SHCFiveCertificate.Generated
