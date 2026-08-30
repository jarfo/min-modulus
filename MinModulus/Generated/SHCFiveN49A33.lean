import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_33 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 85, 153, 773, 643, 402, 4227, 386, 770, 1667]

private theorem valid49_33 : ∀ code ∈ codes49_33, validRelationCode code := by
  decide

private theorem cover49_33 : ∀ q : IncreasingFourTail 47 (⟨33, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_33 (increasingFourValues (N := 49) ⟨⟨33, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a33
    (q : IncreasingFourTail 47 (⟨33, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨33, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_33 _ valid49_33 (cover49_33 q)

end MinModulus.SHCFiveCertificate.Generated
