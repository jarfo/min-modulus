import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_29 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 403, 4387, 402, 589, 4227, 4232, 2786, 2631, 2308, 85, 153, 773, 643, 1347, 386, 1667]

private theorem valid49_29 : ∀ code ∈ codes49_29, validRelationCode code := by
  decide

private theorem cover49_29 : ∀ q : IncreasingFourTail 47 (⟨29, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_29 (increasingFourValues (N := 49) ⟨⟨29, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a29
    (q : IncreasingFourTail 47 (⟨29, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨29, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_29 _ valid49_29 (cover49_29 q)

end MinModulus.SHCFiveCertificate.Generated
