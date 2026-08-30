import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_24 : List ℕ := [17, 521, 261, 131, 3785, 2485, 642, 4227, 589, 773, 2631, 2468, 772, 402, 465, 4884, 85, 643, 4387, 4232, 2476, 2626, 2308, 403, 2786, 153, 526, 961, 705, 4234, 4066, 2958, 898, 833, 93, 5514]

private theorem valid49_24 : ∀ code ∈ codes49_24, validRelationCode code := by
  decide

private theorem cover49_24 : ∀ q : IncreasingFourTail 47 (⟨24, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_24 (increasingFourValues (N := 49) ⟨⟨24, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a24
    (q : IncreasingFourTail 47 (⟨24, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨24, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_24 _ valid49_24 (cover49_24 q)

end MinModulus.SHCFiveCertificate.Generated
