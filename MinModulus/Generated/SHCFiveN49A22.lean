import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_22 : List ℕ := [6, 193, 17, 521, 261, 1984, 1865, 2545, 3745, 772, 22, 2786, 402, 526, 465, 4387, 4227, 4232, 2476, 2626, 2308, 642, 705, 386, 773, 153, 1507, 85, 589, 2468, 449, 2631, 898, 14, 30]

private theorem valid49_22 : ∀ code ∈ codes49_22, validRelationCode code := by
  decide

private theorem cover49_22 : ∀ q : IncreasingFourTail 47 (⟨22, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_22 (increasingFourValues (N := 49) ⟨⟨22, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a22
    (q : IncreasingFourTail 47 (⟨22, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨22, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_22 _ valid49_22 (cover49_22 q)

end MinModulus.SHCFiveCertificate.Generated
