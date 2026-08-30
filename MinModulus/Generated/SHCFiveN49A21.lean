import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_21 : List ℕ := [17, 521, 261, 131, 7, 6, 193, 1984, 3585, 3745, 1865, 2545, 4227, 465, 2476, 643, 4885, 772, 773, 2308, 705, 2468, 4544, 3344, 526, 403, 4387, 22, 5045, 527, 3264, 2866, 89, 2786, 770, 449, 27, 5036, 402, 85]

private theorem valid49_21 : ∀ code ∈ codes49_21, validRelationCode code := by
  decide

private theorem cover49_21 : ∀ q : IncreasingFourTail 47 (⟨21, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_21 (increasingFourValues (N := 49) ⟨⟨21, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a21
    (q : IncreasingFourTail 47 (⟨21, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨21, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_21 _ valid49_21 (cover49_21 q)

end MinModulus.SHCFiveCertificate.Generated
