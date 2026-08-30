import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_21 : List ℕ := [6, 193, 17, 521, 261, 1984, 1865, 2545, 3745, 772, 526, 22, 2786, 4227, 2308, 402, 642, 153, 1347, 4232, 2468, 705, 773, 26, 2476, 2626, 5346, 2866, 386, 14, 465, 93]

private theorem valid47_21 : ∀ code ∈ codes47_21, validRelationCode code := by
  decide

private theorem cover47_21 : ∀ q : IncreasingFourTail 45 (⟨21, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_21 (increasingFourValues (N := 47) ⟨⟨21, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a21
    (q : IncreasingFourTail 45 (⟨21, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨21, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_21 _ valid47_21 (cover47_21 q)

end MinModulus.SHCFiveCertificate.Generated
