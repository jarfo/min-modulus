import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_20 : List ℕ := [17, 521, 261, 131, 7, 6, 193, 1984, 3585, 3745, 1865, 2545, 4227, 465, 2476, 772, 2308, 705, 3344, 773, 526, 4885, 403, 2468, 4544, 4387, 4232, 1828, 3273, 643, 23, 402, 22, 527, 1507, 642, 589]

private theorem valid47_20 : ∀ code ∈ codes47_20, validRelationCode code := by
  decide

private theorem cover47_20 : ∀ q : IncreasingFourTail 45 (⟨20, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_20 (increasingFourValues (N := 47) ⟨⟨20, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a20
    (q : IncreasingFourTail 45 (⟨20, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨20, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_20 _ valid47_20 (cover47_20 q)

end MinModulus.SHCFiveCertificate.Generated
