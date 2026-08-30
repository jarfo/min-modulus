import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_18 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 772, 4227, 2308, 3585, 642, 3745, 402, 2626, 1865, 2545, 773, 2468, 4387, 4232, 85, 589, 2631, 153, 643, 4884, 2786, 403, 1868, 5025, 518, 4885, 10, 278, 385, 321, 519, 3344, 4544, 209, 4265, 22, 713, 279, 4066, 1506, 26]

private theorem valid47_18 : ∀ code ∈ codes47_18, validRelationCode code := by
  decide

private theorem cover47_18 : ∀ q : IncreasingFourTail 45 (⟨18, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_18 (increasingFourValues (N := 47) ⟨⟨18, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a18
    (q : IncreasingFourTail 45 (⟨18, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨18, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_18 _ valid47_18 (cover47_18 q)

end MinModulus.SHCFiveCertificate.Generated
