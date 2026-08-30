import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_15 : List ℕ := [17, 521, 261, 131, 1186, 772, 4584, 4265, 278, 402, 713, 4425, 279, 589, 403, 4884, 153, 773, 2546, 4227, 2308, 2624, 2064, 2626, 642, 4232, 85, 4387, 209, 2631, 2468, 643, 321, 2465, 2786, 1905, 2305, 1825, 518, 10, 519, 1527, 1546, 4234, 26, 1665, 577, 5025, 262, 1984, 3904, 201, 385, 5036, 833, 337, 386, 18, 522, 449, 193, 897]

private theorem valid47_15 : ∀ code ∈ codes47_15, validRelationCode code := by
  decide

private theorem cover47_15 : ∀ q : IncreasingFourTail 45 (⟨15, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_15 (increasingFourValues (N := 47) ⟨⟨15, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a15
    (q : IncreasingFourTail 45 (⟨15, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨15, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_15 _ valid47_15 (cover47_15 q)

end MinModulus.SHCFiveCertificate.Generated
