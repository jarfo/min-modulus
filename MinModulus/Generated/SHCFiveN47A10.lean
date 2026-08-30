import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_10 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 2024, 2704, 3904, 403, 643, 2786, 153, 773, 4387, 4232, 2468, 589, 85, 2631, 4234, 337, 1825, 201, 4884, 577, 4265, 262, 522, 1665, 209, 713, 518, 321, 3765, 1905, 2305, 18, 10, 4425, 2465, 278, 2624, 2064, 4584, 523, 263, 19, 3586, 2808, 12, 519, 387, 3185, 3906, 20, 524, 770, 11, 4385, 93, 279, 386, 193, 28, 154, 774, 217, 897, 385, 401, 25, 5504]

private theorem valid47_10 : ∀ code ∈ codes47_10, validRelationCode code := by
  decide

private theorem cover47_10 : ∀ q : IncreasingFourTail 45 (⟨10, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_10 (increasingFourValues (N := 47) ⟨⟨10, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a10
    (q : IncreasingFourTail 45 (⟨10, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨10, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_10 _ valid47_10 (cover47_10 q)

end MinModulus.SHCFiveCertificate.Generated
