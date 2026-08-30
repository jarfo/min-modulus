import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_16 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 4584, 4425, 4265, 278, 153, 773, 589, 403, 279, 4884, 4227, 2308, 2626, 642, 4232, 2468, 10, 2786, 321, 209, 1905, 4387, 518, 643, 2465, 2305, 2631, 85, 519, 1984, 11, 4876, 193, 1825, 2476, 2624, 1187, 3585, 2546, 2808, 465, 201, 6, 30, 705, 4544]

private theorem valid47_16 : ∀ code ∈ codes47_16, validRelationCode code := by
  decide

private theorem cover47_16 : ∀ q : IncreasingFourTail 45 (⟨16, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_16 (increasingFourValues (N := 47) ⟨⟨16, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a16
    (q : IncreasingFourTail 45 (⟨16, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨16, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_16 _ valid47_16 (cover47_16 q)

end MinModulus.SHCFiveCertificate.Generated
