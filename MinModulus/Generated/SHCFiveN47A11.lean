import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_11 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 1347, 402, 4227, 2308, 10, 2305, 278, 518, 4265, 2624, 1187, 11, 321, 2465, 85, 2631, 2786, 643, 773, 589, 4425, 209, 713, 1905, 4232, 153, 4387, 403, 2468, 519, 279, 1186, 4584, 1825, 4884, 4234, 2064, 3904, 770, 27, 3907, 18, 201, 385, 3264, 1546, 386, 387, 19, 12, 2024, 2954, 577, 2866, 1993, 193, 337, 1665, 2546, 3767, 28, 262, 89, 641, 769, 4087, 20, 154, 526, 897, 401, 25]

private theorem valid47_11 : ∀ code ∈ codes47_11, validRelationCode code := by
  decide

private theorem cover47_11 : ∀ q : IncreasingFourTail 45 (⟨11, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_11 (increasingFourValues (N := 47) ⟨⟨11, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a11
    (q : IncreasingFourTail 45 (⟨11, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨11, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_11 _ valid47_11 (cover47_11 q)

end MinModulus.SHCFiveCertificate.Generated
