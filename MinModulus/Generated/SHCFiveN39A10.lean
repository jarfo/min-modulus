import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_10 : List ℕ := [17, 521, 261, 131, 772, 402, 279, 278, 713, 4425, 4265, 4584, 589, 403, 153, 773, 4884, 642, 2308, 2626, 4227, 643, 2468, 2786, 4232, 209, 2465, 321, 1905, 2064, 2624, 4234, 4387, 1186, 10, 518, 85, 2631, 11, 2305, 3585, 770, 4870, 3586, 12, 18, 2546, 193, 897]

private theorem valid39_10 : ∀ code ∈ codes39_10, validRelationCode code := by
  decide

private theorem cover39_10 : ∀ q : IncreasingFourTail 37 (⟨10, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_10 (increasingFourValues (N := 39) ⟨⟨10, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a10
    (q : IncreasingFourTail 37 (⟨10, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨10, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_10 _ valid39_10 (cover39_10 q)

end MinModulus.SHCFiveCertificate.Generated
