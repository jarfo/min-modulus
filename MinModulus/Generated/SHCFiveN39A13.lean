import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_13 : List ℕ := [17, 521, 261, 131, 1186, 772, 4584, 4265, 402, 278, 713, 4425, 589, 403, 279, 4884, 153, 773, 1347, 2468, 2626, 85, 4234, 4387, 642, 2308, 10, 209, 2305, 4227, 2786, 321, 1905, 4232, 518, 28, 1984, 2465, 770, 262, 577]

private theorem valid39_13 : ∀ code ∈ codes39_13, validRelationCode code := by
  decide

private theorem cover39_13 : ∀ q : IncreasingFourTail 37 (⟨13, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_13 (increasingFourValues (N := 39) ⟨⟨13, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a13
    (q : IncreasingFourTail 37 (⟨13, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨13, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_13 _ valid39_13 (cover39_13 q)

end MinModulus.SHCFiveCertificate.Generated
