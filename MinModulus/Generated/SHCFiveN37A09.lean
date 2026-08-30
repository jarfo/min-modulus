import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_09 : List ℕ := [17, 521, 261, 131, 772, 278, 4265, 402, 4584, 279, 713, 4425, 589, 403, 153, 773, 4884, 642, 2308, 85, 2631, 643, 2626, 4227, 2786, 2465, 1905, 2468, 518, 209, 321, 2305, 10, 2624, 19, 4387, 4232, 386, 385, 262, 387, 770, 522, 523]

private theorem valid37_09 : ∀ code ∈ codes37_09, validRelationCode code := by
  decide

private theorem cover37_09 : ∀ q : IncreasingFourTail 35 (⟨9, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_09 (increasingFourValues (N := 37) ⟨⟨9, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a09
    (q : IncreasingFourTail 35 (⟨9, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨9, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_09 _ valid37_09 (cover37_09 q)

end MinModulus.SHCFiveCertificate.Generated
