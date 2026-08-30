import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_08 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 11, 279, 519, 85, 589, 2631, 4265, 2305, 403, 2786, 153, 773, 643, 2468, 4232, 278, 4387, 10, 518, 1825, 321, 4425, 713, 1905, 3904, 209, 19, 2465, 337, 523, 386, 5184, 1868, 577, 1907, 401, 4584, 3746, 20, 385]

private theorem valid37_08 : ∀ code ∈ codes37_08, validRelationCode code := by
  decide

private theorem cover37_08 : ∀ q : IncreasingFourTail 35 (⟨8, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_08 (increasingFourValues (N := 37) ⟨⟨8, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a08
    (q : IncreasingFourTail 35 (⟨8, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨8, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_08 _ valid37_08 (cover37_08 q)

end MinModulus.SHCFiveCertificate.Generated
