import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_22 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 77, 2631, 3911, 153, 773]

private theorem valid39_22 : ∀ code ∈ codes39_22, validRelationCode code := by
  decide

private theorem cover39_22 : ∀ q : IncreasingFourTail 37 (⟨22, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_22 (increasingFourValues (N := 39) ⟨⟨22, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a22
    (q : IncreasingFourTail 37 (⟨22, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨22, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_22 _ valid39_22 (cover39_22 q)

end MinModulus.SHCFiveCertificate.Generated
