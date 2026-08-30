import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_21 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 4227, 2308, 85, 589, 2631, 403, 643, 2786, 386, 93, 4387]

private theorem valid39_21 : ∀ code ∈ codes39_21, validRelationCode code := by
  decide

private theorem cover39_21 : ∀ q : IncreasingFourTail 37 (⟨21, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_21 (increasingFourValues (N := 39) ⟨⟨21, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a21
    (q : IncreasingFourTail 37 (⟨21, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨21, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_21 _ valid39_21 (cover39_21 q)

end MinModulus.SHCFiveCertificate.Generated
