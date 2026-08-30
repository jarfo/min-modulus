import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_26 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 85, 77, 386, 770]

private theorem valid39_26 : ∀ code ∈ codes39_26, validRelationCode code := by
  decide

private theorem cover39_26 : ∀ q : IncreasingFourTail 37 (⟨26, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_26 (increasingFourValues (N := 39) ⟨⟨26, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a26
    (q : IncreasingFourTail 37 (⟨26, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨26, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_26 _ valid39_26 (cover39_26 q)

end MinModulus.SHCFiveCertificate.Generated
