import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_30 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 85, 77, 386, 770]

private theorem valid43_30 : ∀ code ∈ codes43_30, validRelationCode code := by
  decide

private theorem cover43_30 : ∀ q : IncreasingFourTail 41 (⟨30, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_30 (increasingFourValues (N := 43) ⟨⟨30, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a30
    (q : IncreasingFourTail 41 (⟨30, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨30, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_30 _ valid43_30 (cover43_30 q)

end MinModulus.SHCFiveCertificate.Generated
