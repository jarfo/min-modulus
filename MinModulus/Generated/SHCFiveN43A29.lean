import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_29 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 403, 589, 2706]

private theorem valid43_29 : ∀ code ∈ codes43_29, validRelationCode code := by
  decide

private theorem cover43_29 : ∀ q : IncreasingFourTail 41 (⟨29, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_29 (increasingFourValues (N := 43) ⟨⟨29, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a29
    (q : IncreasingFourTail 41 (⟨29, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨29, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_29 _ valid43_29 (cover43_29 q)

end MinModulus.SHCFiveCertificate.Generated
