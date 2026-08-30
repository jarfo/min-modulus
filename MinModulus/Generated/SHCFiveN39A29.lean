import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_29 : List ℕ := [17, 521, 261, 131, 772]

private theorem valid39_29 : ∀ code ∈ codes39_29, validRelationCode code := by
  decide

private theorem cover39_29 : ∀ q : IncreasingFourTail 37 (⟨29, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_29 (increasingFourValues (N := 39) ⟨⟨29, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a29
    (q : IncreasingFourTail 37 (⟨29, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨29, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_29 _ valid39_29 (cover39_29 q)

end MinModulus.SHCFiveCertificate.Generated
