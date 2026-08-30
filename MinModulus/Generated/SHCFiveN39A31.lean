import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_31 : List ℕ := [17, 521, 770]

private theorem valid39_31 : ∀ code ∈ codes39_31, validRelationCode code := by
  decide

private theorem cover39_31 : ∀ q : IncreasingFourTail 37 (⟨31, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_31 (increasingFourValues (N := 39) ⟨⟨31, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a31
    (q : IncreasingFourTail 37 (⟨31, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨31, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_31 _ valid39_31 (cover39_31 q)

end MinModulus.SHCFiveCertificate.Generated
