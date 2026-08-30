import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_00 : List ℕ := [1344]

private theorem valid39_00 : ∀ code ∈ codes39_00, validRelationCode code := by
  decide

private theorem cover39_00 : ∀ q : IncreasingFourTail 37 (⟨0, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_00 (increasingFourValues (N := 39) ⟨⟨0, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a00
    (q : IncreasingFourTail 37 (⟨0, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨0, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_00 _ valid39_00 (cover39_00 q)

end MinModulus.SHCFiveCertificate.Generated
