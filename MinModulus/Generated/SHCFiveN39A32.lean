import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_32 : List ℕ := [17, 402]

private theorem valid39_32 : ∀ code ∈ codes39_32, validRelationCode code := by
  decide

private theorem cover39_32 : ∀ q : IncreasingFourTail 37 (⟨32, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_32 (increasingFourValues (N := 39) ⟨⟨32, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a32
    (q : IncreasingFourTail 37 (⟨32, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨32, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_32 _ valid39_32 (cover39_32 q)

end MinModulus.SHCFiveCertificate.Generated
