import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_24 : List ℕ := [1185]

private theorem valid51_24 : ∀ code ∈ codes51_24, validRelationCode code := by
  decide

private theorem cover51_24 : ∀ q : IncreasingFourTail 49 (⟨24, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_24 (increasingFourValues (N := 51) ⟨⟨24, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a24
    (q : IncreasingFourTail 49 (⟨24, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨24, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_24 _ valid51_24 (cover51_24 q)

end MinModulus.SHCFiveCertificate.Generated
