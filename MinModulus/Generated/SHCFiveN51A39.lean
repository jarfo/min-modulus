import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_39 : List ℕ := [17, 521, 261, 131, 772, 642, 2626]

private theorem valid51_39 : ∀ code ∈ codes51_39, validRelationCode code := by
  decide

private theorem cover51_39 : ∀ q : IncreasingFourTail 49 (⟨39, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_39 (increasingFourValues (N := 51) ⟨⟨39, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a39
    (q : IncreasingFourTail 49 (⟨39, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨39, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_39 _ valid51_39 (cover51_39 q)

end MinModulus.SHCFiveCertificate.Generated
