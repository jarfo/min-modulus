import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_41 : List ℕ := [17, 521, 261, 131, 772]

private theorem valid51_41 : ∀ code ∈ codes51_41, validRelationCode code := by
  decide

private theorem cover51_41 : ∀ q : IncreasingFourTail 49 (⟨41, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_41 (increasingFourValues (N := 51) ⟨⟨41, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a41
    (q : IncreasingFourTail 49 (⟨41, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨41, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_41 _ valid51_41 (cover51_41 q)

end MinModulus.SHCFiveCertificate.Generated
