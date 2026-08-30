import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_45 : List ℕ := [772]

private theorem valid51_45 : ∀ code ∈ codes51_45, validRelationCode code := by
  decide

private theorem cover51_45 : ∀ q : IncreasingFourTail 49 (⟨45, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_45 (increasingFourValues (N := 51) ⟨⟨45, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a45
    (q : IncreasingFourTail 49 (⟨45, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨45, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_45 _ valid51_45 (cover51_45 q)

end MinModulus.SHCFiveCertificate.Generated
