import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_33 : List ℕ := [17, 521, 770]

private theorem valid41_33 : ∀ code ∈ codes41_33, validRelationCode code := by
  decide

private theorem cover41_33 : ∀ q : IncreasingFourTail 39 (⟨33, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_33 (increasingFourValues (N := 41) ⟨⟨33, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a33
    (q : IncreasingFourTail 39 (⟨33, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨33, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_33 _ valid41_33 (cover41_33 q)

end MinModulus.SHCFiveCertificate.Generated
