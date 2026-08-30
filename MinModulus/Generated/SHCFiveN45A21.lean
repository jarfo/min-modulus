import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_21 : List ℕ := [1185]

private theorem valid45_21 : ∀ code ∈ codes45_21, validRelationCode code := by
  decide

private theorem cover45_21 : ∀ q : IncreasingFourTail 43 (⟨21, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_21 (increasingFourValues (N := 45) ⟨⟨21, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a21
    (q : IncreasingFourTail 43 (⟨21, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨21, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_21 _ valid45_21 (cover45_21 q)

end MinModulus.SHCFiveCertificate.Generated
