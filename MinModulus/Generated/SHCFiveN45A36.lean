import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_36 : List ℕ := [17, 521, 261, 772]

private theorem valid45_36 : ∀ code ∈ codes45_36, validRelationCode code := by
  decide

private theorem cover45_36 : ∀ q : IncreasingFourTail 43 (⟨36, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_36 (increasingFourValues (N := 45) ⟨⟨36, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a36
    (q : IncreasingFourTail 43 (⟨36, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨36, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_36 _ valid45_36 (cover45_36 q)

end MinModulus.SHCFiveCertificate.Generated
