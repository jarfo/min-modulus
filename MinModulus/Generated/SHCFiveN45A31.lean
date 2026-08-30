import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_31 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 403, 589, 2706]

private theorem valid45_31 : ∀ code ∈ codes45_31, validRelationCode code := by
  decide

private theorem cover45_31 : ∀ q : IncreasingFourTail 43 (⟨31, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_31 (increasingFourValues (N := 45) ⟨⟨31, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a31
    (q : IncreasingFourTail 43 (⟨31, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨31, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_31 _ valid45_31 (cover45_31 q)

end MinModulus.SHCFiveCertificate.Generated
