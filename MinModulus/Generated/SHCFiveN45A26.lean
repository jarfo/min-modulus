import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_26 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 3765, 4234, 85, 643, 4387, 4232, 589, 153, 403, 898, 3264, 386, 449, 93]

private theorem valid45_26 : ∀ code ∈ codes45_26, validRelationCode code := by
  decide

private theorem cover45_26 : ∀ q : IncreasingFourTail 43 (⟨26, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_26 (increasingFourValues (N := 45) ⟨⟨26, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a26
    (q : IncreasingFourTail 43 (⟨26, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨26, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_26 _ valid45_26 (cover45_26 q)

end MinModulus.SHCFiveCertificate.Generated
