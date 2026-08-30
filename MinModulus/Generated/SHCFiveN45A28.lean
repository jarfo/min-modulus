import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_28 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 77, 2631, 3911, 153, 773]

private theorem valid45_28 : ∀ code ∈ codes45_28, validRelationCode code := by
  decide

private theorem cover45_28 : ∀ q : IncreasingFourTail 43 (⟨28, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_28 (increasingFourValues (N := 45) ⟨⟨28, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a28
    (q : IncreasingFourTail 43 (⟨28, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨28, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_28 _ valid45_28 (cover45_28 q)

end MinModulus.SHCFiveCertificate.Generated
