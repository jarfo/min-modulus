import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_29 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 85, 153, 773, 643, 402, 4227, 386, 770, 1667]

private theorem valid45_29 : ∀ code ∈ codes45_29, validRelationCode code := by
  decide

private theorem cover45_29 : ∀ q : IncreasingFourTail 43 (⟨29, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_29 (increasingFourValues (N := 45) ⟨⟨29, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a29
    (q : IncreasingFourTail 43 (⟨29, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨29, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_29 _ valid45_29 (cover45_29 q)

end MinModulus.SHCFiveCertificate.Generated
