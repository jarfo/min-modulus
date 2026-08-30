import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_32 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 85, 77, 386, 770]

private theorem valid45_32 : ∀ code ∈ codes45_32, validRelationCode code := by
  decide

private theorem cover45_32 : ∀ q : IncreasingFourTail 43 (⟨32, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_32 (increasingFourValues (N := 45) ⟨⟨32, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a32
    (q : IncreasingFourTail 43 (⟨32, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨32, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_32 _ valid45_32 (cover45_32 q)

end MinModulus.SHCFiveCertificate.Generated
