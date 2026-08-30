import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_34 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 77, 2631, 3911, 153, 773]

private theorem valid51_34 : ∀ code ∈ codes51_34, validRelationCode code := by
  decide

private theorem cover51_34 : ∀ q : IncreasingFourTail 49 (⟨34, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_34 (increasingFourValues (N := 51) ⟨⟨34, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a34
    (q : IncreasingFourTail 49 (⟨34, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨34, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_34 _ valid51_34 (cover51_34 q)

end MinModulus.SHCFiveCertificate.Generated
