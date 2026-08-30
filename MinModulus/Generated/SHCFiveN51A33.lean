import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_33 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 4227, 2308, 85, 589, 2631, 403, 643, 2786, 386, 93, 4387]

private theorem valid51_33 : ∀ code ∈ codes51_33, validRelationCode code := by
  decide

private theorem cover51_33 : ∀ q : IncreasingFourTail 49 (⟨33, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_33 (increasingFourValues (N := 51) ⟨⟨33, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a33
    (q : IncreasingFourTail 49 (⟨33, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨33, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_33 _ valid51_33 (cover51_33 q)

end MinModulus.SHCFiveCertificate.Generated
