import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_30 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 773, 403, 643, 4387, 2786, 2631, 2468, 89, 2866, 5191, 898, 387]

private theorem valid51_30 : ∀ code ∈ codes51_30, validRelationCode code := by
  decide

private theorem cover51_30 : ∀ q : IncreasingFourTail 49 (⟨30, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_30 (increasingFourValues (N := 51) ⟨⟨30, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a30
    (q : IncreasingFourTail 49 (⟨30, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨30, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_30 _ valid51_30 (cover51_30 q)

end MinModulus.SHCFiveCertificate.Generated
