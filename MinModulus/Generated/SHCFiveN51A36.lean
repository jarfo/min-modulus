import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_36 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308]

private theorem valid51_36 : ∀ code ∈ codes51_36, validRelationCode code := by
  decide

private theorem cover51_36 : ∀ q : IncreasingFourTail 49 (⟨36, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_36 (increasingFourValues (N := 51) ⟨⟨36, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a36
    (q : IncreasingFourTail 49 (⟨36, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨36, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_36 _ valid51_36 (cover51_36 q)

end MinModulus.SHCFiveCertificate.Generated
