import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_38 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 85, 77, 386, 770]

private theorem valid51_38 : ∀ code ∈ codes51_38, validRelationCode code := by
  decide

private theorem cover51_38 : ∀ q : IncreasingFourTail 49 (⟨38, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_38 (increasingFourValues (N := 51) ⟨⟨38, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a38
    (q : IncreasingFourTail 49 (⟨38, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨38, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_38 _ valid51_38 (cover51_38 q)

end MinModulus.SHCFiveCertificate.Generated
