import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_43 : List ℕ := [17, 521, 770]

private theorem valid51_43 : ∀ code ∈ codes51_43, validRelationCode code := by
  decide

private theorem cover51_43 : ∀ q : IncreasingFourTail 49 (⟨43, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_43 (increasingFourValues (N := 51) ⟨⟨43, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a43
    (q : IncreasingFourTail 49 (⟨43, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨43, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_43 _ valid51_43 (cover51_43 q)

end MinModulus.SHCFiveCertificate.Generated
