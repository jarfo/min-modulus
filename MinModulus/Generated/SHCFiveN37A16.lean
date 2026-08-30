import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_16 : List ℕ := [6, 193, 17, 521, 261, 1984, 1865, 2545, 3745, 772, 22, 2786, 402, 465, 526, 3344, 589, 153, 773, 2706]

private theorem valid37_16 : ∀ code ∈ codes37_16, validRelationCode code := by
  decide

private theorem cover37_16 : ∀ q : IncreasingFourTail 35 (⟨16, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_16 (increasingFourValues (N := 37) ⟨⟨16, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a16
    (q : IncreasingFourTail 35 (⟨16, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨16, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_16 _ valid37_16 (cover37_16 q)

end MinModulus.SHCFiveCertificate.Generated
