import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_18 : List ℕ := [17, 521, 261, 131, 7, 6, 193, 1984, 3585, 3745, 1865, 2545, 4227, 465, 2476, 772, 2308, 705, 643, 386, 2706, 642, 402, 3344, 1506, 2626, 403, 773, 2786, 3946, 4387, 770]

private theorem valid43_18 : ∀ code ∈ codes43_18, validRelationCode code := by
  decide

private theorem cover43_18 : ∀ q : IncreasingFourTail 41 (⟨18, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_18 (increasingFourValues (N := 43) ⟨⟨18, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a18
    (q : IncreasingFourTail 41 (⟨18, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨18, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_18 _ valid43_18 (cover43_18 q)

end MinModulus.SHCFiveCertificate.Generated
