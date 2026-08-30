import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_16 : List ℕ := [17, 521, 261, 131, 7, 6, 193, 1984, 3585, 3745, 1865, 2545, 4227, 772, 465, 2476, 2308, 705, 386, 2706, 642, 1506, 22, 526, 402, 14, 833, 85]

private theorem valid39_16 : ∀ code ∈ codes39_16, validRelationCode code := by
  decide

private theorem cover39_16 : ∀ q : IncreasingFourTail 37 (⟨16, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_16 (increasingFourValues (N := 39) ⟨⟨16, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a16
    (q : IncreasingFourTail 37 (⟨16, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨16, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_16 _ valid39_16 (cover39_16 q)

end MinModulus.SHCFiveCertificate.Generated
