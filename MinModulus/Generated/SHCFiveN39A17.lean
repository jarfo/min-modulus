import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_17 : List ℕ := [6, 193, 17, 521, 261, 1984, 1865, 2545, 3745, 772, 526, 22, 2786, 4227, 2308, 402, 642, 77, 2626, 3911, 589, 386, 14]

private theorem valid39_17 : ∀ code ∈ codes39_17, validRelationCode code := by
  decide

private theorem cover39_17 : ∀ q : IncreasingFourTail 37 (⟨17, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_17 (increasingFourValues (N := 39) ⟨⟨17, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a17
    (q : IncreasingFourTail 37 (⟨17, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨17, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_17 _ valid39_17 (cover39_17 q)

end MinModulus.SHCFiveCertificate.Generated
