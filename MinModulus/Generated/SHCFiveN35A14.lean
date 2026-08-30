import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes35_14 : List ℕ := [17, 521, 261, 131, 7, 6, 193, 1984, 3585, 3745, 465, 2476, 4227, 772, 705, 2308, 1865, 2545, 386, 3344]

private theorem valid35_14 : ∀ code ∈ codes35_14, validRelationCode code := by
  decide

private theorem cover35_14 : ∀ q : IncreasingFourTail 33 (⟨14, by norm_num⟩ : Fin 30),
    coveredNat 35 codes35_14 (increasingFourValues (N := 35) ⟨⟨14, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate35_a14
    (q : IncreasingFourTail 33 (⟨14, by norm_num⟩ : Fin 30)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 35 (increasingFourValues (N := 35) ⟨⟨14, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 35 codes35_14 _ valid35_14 (cover35_14 q)

end MinModulus.SHCFiveCertificate.Generated
