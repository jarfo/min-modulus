/-
# An actual negative-one extra forces coherent shorter-prefix lifts

Normalize the lifted zero to zero. Validity forces the lifted negative
one plus the lifted one to be the half modulus. A wrong lift at any later
SI coordinate would then make that coordinate and the negative-one extra
sum to twice its predecessor, contradicting validity. Thus the whole
shorter prefix is coherent under the actual lifted-one multiplier.
-/
import MinModulus.SIQuarterPrefix

namespace MinModulus
open Finset

/-- A valid tuple has no double equal to the sum of two distinct entries. -/
theorem not_validTuple_of_double_eq_distinct_pair
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (a b c : Fin n) (hab : a ≠ b) (heq : 2 • g c = g a + g b) : ¬ ValidTuple g := by
  classical
  let R := (Finset.univ.erase a).erase b
  have hb : b ∈ Finset.univ.erase a := by simp [hab.symm]
  have hcard : R.card + 2 = n := by
    dsimp [R]
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a)]
    have hn : 2 ≤ n := by
      have hcard := Finset.card_le_card (show ({a, b} : Finset (Fin n)) ⊆ Finset.univ by simp)
      simpa [hab] using hcard
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hsum : (∑ i ∈ R, g i) + g a + g b = ∑ i, g i := by
    have h1 := Finset.sum_erase_add (Finset.univ.erase a) g hb
    have h2 := Finset.sum_erase_add Finset.univ g (Finset.mem_univ a)
    dsimp only [R]
    rw [show (∑ i ∈ (Finset.univ.erase a).erase b, g i) + g a + g b =
      ((∑ i ∈ (Finset.univ.erase a).erase b, g i) + g b) + g a by abel, h1, h2]
  let s := R.val + Multiset.replicate 2 c
  intro hg
  have hscard : s.card = n := by simpa [s] using hcard
  have hssum : (s.map g).sum = ∑ i, g i := by
    simp only [s, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate, Multiset.sum_replicate]
    rw [heq]
    simpa only [Finset.sum_eq_multiset_sum, add_assoc] using hsum
  have hc := multiset_count_eq_one_of_validTuple g hg s hscard hssum c
  simp only [s, Multiset.count_add, Multiset.count_replicate_self] at hc
  omega

/-- With an actual negative-one extra, validity forces every shorter-prefix
lift to agree with the multiplier supplied by its lifted one. -/
theorem scaled_fixed_short_prefix_of_valid_si_lifts_neg_one
    {m M : ℕ} [NeZero M] (hm : 2 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc.castSucc) = (a i.val : ZMod M))
    (hzero : g ((⟨0, by omega⟩ : Fin m).castSucc.castSucc) = 0)
    (hy : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) = -1) :
    ∀ i : Fin m, g i.castSucc.castSucc =
      g ((⟨1, by omega⟩ : Fin m).castSucc.castSucc) * (a i.val : ZMod (2 * M)) := by
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let one : Fin (m + 2) := (⟨1, by omega⟩ : Fin m).castSucc.castSucc
  let zero : Fin (m + 2) := (⟨0, by omega⟩ : Fin m).castSucc.castSucc
  let y := Fin.last (m + 1)
  let c := g one
  have hc : π c = 1 := (hprefix ⟨1, by omega⟩).trans (by norm_num [a])
  have hysum : g y + c = (M : ZMod (2 * M)) := by
    have hproj : π (g y + c) = π 0 := by rw [map_add, hy, hc, map_zero]; simp
    rcases eq_or_eq_add_half_of_castHom_eq (g y + c) 0 hproj with hz | hh
    · exact False.elim (not_validTuple_of_double_eq_distinct_pair g y one zero
        (Fin.castSucc_ne_last ((⟨1, by omega⟩ : Fin m).castSucc)).symm
        (by rw [hzero, smul_zero]; exact hz.symm) hg)
    · simpa using hh
  have h2c : 2 * c = (2 : ZMod (2 * M)) := by
    have := nsmul_eq_of_even_of_castHom_eq (by decide : Even 2) c 1
      (by simpa only [map_one] using hc)
    simpa only [nsmul_eq_mul, Nat.cast_ofNat, mul_one] using this
  intro i
  by_cases hi0 : i.val = 0
  · have hi : i = ⟨0, by omega⟩ := Fin.ext hi0
    rw [hi]
    simp only [hzero, a, pow_zero, Nat.sub_self, Nat.cast_zero, mul_zero]
  · have hproj : π (g i.castSucc.castSucc) = π (c * (a i.val : ZMod (2 * M))) := by
      rw [map_mul, map_natCast, hc, one_mul]
      exact hprefix i
    rcases eq_or_eq_add_half_of_castHom_eq _ _ hproj with heq | hwrong
    · exact heq
    · let p : Fin m := ⟨i.val - 1, by omega⟩
      have h2p : 2 • g p.castSucc.castSucc = 2 * (a p.val : ZMod (2 * M)) := by
        have := nsmul_eq_of_even_of_castHom_eq (by decide : Even 2)
          (g p.castSucc.castSucc) (a p.val : ZMod (2 * M))
          (by simpa only [map_natCast] using hprefix p)
        simpa only [nsmul_eq_mul, Nat.cast_ofNat] using this
      have hnat : a i.val = 2 * a p.val + 1 := by
        have hp : 2 ^ i.val = 2 * 2 ^ (i.val - 1) := by rw [← pow_succ']; congr 1; omega
        have hpPos : 0 < 2 ^ (i.val - 1) := by positivity
        dsimp [p, a]
        omega
      have ha : (a i.val : ZMod (2 * M)) = 2 * (a p.val : ZMod (2 * M)) + 1 := by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
          congrArg (fun k : ℕ ↦ (k : ZMod (2 * M))) hnat
      have hpair : 2 • g p.castSucc.castSucc = g i.castSucc.castSucc + g y := by
        rw [h2p, hwrong, ha]
        have hh := half_add_half (M := M) rfl
        linear_combination -hysum - hh - (a p.val : ZMod (2 * M)) * h2c
      exact False.elim (not_validTuple_of_double_eq_distinct_pair g i.castSucc.castSucc y
        p.castSucc.castSucc (Fin.castSucc_ne_last i.castSucc) hpair hg)

/-- Translating by the actual lifted zero gives a canonical affine
coherent prefix, extracted from validity rather than assumed. -/
theorem affine_scaled_short_prefix_of_valid_si_lifts_neg_one
    {m M : ℕ} [NeZero M] (hm : 2 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc.castSucc) = (a i.val : ZMod M))
    (hy : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) = -1) :
    ∀ i : Fin m, g i.castSucc.castSucc =
      (g ((⟨1, by omega⟩ : Fin m).castSucc.castSucc) -
        g ((⟨0, by omega⟩ : Fin m).castSucc.castSucc)) * (a i.val : ZMod (2 * M)) +
        g ((⟨0, by omega⟩ : Fin m).castSucc.castSucc) := by
  let b := g ((⟨0, by omega⟩ : Fin m).castSucc.castSucc)
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  have hb : π b = 0 := (hprefix ⟨0, by omega⟩).trans (by norm_num [a])
  have hnorm := scaled_fixed_short_prefix_of_valid_si_lifts_neg_one hm
    (fun i ↦ g i - b) (validTuple_sub_const g hg b)
    (by intro i; rw [map_sub, hprefix, hb, sub_zero])
    (by exact sub_self b) (by rw [map_sub, hy, hb, sub_zero])
  intro i
  exact sub_eq_iff_eq_add.mp (hnorm i)

/-- A negative-one quotient extra gives the full global lower bound for
arbitrary independent shorter-prefix lifts, at every positive half modulus. -/
theorem global_lower_bound_of_valid_si_lifts_neg_one
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc.castSucc) = (a i.val : ZMod M))
    (hy : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) = -1) :
    globalBound (m + 2) ≤ 2 * M := by
  have hM := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  exact global_lower_bound_of_valid_scaled_fixed_short_prefix hm g hg (Equiv.refl _)
    (g ((⟨1, by omega⟩ : Fin m).castSucc.castSucc) -
      g ((⟨0, by omega⟩ : Fin m).castSucc.castSucc))
    (g ((⟨0, by omega⟩ : Fin m).castSucc.castSucc))
    (affine_scaled_short_prefix_of_valid_si_lifts_neg_one (by omega) g hg hprefix hy)

/-- Direct G3 exclusion after actual coherent-prefix extraction. -/
theorem not_validTuple_exceptional_of_si_lifts_neg_one
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g i.castSucc.castSucc) = (a i.val : ZMod (globalBound (m + 1))))
    (hy : ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
      (g (Fin.last (m + 1))) = -1) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (globalBound (m + 1)) := ⟨by omega⟩
  have hbound := global_lower_bound_of_valid_si_lifts_neg_one hm g hg hprefix hy
  have hcrit := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ m + 1) hnpow
  change 2 * globalBound (m + 1) < globalBound (m + 2) at hcrit
  omega

/-- Affine quotient transport leaves the negative-one extraction and
exceptional exclusion valid for arbitrary original lift bits. -/
theorem not_validTuple_exceptional_of_quotient_affine_short_prefix_neg_one
    {m : ℕ} (hm : 3 ≤ m) (hnpow : 2 ^ Nat.log 2 (m + 2) ≠ m + 2)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (e : Equiv.Perm (Fin (m + 2)))
    (φ : ZMod (globalBound (m + 1)) ≃+ ZMod (globalBound (m + 1)))
    (b : ZMod (globalBound (m + 1)))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g (e i.castSucc.castSucc)) = φ (a i.val) + b)
    (hy : ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
      (g (e (Fin.last (m + 1)))) = φ (-1) + b) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (globalBound (m + 1)) := ⟨by omega⟩
  letI : NeZero (2 * globalBound (m + 1)) := ⟨by omega⟩
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_lift_castHom (dvd_mul_left (globalBound (m + 1)) 2) φ
  let B : ZMod (2 * globalBound (m + 1)) := b.val
  have hv := validTuple_sub_const (fun i ↦ g (e i)) (validTuple_embedding e.toEmbedding g hg) B
  have hw := validTuple_comp hv Φ.symm.toAddMonoidHom Φ.symm.injective
  apply not_validTuple_exceptional_of_si_lifts_neg_one hm hnpow
    (fun i ↦ Φ.symm (g (e i) - B)) _ _ hw
  · intro i
    apply φ.injective
    rw [← hΦ, Φ.apply_symm_apply, map_sub, hprefix]
    simp [B]
  · apply φ.injective
    rw [← hΦ, Φ.apply_symm_apply, map_sub, hy]
    simp [B]

end MinModulus
