import MinModulus.SIThreeOddTargetPacking

/-!
# Index-two coherent prefixes with three arbitrary extras

All parity patterns are consumed for n >= 8. Two even extras give an actual
valid two-extra child: its top two binary residues have a small admissible
gap, while lower moduli give actual whole-child SI extraction. One even
extra is excluded by the large-fibre cover, and zero even extras satisfy
the first-even bound by actual target packing. Thus subbinary validity
implies fixed validity at the same modulus, and the global and every exact
even-stratum lower bound follow. Unit-affine transport is in the original
modulus; arbitrary prefix extraction and other subgroup indices are not
asserted here.
-/

namespace MinModulus
open Finset

/-- Dividing two actual even extras together with the doubled prefix
produces a valid coherent two-extra child at half the modulus. -/
theorem exists_valid_child_of_doubled_three_extra_two_even
    {m M : ℕ} [NeZero M]
    (g : Fin (m+3) → ZMod (2*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom 2 M (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last m).castSucc.castSucc) = 0)
    (hy : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last (m+1)).castSucc) = 0) :
    ∃ u : Fin (m+2) → ZMod M, ValidTuple u ∧
      (∀ i : Fin m, u i.castSucc.castSucc = (a i.val : ZMod M)) ∧
      ∀ i, zmodScaleHom 2 M (u i) = g i.castSucc := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  obtain ⟨x, hx'⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hx
  obtain ⟨y, hy'⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hy
  let u : Fin (m+2) → ZMod M := Fin.lastCases y (Fin.lastCases x (fun i : Fin m ↦ (a i.val : ZMod M)))
  have hu (i : Fin (m+2)) : zmodScaleHom 2 M (u i) = g i.castSucc := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [u, Fin.lastCases_last] using hy'
    · refine Fin.lastCases ?_ (fun k ↦ ?_) j
      · simpa only [u, Fin.lastCases_castSucc, Fin.lastCases_last] using hx'
      · simpa only [u, Fin.lastCases_castSucc] using (hpref k).symm
  refine ⟨u, ?_, by intro i; simp only [u, Fin.lastCases_castSucc], hu⟩
  apply validTuple_of_comp (zmodScaleHom 2 M)
  have hv := validTuple_embedding ⟨Fin.castSucc, Fin.castSucc_injective (m+2)⟩ g hg
  change ValidTuple (fun i : Fin (m+2) ↦ g i.castSucc) at hv
  simpa only [hu] using hv

/-- Two same-parity extras give fixed validity at the original subbinary
modulus. The child either has a small admissible gap or its actual whole
SI structure is extracted and mapped back to the original tuple. -/
theorem valid_fixed_of_valid_doubled_three_extra_two_even_subbinary
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m)
    (g : Fin (m+3) → ZMod (2*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom 2 M (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last m).castSucc.castSucc) = 0)
    (hy : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last (m+1)).castSucc) = 0)
    (hupper : 2*M < 2^(m+3)) : Valid (m+3) (2*M) := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2*M) := ⟨by omega⟩
  have hpow : 2^(m+3) = 2*2^(m+2) := by rw [show m+3=(m+2)+1 by omega, pow_succ']
  have hMsmall : M < 2^(m+2) := by omega
  obtain ⟨u, hu, hup, humap⟩ := exists_valid_child_of_doubled_three_extra_two_even g hg hpref hx hy
  by_cases hlow : M ≤ 2^(m+2)-3
  · obtain ⟨p, hp⟩ := exists_perm_fixed_of_valid_fixed_short_prefix_of_modulus_le hm hlow u hu hup
    let E : Equiv.Perm (Fin (m+3)) :=
      (finSuccEquiv' (Fin.last (m+2))).trans
        ((Equiv.optionCongr p).trans (finSuccEquiv' (Fin.last (m+2))).symm)
    have hE (i : Fin (m+2)) : E i.castSucc = (p i).castSucc := by
      simp only [E, Equiv.trans_apply, finSuccEquiv'_last_apply_castSucc, Equiv.optionCongr_apply]
      apply (finSuccEquiv' (Fin.last (m+2))).injective
      rw [Equiv.apply_symm_apply, finSuccEquiv'_last_apply_castSucc]
      rfl
    apply valid_fixed_of_valid_scaled_fixed_prefix_lt_two_pow (by omega : 2 ≤ m+2)
      g hg E 2 0 ?_ hupper
    intro i
    rw [hE, ← humap, hp, zmodScaleHom_natCast]
    simp only [Nat.cast_mul, Nat.cast_ofNat, add_zero]
  · have hfixed := valid_fixed_of_valid_scaled_fixed_short_prefix_lt_two_pow (by omega : 3 ≤ m)
      u hu (Equiv.refl _) 1 0 (by intro i; simpa using hup i) hMsmall
    have hMtwo : 2 ≤ M := by
      have hc := Fintype.card_le_of_injective _ (validTuple_injective u hu)
      simp only [Fintype.card_fin, ZMod.card] at hc
      omega
    obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_fixed_lt_two_pow
      (by omega : 3 ≤ m+2) hMtwo hMsmall hfixed
    have hbudget : 2^t ≤ 2 := by
      have hpowt := Nat.pow_le_pow_right (by omega : 1 ≤ (2:ℕ)) ht.le
      omega
    have hgap2 : 2*M = 2^(m+3)-2^(t+1) := by
      rw [hpow, hgap, Nat.mul_sub_left_distrib, show 2^(t+1)=2*2^t from pow_succ' 2 t]
    rw [hgap2]
    apply valid_gap (by omega : 2 ≤ m+3)
    rw [pow_succ']
    omega

/-- All parity patterns of the three arbitrary extras are now consumed.
An index-two coherent prefix suffices for same-modulus fixed validity
throughout the subbinary range, without an assumed parity classification. -/
theorem valid_fixed_of_valid_doubled_three_extra_prefix_lt_two_pow
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m)
    (g : Fin (m+3) → ZMod (2*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom 2 M (a i.val : ZMod M))
    (hupper : 2*M < 2^(m+3)) : Valid (m+3) (2*M) := by
  let π := ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
  let x : Fin (m+3) := (Fin.last m).castSucc.castSucc
  let y : Fin (m+3) := (Fin.last (m+1)).castSucc
  let z : Fin (m+3) := Fin.last (m+2)
  have hxy : x ≠ y := by intro h; have h' := congrArg Fin.val h; simp [x, y] at h'
  have hxz : x ≠ z := by intro h; have h' := congrArg Fin.val h; simp [x, z] at h'
  have hyz : y ≠ z := by intro h; have h' := congrArg Fin.val h; simp [y, z] at h'
  have hswap (j k : Fin (m+3)) (hj : m ≤ j.val) (hk : m ≤ k.val) :
      ∀ i : Fin m, g (Equiv.swap j k i.castSucc.castSucc.castSucc) =
        zmodScaleHom 2 M (a i.val : ZMod M) := by
    intro i
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact hpref i
    · intro heq; have h' := congrArg Fin.val heq; simp only [Fin.val_castSucc] at h'; omega
    · intro heq; have h' := congrArg Fin.val heq; simp only [Fin.val_castSucc] at h'; omega
  have h2 (p : Equiv.Perm (Fin (m+3)))
      (hp : ∀ i : Fin m, g (p i.castSucc.castSucc.castSucc) = zmodScaleHom 2 M (a i.val : ZMod M))
      (ha : π (g (p x)) = 0) (hb : π (g (p y)) = 0) : Valid (m+3) (2*M) :=
    valid_fixed_of_valid_doubled_three_extra_two_even_subbinary hm
      (fun i ↦ g (p i)) (validTuple_embedding p.toEmbedding g hg) hp ha hb hupper
  have h1 (p : Equiv.Perm (Fin (m+3)))
      (hp : ∀ i : Fin m, g (p i.castSucc.castSucc.castSucc) = zmodScaleHom 2 M (a i.val : ZMod M))
      (ha : π (g (p x)) = 0) (hb : π (g (p y)) = 1) (hc : π (g (p z)) = 1) : False :=
    (Nat.not_le_of_gt hupper) (binary_lower_bound_of_valid_doubled_three_extra_one_even
      (by omega) g hg p hp ha hb hc)
  have hh : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  rcases hh (π (g x)) with hx | hx
  · rcases hh (π (g y)) with hy | hy
    · exact h2 (Equiv.refl _) hpref hx hy
    · rcases hh (π (g z)) with hz | hz
      · apply h2 (Equiv.swap y z) (hswap y z (by simp [y]) (by simp [z]))
        · simpa [Equiv.swap_apply_def, hxy, hxz] using hx
        · simpa using hz
      · exact False.elim (h1 (Equiv.refl _) hpref hx hy hz)
  · rcases hh (π (g y)) with hy | hy
    · rcases hh (π (g z)) with hz | hz
      · apply h2 (Equiv.swap x z) (hswap x z (by simp [x]) (by simp [z]))
        · simpa using hz
        · simpa [Equiv.swap_apply_def, hxy.symm, hyz] using hy
      · apply False.elim
        apply h1 (Equiv.swap x y) (hswap x y (by simp [x]) (by simp [y]))
        · simpa using hy
        · simpa using hx
        · simpa [Equiv.swap_apply_def, hxz.symm, hyz.symm] using hz
    · rcases hh (π (g z)) with hz | hz
      · apply False.elim
        apply h1 (Equiv.swap x z) (hswap x z (by simp [x]) (by simp [z]))
        · simpa using hz
        · simpa [Equiv.swap_apply_def, hxy.symm, hyz] using hy
        · simpa using hx
      · have hb := first_even_lower_bound_of_valid_doubled_three_odd_extras hm
          g hg (Equiv.refl _) hpref hx hy hz
        have hpow : 2^(m+3)=2*2^(m+2) := by rw [show m+3=(m+2)+1 by omega, pow_succ']
        have hgap : 2*M=2^(m+3)-2 := by omega
        rw [hgap]
        simpa only [pow_one] using valid_gap (n := m+3) (t := 1) (by omega) (by norm_num)

/-- Unit-affine transport in the original modulus preserves the entire
index-two, three-arbitrary-extra result. No parity hypothesis remains. -/
theorem valid_fixed_of_valid_affine_doubled_three_extra_prefix_lt_two_pow
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m)
    (g : Fin (m+3) → ZMod (2*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (φ : ZMod (2*M) ≃+ ZMod (2*M)) (b : ZMod (2*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (zmodScaleHom 2 M (a i.val : ZMod M))+b)
    (hupper : 2*M < 2^(m+3)) : Valid (m+3) (2*M) := by
  apply valid_fixed_of_valid_doubled_three_extra_prefix_lt_two_pow hm
    (fun i ↦ φ.symm (g (e i)-b))
    (validTuple_comp (validTuple_sub_const _ (validTuple_embedding e.toEmbedding g hg) b)
      φ.symm.toAddMonoidHom φ.symm.injective) ?_ hupper
  intro i
  simp only [hpref, add_sub_cancel_right, AddEquiv.symm_apply_apply]

/-- Every positive even modulus with a coherent index-two n-3 prefix
satisfies the full global bound, with all three extras arbitrary. -/
theorem global_lower_bound_of_valid_affine_doubled_three_extra_prefix
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m)
    (g : Fin (m+3) → ZMod (2*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (φ : ZMod (2*M) ≃+ ZMod (2*M)) (b : ZMod (2*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (zmodScaleHom 2 M (a i.val : ZMod M))+b) :
    globalBound (m+3) ≤ 2*M := by
  by_cases hupper : 2*M < 2^(m+3)
  · have hv := valid_fixed_of_valid_affine_doubled_three_extra_prefix_lt_two_pow hm g hg e φ b hpref hupper
    exact (nmin_eq (by omega : 2 ≤ m+3)).2 ⟨by have h := Nat.pos_of_ne_zero (NeZero.ne M); omega, hv⟩
  · exact (Nat.sub_le _ _).trans (by omega)

/-- The same actual-prefix class satisfies every exact even-stratum
threshold, not just its global envelope. -/
theorem stratum_lower_bound_of_valid_affine_doubled_three_extra_prefix
    {m M s q : ℕ} [NeZero M] (hm : 5 ≤ m) (hq : Odd q) (hN : 2*M=2^s*q)
    (g : Fin (m+3) → ZMod (2*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (φ : ZMod (2*M) ≃+ ZMod (2*M)) (b : ZMod (2*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (zmodScaleHom 2 M (a i.val : ZMod M))+b) :
    stratumBound (m+3) s ≤ 2*M := by
  by_cases hupper : 2*M < 2^(m+3)
  · have hv := valid_fixed_of_valid_affine_doubled_three_extra_prefix_lt_two_pow hm g hg e φ b hpref hupper
    rw [hN] at hv
    simpa only [hN] using stratum_lower_bound_of_valid_fixed (by omega : 3 ≤ m+3) hq hv
  · exact (Nat.sub_le _ _).trans (by omega)

end MinModulus
