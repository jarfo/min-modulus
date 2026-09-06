import MinModulus.SIThreeIndexThree

/-!
# Index-four coherent prefixes with three arbitrary extras

For every n >= 8, subbinary validity with a coherent quadrupled n-3
prefix implies fixed validity at the same modulus. Global and all exact
even-stratum bounds follow, with three arbitrary extras and original-
modulus unit-affine transport. Three same-coset extras force three cyclic
gaps via actual m-coin rivals. The remaining quotient cases are actual
subgroup extraction, admissible boundary gaps, or subgroup-sum rivals.
No finite tuple census or unrestricted global gate is used.
-/

namespace MinModulus
open Finset

/-- An actual difference of outside coordinates cannot have a short
representative in the prefix subgroup: the m-coin cover would transfer
one copy and omit a coordinate. This holds for any additive target group. -/
theorem scaled_three_extra_difference_val_large
    {m M : ℕ} [NeZero M] (hm : 4 ≤ m) {G : Type*} [AddCommGroup G]
    (τ : ZMod M →+ G) (g : Fin (m+3) → G) (hg : ValidTuple g)
    (f : Fin m → Fin (m+3)) (hpref : ∀ i, g (f i) = τ (a i.val : ZMod M))
    (x y z : Fin (m+3)) (hxy : x ≠ y) (hyz : y ≠ z) (hy : ∀ i, f i ≠ y)
    (htotal : (∑ i, g i) = τ (2^m-m-1 : ℕ)+g x+g y+g z)
    (w : ZMod M) (hw : τ w = g x-g y) : 2^m-m-1 < w.val := by
  by_contra hsmall
  let S := 2^m-m-1
  let r := S-w.val
  have hr : r ≤ S := Nat.sub_le _ _
  have hp := Nat.lt_two_pow_self (n := m-1)
  have hpow : 2^m=2*2^(m-1) := by rw [← pow_succ']; congr 1; omega
  have hinterval : r < (1+2)*(2^(m-1)-1)-(m-2) := by dsimp [S] at hr; omega
  obtain ⟨s, hcard, hs⟩ := exists_fixed_multiset_sum_of_lt_initial_interval
    (N := M) (d := 1) (by omega : 2 ≤ m) hinterval
  have hrval : (r : ZMod M) = (S : ZMod M)-w := by
    dsimp [r]
    rw [Nat.cast_sub (by dsimp [S]; omega), ZMod.natCast_zmod_val]
  have hsum : τ (r : ZMod M)+2 • g x+g z = ∑ i, g i := by
    rw [hrval, map_sub, hw, htotal]
    dsimp [S]
    abel
  apply not_validTuple_of_actual_mapped_fibre_cover τ (fun i : Fin m ↦ (a i.val : ZMod M))
    g f hpref (r : ZMod M) ⟨s, hcard, hs⟩ (Multiset.replicate 2 x+{z})
    (by simp; omega) (by simpa only [Multiset.map_add, Multiset.sum_add,
      Multiset.map_replicate, Multiset.sum_replicate, Multiset.map_singleton,
      Multiset.sum_singleton, add_assoc] using hsum) y hy ?_ hg
  simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton]
  tauto

/-- Three points on a cyclic interval whose directed differences all
avoid [0,S] require room for three gaps of length S+1. -/
theorem three_cyclic_separated_points_modulus_bound
    {M : ℕ} [NeZero M] (S : ℕ) (u v : ZMod M)
    (hu : S < u.val) (hv : S < v.val)
    (hnu : S < (-u).val) (hnv : S < (-v).val)
    (huv : S < (u-v).val) (hvu : S < (v-u).val) : 3*(S+1) ≤ M := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  rw [ZMod.neg_val, if_neg hu0] at hnu
  rw [ZMod.neg_val, if_neg hv0] at hnv
  rcases le_total u.val v.val with h | h
  · rw [ZMod.val_sub h] at hvu
    omega
  · rw [ZMod.val_sub h] at huv
    omega

/-- Three extras in one quotient coset force three separated actual
subgroup points, giving a uniform modulus bound at every subgroup index. -/
theorem modulus_bound_of_scaled_three_extras_same_coset
    {m d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 4 ≤ m)
    (g : Fin (m+3) → ZMod (d*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M))
    (hxy : ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.last m).castSucc.castSucc) =
      ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.last (m+1)).castSucc))
    (hyz : ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.last (m+1)).castSucc) =
      ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.last (m+2)))) :
    3*((2^m-m-1)+1) ≤ M := by
  let τ := zmodScaleHom d M
  let π := ZMod.castHom (dvd_mul_right d M) (ZMod d)
  let x : Fin (m+3) := (Fin.last m).castSucc.castSucc
  let y : Fin (m+3) := (Fin.last (m+1)).castSucc
  let z : Fin (m+3) := Fin.last (m+2)
  let f : Fin m → Fin (m+3) := fun i ↦ i.castSucc.castSucc.castSucc
  have hxy' : x ≠ y := by intro h; have h' := congrArg Fin.val h; simp [x, y] at h'
  have hxz' : x ≠ z := by intro h; have h' := congrArg Fin.val h; simp [x, z] at h'
  have hyz' : y ≠ z := by intro h; have h' := congrArg Fin.val h; simp [y, z] at h'
  have hfx (i : Fin m) : f i ≠ x := by
    intro h; have h' := congrArg Fin.val h; simp only [f, x, Fin.val_castSucc, Fin.val_last] at h'; omega
  have hfy (i : Fin m) : f i ≠ y := by
    intro h; have h' := congrArg Fin.val h; simp only [f, y, Fin.val_castSucc, Fin.val_last] at h'; omega
  have hfz (i : Fin m) : f i ≠ z := by
    intro h; have h' := congrArg Fin.val h; simp only [f, z, Fin.val_castSucc, Fin.val_last] at h'; omega
  have htotal : (∑ i, g i) = τ (2^m-m-1 : ℕ)+g x+g y+g z := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [hpref, ← map_sum, ← Nat.cast_sum, sum_fixed_eq_cover_hole, τ, x, y, z]
  have huy : π (g y-g x)=0 := by rw [map_sub, show π (g x)=π (g y) from hxy, sub_self]
  have hvz : π (g z-g x)=0 := by
    rw [map_sub, show π (g x)=π (g y) from hxy, show π (g y)=π (g z) from hyz, sub_self]
  obtain ⟨u, hu⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ huy
  obtain ⟨v, hv⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hvz
  have hU := scaled_three_extra_difference_val_large hm τ g hg f hpref y x z
    hxy'.symm hxz' hfx (by rw [htotal]; abel) u hu
  have hV := scaled_three_extra_difference_val_large hm τ g hg f hpref z x y
    hxz'.symm hxy' hfx (by rw [htotal]; abel) v hv
  have hNU := scaled_three_extra_difference_val_large hm τ g hg f hpref x y z
    hxy' hyz' hfy htotal (-u) (by rw [map_neg, hu]; abel)
  have hNV := scaled_three_extra_difference_val_large hm τ g hg f hpref x z y
    hxz' hyz'.symm hfz (by rw [htotal]; abel) (-v) (by rw [map_neg, hv]; abel)
  have hUV := scaled_three_extra_difference_val_large hm τ g hg f hpref y z x
    hyz' hxz'.symm hfz (by rw [htotal]; abel) (u-v) (by rw [map_sub, hu, hv]; abel)
  have hVU := scaled_three_extra_difference_val_large hm τ g hg f hpref z y x
    hyz'.symm hxy'.symm hfy (by rw [htotal]; abel) (v-u) (by rw [map_sub, hu, hv]; abel)
  exact three_cyclic_separated_points_modulus_bound _ u v hU hV hNU hNV hUV hVU

/-- A subgroup extra extends the actual coherent prefix whenever its
one-extra child lies below its last two binary residues. This works for
every subgroup index and gives fixed validity at the original modulus. -/
theorem valid_fixed_of_scaled_three_extra_subgroup_extra_small_child
    {m d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 2 ≤ m)
    (hM : M ≤ 2^(m+1)-3) (hupper : d*M < 2^(m+3))
    (g : Fin (m+3) → ZMod (d*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.last m).castSucc.castSucc) = 0) :
    Valid (m+3) (d*M) := by
  obtain ⟨t, ht⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hx
  let u : Fin (m+1) → ZMod M := Fin.lastCases t (fun i : Fin m ↦ (a i.val : ZMod M))
  have hu : ValidTuple u := validTuple_fixed_extra_of_valid_scaled_short_prefix
    (fun i : Fin (m+2) ↦ g i.castSucc)
    (validTuple_embedding ⟨Fin.castSucc, Fin.castSucc_injective (m+2)⟩ g hg)
    hpref (Fin.last m).castSucc (by simp) t ht.symm
  have hfull := eq_fixed_of_valid_fixed_prefix_of_modulus_le hm hM u hu (by intro i; simp [u])
  have ht' : t = (a m : ZMod M) := by
    simpa only [u, Fin.lastCases_last, Fin.val_last] using congrFun hfull (Fin.last m)
  have hnext : g (Fin.last m).castSucc.castSucc = zmodScaleHom d M (a m : ZMod M) := by
    rw [← ht, ht']
  have hlong (i : Fin (m+1)) : g i.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M) :=
    Fin.lastCases hnext (fun j ↦ hpref j) i
  apply valid_fixed_of_valid_scaled_fixed_short_prefix_lt_two_pow (by omega : 3 ≤ m+1)
    g hg (Equiv.refl _) (d : ZMod (d*M)) 0 ?_ hupper
  intro i
  simp only [Equiv.refl_apply, hlong, zmodScaleHom_natCast, Nat.cast_mul, add_zero]

/-- At index four, the two child residues not handled by extraction
already double twice to admissible gaps. Thus any subgroup extra supplies
same-modulus fixed validity throughout the subbinary range. -/
theorem valid_fixed_of_quadrupled_three_extra_subgroup_extra_subbinary
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m) (hupper : 4*M < 2^(m+3))
    (g : Fin (m+3) → ZMod (4*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom 4 M (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_right 4 M) (ZMod 4) (g (Fin.last m).castSucc.castSucc) = 0) :
    Valid (m+3) (4*M) := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (4*M) := ⟨by omega⟩
  by_cases hM : M ≤ 2^(m+1)-3
  · exact valid_fixed_of_scaled_three_extra_subgroup_extra_small_child (by omega) hM hupper g hg hpref hx
  have hpow : 2^(m+3) = 4*2^(m+1) := by
    rw [show m+3=(m+1)+2 by omega, pow_add]; norm_num; ring
  by_cases hgap : M = 2^(m+1)-1
  · have hN : 4*M = 2^(m+3)-4 := by omega
    rw [hN]
    simpa only [show 2^2=(4:ℕ) by norm_num] using
      valid_gap (n := m+3) (t := 2) (by omega) (by norm_num; omega)
  · have hN : 4*M = 2^(m+3)-8 := by omega
    rw [hN]
    simpa only [show 2^3=(8:ℕ) by norm_num] using
      valid_gap (n := m+3) (t := 3) (by omega) (by norm_num; omega)

/-- Quotient arithmetic modulo four reduces every triple to a subgroup
entry, a subgroup-valued sum, or three entries in the same coset. -/
theorem zmod_four_three_extra_cases (x y z : ZMod 4) :
    x=0 ∨ y=0 ∨ z=0 ∨ x+y+z=0 ∨ x+y=0 ∨ x+z=0 ∨ y+z=0 ∨ (x=y ∧ y=z) := by
  revert x y z
  decide

/-- All index-four quotient triples are consumed uniformly for n>=8. -/
theorem valid_fixed_of_valid_quadrupled_three_extra_prefix_lt_two_pow
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m) (hupper : 4*M < 2^(m+3))
    (g : Fin (m+3) → ZMod (4*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom 4 M (a i.val : ZMod M)) :
    Valid (m+3) (4*M) := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (4*M) := ⟨by omega⟩
  have hgrowth := three_mul_le_mersenne_pred hm
  have hpow : 2^m=2*2^(m-1) := by rw [← pow_succ']; congr 1; omega
  have hpow3 : 2^(m+3)=16*2^(m-1) := by rw [pow_add, hpow]; norm_num; ring
  have hMpair : M ≤ 5*(2^(m-1)-1)-(m-2) := by omega
  have hMtotal : M ≤ (4+2)*(2^(m-1)-1)-(m-2) := by omega
  have hMcircle : M < 3*((2^m-m-1)+1) := by omega
  let π := ZMod.castHom (dvd_mul_right 4 M) (ZMod 4)
  let x : Fin (m+3) := (Fin.last m).castSucc.castSucc
  let y : Fin (m+3) := (Fin.last (m+1)).castSucc
  let z : Fin (m+3) := Fin.last (m+2)
  have hxy : x ≠ y := by intro h; have h' := congrArg Fin.val h; simp [x, y] at h'
  have hxz : x ≠ z := by intro h; have h' := congrArg Fin.val h; simp [x, z] at h'
  have hyz : y ≠ z := by intro h; have h' := congrArg Fin.val h; simp [y, z] at h'
  have hswap (j k : Fin (m+3)) (hj : m ≤ j.val) (hk : m ≤ k.val) :
      ∀ i : Fin m, g (Equiv.swap j k i.castSucc.castSucc.castSucc) =
        zmodScaleHom 4 M (a i.val : ZMod M) := by
    intro i
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact hpref i
    · intro heq; have h' := congrArg Fin.val heq; simp only [Fin.val_castSucc] at h'; omega
    · intro heq; have h' := congrArg Fin.val heq; simp only [Fin.val_castSucc] at h'; omega
  have hzero (p : Equiv.Perm (Fin (m+3)))
      (hp : ∀ i : Fin m, g (p i.castSucc.castSucc.castSucc) = zmodScaleHom 4 M (a i.val : ZMod M))
      (ha : π (g (p x)) = 0) : Valid (m+3) (4*M) :=
    valid_fixed_of_quadrupled_three_extra_subgroup_extra_subbinary hm hupper
      (fun i ↦ g (p i)) (validTuple_embedding p.toEmbedding g hg) hp ha
  have hpair (p : Equiv.Perm (Fin (m+3)))
      (hp : ∀ i : Fin m, g (p i.castSucc.castSucc.castSucc) = zmodScaleHom 4 M (a i.val : ZMod M))
      (ha : π (g (p x))+π (g (p y))=0) : False :=
    not_validTuple_of_scaled_short_prefix_extra_sum_zero (by omega) hMpair
      (fun i : Fin (m+2) ↦ g (p i.castSucc)) hp (by simpa only [map_add] using ha)
      (validTuple_embedding ⟨Fin.castSucc, Fin.castSucc_injective (m+2)⟩
        (fun i ↦ g (p i)) (validTuple_embedding p.toEmbedding g hg))
  rcases zmod_four_three_extra_cases (π (g x)) (π (g y)) (π (g z)) with
    h | h | h | h | h | h | h | h
  · exact hzero (Equiv.refl _) hpref h
  · apply hzero (Equiv.swap x y) (hswap x y (by simp [x]) (by simp [y]))
    simpa using h
  · apply hzero (Equiv.swap x z) (hswap x z (by simp [x]) (by simp [z]))
    simpa using h
  · have htotal : π (∑ i, g i)=0 := by
      rw [map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      have hπprefix (i : Fin m) : π (g i.castSucc.castSucc.castSucc)=0 := by
        rw [hpref, zmodScaleHom_natCast, map_natCast π, Nat.cast_mul, ZMod.natCast_self, zero_mul]
      simpa only [hπprefix, Finset.sum_const_zero, zero_add, x, y, z] using h
    exact False.elim (not_validTuple_of_scaled_three_extra_total_in_subgroup (by omega) hMtotal g hpref htotal hg)
  · exact False.elim (hpair (Equiv.refl _) hpref h)
  · apply False.elim
    apply hpair (Equiv.swap y z) (hswap y z (by simp [y]) (by simp [z]))
    simpa [Equiv.swap_apply_def, hxy, hxz] using h
  · apply False.elim
    apply hpair (Equiv.swap x z) (hswap x z (by simp [x]) (by simp [z]))
    simpa [Equiv.swap_apply_def, hxy.symm, hyz, add_comm] using h
  · have hb := modulus_bound_of_scaled_three_extras_same_coset (by omega) g hg hpref h.1 h.2
    omega

/-- Original-modulus unit-affine transport preserves the complete
index-four three-extra result. -/
theorem valid_fixed_of_valid_affine_quadrupled_three_extra_prefix_lt_two_pow
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m)
    (g : Fin (m+3) → ZMod (4*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (φ : ZMod (4*M) ≃+ ZMod (4*M)) (b : ZMod (4*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (zmodScaleHom 4 M (a i.val : ZMod M))+b)
    (hupper : 4*M < 2^(m+3)) : Valid (m+3) (4*M) := by
  apply valid_fixed_of_valid_quadrupled_three_extra_prefix_lt_two_pow hm hupper
    (fun i ↦ φ.symm (g (e i)-b))
    (validTuple_comp (validTuple_sub_const _ (validTuple_embedding e.toEmbedding g hg) b)
      φ.symm.toAddMonoidHom φ.symm.injective)
  intro i
  simp only [hpref, add_sub_cancel_right, AddEquiv.symm_apply_apply]

/-- Every coherent index-four n-3 prefix satisfies the full global
bound, n>=8, with all three extras arbitrary. -/
theorem global_lower_bound_of_valid_affine_quadrupled_three_extra_prefix
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m)
    (g : Fin (m+3) → ZMod (4*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (φ : ZMod (4*M) ≃+ ZMod (4*M)) (b : ZMod (4*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (zmodScaleHom 4 M (a i.val : ZMod M))+b) :
    globalBound (m+3) ≤ 4*M := by
  by_cases hupper : 4*M < 2^(m+3)
  · have hv := valid_fixed_of_valid_affine_quadrupled_three_extra_prefix_lt_two_pow hm g hg e φ b hpref hupper
    exact (nmin_eq (by omega : 2 ≤ m+3)).2 ⟨by have h := Nat.pos_of_ne_zero (NeZero.ne M); omega, hv⟩
  · exact (Nat.sub_le _ _).trans (by omega)

/-- The entire index-four class also satisfies every exact even-stratum
threshold, not merely the global envelope. -/
theorem stratum_lower_bound_of_valid_affine_quadrupled_three_extra_prefix
    {m M s q : ℕ} [NeZero M] (hm : 5 ≤ m) (hq : Odd q) (hN : 4*M=2^s*q)
    (g : Fin (m+3) → ZMod (4*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (φ : ZMod (4*M) ≃+ ZMod (4*M)) (b : ZMod (4*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (zmodScaleHom 4 M (a i.val : ZMod M))+b) :
    stratumBound (m+3) s ≤ 4*M := by
  by_cases hupper : 4*M < 2^(m+3)
  · have hv := valid_fixed_of_valid_affine_quadrupled_three_extra_prefix_lt_two_pow hm g hg e φ b hpref hupper
    rw [hN] at hv
    simpa only [hN] using stratum_lower_bound_of_valid_fixed (by omega : 3 ≤ m+3) hq hv
  · exact (Nat.sub_le _ _).trans (by omega)

end MinModulus
