import MinModulus.SIThreeIndexFour

/-!
# Index-five coherent prefixes with three arbitrary extras

The binary bound holds for every n >= 8 and positive modulus 5*M,
including odd moduli, with arbitrary extras and original-modulus unit-
affine transport. A subgroup extra gives an actual one-extra child and
its proved lower bound. Opposite quotient residues give a prefix-only
rival. Equal quotient residues are excluded using the m-coin prefix cover
in both directions, even when it does not cover the whole subgroup.
Elementary quotient arithmetic exhausts the patterns; no finite tuple
census or unrestricted G1/G2/G3 premise is used.
-/

namespace MinModulus
open Finset

/-- Two residues whose sum is twice S cannot both lie strictly above S
when the modulus is at most 2*S+1. -/
theorem not_both_val_gt_of_add_eq_twice
    {M S : ℕ} [NeZero M] (hM : M ≤ 2 * S + 1)
    (x y : ZMod M) (hsum : x + y = (2 * S : ℕ))
    (hx : S < x.val) (hy : S < y.val) : False := by
  have hxlt := x.val_lt
  have hylt := y.val_lt
  let D := x.val + y.val - 2 * S
  have hDpos : 0 < D := by dsimp [D]; omega
  have hDlt : D < M := by dsimp [D]; omega
  have hDzero : (D : ZMod M) = 0 := by
    dsimp [D]
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, hsum, sub_self]
  have hdvd := (ZMod.natCast_eq_zero_iff D M).mp hDzero
  exact (not_le_of_gt hDlt) (Nat.le_of_dvd hDpos hdvd)

/-- Using the m-coin cover in both directions excludes same-coset extras
up to twice the prefix sum plus one, beyond the full-cover range. -/
theorem not_validTuple_of_scaled_short_prefix_same_coset_two_sided
    {m d M : ℕ} [NeZero M] [NeZero (d * M)] (hm : 2 ≤ m)
    (hM : M ≤ 2 * (2 ^ m - m - 1) + 1)
    (g : Fin (m + 2) → ZMod (d * M))
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M))
    (hdiff : ZMod.castHom (dvd_mul_right d M) (ZMod d)
      (g (Fin.last m).castSucc - g (Fin.last (m + 1))) = 0) : ¬ ValidTuple g := by
  intro hg
  let τ := zmodScaleHom d M
  let S := 2 ^ m - m - 1
  let C := 3 * (2 ^ (m - 1) - 1) - (m - 2)
  let x : Fin (m + 2) := (Fin.last m).castSucc
  let y : Fin (m + 2) := Fin.last (m + 1)
  let f : Fin m ↪ Fin (m + 2) := ⟨fun i ↦ i.castSucc.castSucc,
    (Fin.castSucc_injective (m + 1)).comp (Fin.castSucc_injective m)⟩
  have hxy : x ≠ y := Fin.castSucc_ne_last _
  have hx : ∀ i, f i ≠ x := by
    intro i hi
    exact Fin.castSucc_ne_last i (Fin.castSucc_injective (m + 1) hi)
  obtain ⟨w, hw⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hdiff
  let u : ZMod M := S + w
  let v : ZMod M := S - w
  have hlarge (z : ZMod M) (A B : ℕ) (hA : A ≠ 1) (hAB : A + B = 2)
      (hsum : τ z + A • g x + B • g y = ∑ i, g i) : C ≤ z.val := by
    by_contra hsmall
    obtain ⟨s, hcard, hs⟩ := exists_fixed_multiset_sum_of_lt_initial_interval
      (N := M) (d := 1) hm (by dsimp [C] at hsmall; omega : z.val < _)
    apply not_validTuple_of_mapped_fixed_block_two_extra_rival τ g f hprefix x y hxy hx
      hA (by omega) z ⟨s, hcard, by simpa only [ZMod.natCast_zmod_val] using hs⟩ hsum hg
  have hu : C ≤ u.val := hlarge u 0 2 (by omega) (by omega) (by
    dsimp [τ, u]
    rw [map_add, hw, sum_divisor_fixed_short_prefix g hprefix]
    dsimp [S, x, y]
    simp only [nsmul_eq_mul]
    ring)
  have hv : C ≤ v.val := hlarge v 2 0 (by omega) (by omega) (by
    dsimp [τ, v]
    rw [map_sub, hw, sum_divisor_fixed_short_prefix g hprefix]
    dsimp [S, x, y]
    simp only [nsmul_eq_mul]
    ring)
  have hSC : S < C := by
    have hp := Nat.lt_two_pow_self (n := m - 1)
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    dsimp [S, C]
    omega
  exact not_both_val_gt_of_add_eq_twice hM u v
    (by dsimp [u, v]; push_cast; ring) (by omega) (by omega)

/-- A subgroup extra produces an actual one-extra child, so its proved
global lower bound excludes any smaller subgroup modulus. -/
theorem not_validTuple_of_scaled_three_extra_subgroup_extra_small_modulus
    {m d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 2 ≤ m)
    (hM : M < globalBound (m+1))
    (g : Fin (m+3) → ZMod (d*M))
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.last m).castSucc.castSucc) = 0) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨t, ht⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hx
  let u : Fin (m+1) → ZMod M := Fin.lastCases t (fun i : Fin m ↦ (a i.val : ZMod M))
  have hu : ValidTuple u := validTuple_fixed_extra_of_valid_scaled_short_prefix
    (fun i : Fin (m+2) ↦ g i.castSucc)
    (validTuple_embedding ⟨Fin.castSucc, Fin.castSucc_injective (m+2)⟩ g hg)
    hpref (Fin.last m).castSucc (by simp) t ht.symm
  have hb := global_lower_bound_of_valid_scaled_fixed_prefix hm u hu (Equiv.refl _) 1 0
    (by intro i; simp [u])
  omega

/-- Three nonzero residues modulo five either repeat a residue or contain
an opposite pair. These are elementary quotient cases, not tuple censuses. -/
theorem zmod_five_three_extra_cases (x y z : ZMod 5) :
    x=0 ∨ y=0 ∨ z=0 ∨ x+y=0 ∨ x+z=0 ∨ y+z=0 ∨ x=y ∨ x=z ∨ y=z := by
  revert x y z
  decide

/-- Every index-five quotient pattern contradicts subbinary validity,
uniformly for n>=8 and all positive original moduli, including odd ones. -/
theorem not_validTuple_of_quintupled_three_extra_prefix_subbinary
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m) (hupper : 5*M < 2^(m+3))
    (g : Fin (m+3) → ZMod (5*M))
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom 5 M (a i.val : ZMod M)) :
    ¬ ValidTuple g := by
  intro hg
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (5*M) := ⟨by omega⟩
  have hgrowth := three_mul_le_mersenne_pred hm
  have hpow : 2^m=2*2^(m-1) := by rw [← pow_succ']; congr 1; omega
  have hpow1 : 2^(m+1)=4*2^(m-1) := by rw [pow_succ', hpow]; ring
  have hpow3 : 2^(m+3)=16*2^(m-1) := by rw [pow_add, hpow]; norm_num; ring
  have hMchild : M < globalBound (m+1) := by
    have hlog := Nat.pow_log_le_self 2 (by omega : m+1≠0)
    unfold globalBound
    omega
  have hMpair : M ≤ 5*(2^(m-1)-1)-(m-2) := by omega
  have hMdup : M ≤ 2*(2^m-m-1)+1 := by omega
  let π := ZMod.castHom (dvd_mul_right 5 M) (ZMod 5)
  let x : Fin (m+3) := (Fin.last m).castSucc.castSucc
  let y : Fin (m+3) := (Fin.last (m+1)).castSucc
  let z : Fin (m+3) := Fin.last (m+2)
  have hxy : x ≠ y := by intro h; have h' := congrArg Fin.val h; simp [x, y] at h'
  have hxz : x ≠ z := by intro h; have h' := congrArg Fin.val h; simp [x, z] at h'
  have hyz : y ≠ z := by intro h; have h' := congrArg Fin.val h; simp [y, z] at h'
  have hswap (j k : Fin (m+3)) (hj : m ≤ j.val) (hk : m ≤ k.val) :
      ∀ i : Fin m, g (Equiv.swap j k i.castSucc.castSucc.castSucc) =
        zmodScaleHom 5 M (a i.val : ZMod M) := by
    intro i
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact hpref i
    · intro heq; have h' := congrArg Fin.val heq; simp only [Fin.val_castSucc] at h'; omega
    · intro heq; have h' := congrArg Fin.val heq; simp only [Fin.val_castSucc] at h'; omega
  have hzero (p : Equiv.Perm (Fin (m+3)))
      (hp : ∀ i : Fin m, g (p i.castSucc.castSucc.castSucc) = zmodScaleHom 5 M (a i.val : ZMod M))
      (ha : π (g (p x)) = 0) : False :=
    not_validTuple_of_scaled_three_extra_subgroup_extra_small_modulus (by omega) hMchild
      (fun i ↦ g (p i)) hp ha (validTuple_embedding p.toEmbedding g hg)
  have hpair (p : Equiv.Perm (Fin (m+3)))
      (hp : ∀ i : Fin m, g (p i.castSucc.castSucc.castSucc) = zmodScaleHom 5 M (a i.val : ZMod M))
      (ha : π (g (p x))+π (g (p y))=0) : False :=
    not_validTuple_of_scaled_short_prefix_extra_sum_zero (by omega) hMpair
      (fun i : Fin (m+2) ↦ g (p i.castSucc)) hp (by simpa only [map_add] using ha)
      (validTuple_embedding ⟨Fin.castSucc, Fin.castSucc_injective (m+2)⟩
        (fun i ↦ g (p i)) (validTuple_embedding p.toEmbedding g hg))
  have hdup (p : Equiv.Perm (Fin (m+3)))
      (hp : ∀ i : Fin m, g (p i.castSucc.castSucc.castSucc) = zmodScaleHom 5 M (a i.val : ZMod M))
      (ha : π (g (p x))=π (g (p y))) : False :=
    not_validTuple_of_scaled_short_prefix_same_coset_two_sided (by omega) hMdup
      (fun i : Fin (m+2) ↦ g (p i.castSucc)) hp (by rw [map_sub]; exact sub_eq_zero.mpr ha)
      (validTuple_embedding ⟨Fin.castSucc, Fin.castSucc_injective (m+2)⟩
        (fun i ↦ g (p i)) (validTuple_embedding p.toEmbedding g hg))
  rcases zmod_five_three_extra_cases (π (g x)) (π (g y)) (π (g z)) with
    h | h | h | h | h | h | h | h | h
  · exact hzero (Equiv.refl _) hpref h
  · apply hzero (Equiv.swap x y) (hswap x y (by simp [x]) (by simp [y]))
    simpa using h
  · apply hzero (Equiv.swap x z) (hswap x z (by simp [x]) (by simp [z]))
    simpa using h
  · exact hpair (Equiv.refl _) hpref h
  · apply hpair (Equiv.swap y z) (hswap y z (by simp [y]) (by simp [z]))
    simpa [Equiv.swap_apply_def, hxy, hxz] using h
  · apply hpair (Equiv.swap x z) (hswap x z (by simp [x]) (by simp [z]))
    simpa [Equiv.swap_apply_def, hxy.symm, hyz, add_comm] using h
  · exact hdup (Equiv.refl _) hpref h
  · apply hdup (Equiv.swap y z) (hswap y z (by simp [y]) (by simp [z]))
    simpa [Equiv.swap_apply_def, hxy, hxz] using h
  · apply hdup (Equiv.swap x z) (hswap x z (by simp [x]) (by simp [z]))
    simpa [Equiv.swap_apply_def, hxy.symm, hyz] using h.symm

/-- All coherent index-five n-3 prefixes, with arbitrary extras and
original-modulus unit-affine transport, satisfy the binary bound. -/
theorem binary_lower_bound_of_valid_affine_quintupled_three_extra_prefix
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m)
    (g : Fin (m+3) → ZMod (5*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (φ : ZMod (5*M) ≃+ ZMod (5*M)) (b : ZMod (5*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (zmodScaleHom 5 M (a i.val : ZMod M))+b) :
    2^(m+3) ≤ 5*M := by
  by_contra h
  apply not_validTuple_of_quintupled_three_extra_prefix_subbinary hm (by omega)
    (fun i ↦ φ.symm (g (e i)-b))
    (by intro i; simp only [hpref, add_sub_cancel_right, AddEquiv.symm_apply_apply])
  exact validTuple_comp (validTuple_sub_const _ (validTuple_embedding e.toEmbedding g hg) b)
    φ.symm.toAddMonoidHom φ.symm.injective

/-- The index-five binary theorem implies global and all exact-stratum
thresholds, including odd moduli, without an unrestricted conjecture. -/
theorem global_and_stratum_lower_bound_of_valid_affine_quintupled_three_extra_prefix
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m)
    (g : Fin (m+3) → ZMod (5*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (φ : ZMod (5*M) ≃+ ZMod (5*M)) (b : ZMod (5*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (zmodScaleHom 5 M (a i.val : ZMod M))+b) :
    globalBound (m+3) ≤ 5*M ∧ ∀ s : ℕ, stratumBound (m+3) s ≤ 5*M := by
  have h := binary_lower_bound_of_valid_affine_quintupled_three_extra_prefix hm g hg e φ b hpref
  exact ⟨(Nat.sub_le _ _).trans h, fun s ↦ (Nat.sub_le _ _).trans h⟩

end MinModulus
