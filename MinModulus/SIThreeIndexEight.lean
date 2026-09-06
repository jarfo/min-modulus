import MinModulus.ActualFibreQuotientCube

/-!
# Index-eight coherent prefixes with three arbitrary extras

For every n >= 8, a coherent octupled n-3 prefix satisfies the global
and all exact even-stratum bounds, with arbitrary extras and original-
modulus affine transport. Subbinary validity forces fixed validity at
the same modulus. Actual-fibre covers rule out tripled quotient rivals;
elementary ZMod 8 arithmetic orders the outside dyadic chain. One-hole
covers force its actual affine relations, and a parity-saving cover fixes
the last projection. Full affine doubling closure supplies the bound.
No external tuple census or unrestricted global gate is assumed.
-/

namespace MinModulus
open Finset

/-- A one-hole prefix cover turns a quotient doubling relation into an
actual affine doubling relation, at any cyclic subgroup index. -/
theorem extra_eq_affine_double_of_valid_scaled_short_prefix
    {m d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 3 ≤ m) (hM : M ≤ 2^m-2)
    (g : Fin (m+2) → ZMod (d*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M))
    (hquot : ZMod.castHom (dvd_mul_right d M) (ZMod d)
      (g (Fin.last m).castSucc-2*g (Fin.last (m+1)))=0) :
    g (Fin.last m).castSucc=2*g (Fin.last (m+1))+(d : ℕ) := by
  let τ := zmodScaleHom d M
  let x := g (Fin.last m).castSucc
  let y := g (Fin.last (m+1))
  obtain ⟨w, hw⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hquot
  let σ : ZMod M := ((2^m-m-1 : ℕ) : ZMod M)
  let z := σ+w
  have hz : z.val=2^m-m := by
    by_contra hne
    have hcover := exists_fixed_multiset_sum_card_pred_except_hole (by omega) hM z hne
    let f : Fin m ↪ Fin (m+2) := ⟨fun i ↦ i.castSucc.castSucc,
      (Fin.castSucc_injective (m+1)).comp (Fin.castSucc_injective m)⟩
    apply not_validTuple_of_mapped_fixed_block_two_extra_rival τ g f hpref
      (Fin.last m).castSucc (Fin.last (m+1)) (Fin.castSucc_ne_last _)
      (by intro i hi; exact Fin.castSucc_ne_last i (Fin.castSucc_injective (m+1) hi))
      (by omega : 0 ≠ 1) (by omega : m-1+0+3=m+2) z hcover ?_ hg
    dsimp only [τ, z]
    rw [map_add, hw, sum_divisor_fixed_short_prefix g hpref]
    dsimp [σ, x, y]
    simp only [nsmul_eq_mul]
    ring
  have hp := Nat.lt_two_pow_self (n := m)
  have hσ : σ+1=((2^m-m : ℕ) : ZMod M) := by
    have hn : 2^m-m-1+1=2^m-m := by omega
    simpa only [Nat.cast_add, Nat.cast_one, σ] using congrArg (fun k : ℕ ↦ (k : ZMod M)) hn
  have hwone : w=1 := by
    have hzc : z=((2^m-m : ℕ) : ZMod M) := by rw [← hz, ZMod.natCast_zmod_val]
    rw [← hσ] at hzc
    exact add_left_cancel hzc
  rw [hwone] at hw
  have hτone : zmodScaleHom d M 1=(d : ℕ) := by simpa using zmodScaleHom_natCast d M 1
  rw [hτone] at hw
  change x=2*y+(d : ℕ)
  linear_combination -hw

/-- A mapped actual prefix cover and a nonstandard outside multiplicity
contradict validity. The subgroup map and all three outside values are arbitrary. -/
theorem not_validTuple_of_mapped_three_extra_block_rival
    {m n M N A B C K : ℕ} (τ : ZMod M →+ ZMod N)
    (g : Fin n → ZMod N) (f : Fin m → Fin n)
    (hpref : ∀ i, g (f i)=τ (a i.val : ZMod M))
    (x y z : Fin n) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : ∀ i, f i ≠ x) (hy : ∀ i, f i ≠ y) (hz : ∀ i, f i ≠ z)
    (hcounts : A ≠ 1 ∨ B ≠ 1 ∨ C ≠ 1) (hcard : K+A+B+C=n)
    (r : ZMod M) (hcover : ∃ s : Multiset (Fin m), s.card=K ∧
      (s.map (fun i ↦ (a i.val : ZMod M))).sum=r)
    (hsum : τ r+A • g x+B • g y+C • g z=∑ i, g i) : ¬ ValidTuple g := by
  classical
  intro hg
  obtain ⟨s, hs, hsr⟩ := hcover
  let t := s.map f+Multiset.replicate A x+Multiset.replicate B y+Multiset.replicate C z
  have htcard : t.card=n := by
    simpa only [t, Multiset.card_add, Multiset.card_map, Multiset.card_replicate, hs] using hcard
  have hmap : ((s.map f).map g).sum=τ r := by
    rw [Multiset.map_map]
    change (s.map (fun i ↦ g (f i))).sum=τ r
    simp only [hpref]
    simpa only [map_multiset_sum, Multiset.map_map, Function.comp_def] using congrArg τ hsr
  have htsum : (t.map g).sum=∑ i, g i := by
    simpa only [t, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, hmap] using hsum
  have hnot (j : Fin n) (hj : ∀ i, f i ≠ j) : j ∉ s.map f := by
    intro hmem
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
    exact hj i hi
  rcases hcounts with hA | hB | hC
  · have h := multiset_count_eq_one_of_validTuple g hg t htcard htsum x
    apply hA
    simpa [t, Multiset.count_replicate, Multiset.count_eq_zero.mpr (hnot x hx), hxy, hxz, Ne.symm hxy, Ne.symm hxz] using h
  · have h := multiset_count_eq_one_of_validTuple g hg t htcard htsum y
    apply hB
    simpa [t, Multiset.count_replicate, Multiset.count_eq_zero.mpr (hnot y hy), hxy, hyz, Ne.symm hxy, Ne.symm hyz] using h
  · have h := multiset_count_eq_one_of_validTuple g hg t htcard htsum z
    apply hC
    simpa [t, Multiset.count_replicate, Multiset.count_eq_zero.mpr (hnot z hz), hxz, hyz, Ne.symm hxz, Ne.symm hyz] using h

/-- At index eight, the parity-saving cover fixes the first outside
entry's subgroup projection once the actual doubling chain is known. -/
theorem odd_extra_projection_eq_neg_seven_of_valid_octupled_three_extra_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hMeven : Even M) (hM : M ≤ 2^m-2)
    (g : Fin (m+3) → ZMod (8*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc=zmodScaleHom 8 M (a i.val : ZMod M))
    (hxodd : Odd (g (Fin.last m).castSucc.castSucc).val)
    (hdouble : g (Fin.last (m+1)).castSucc=2*g (Fin.last m).castSucc.castSucc+8)
    (hdouble2 : g (Fin.last (m+2))=2*g (Fin.last (m+1)).castSucc+8) :
    ZMod.castHom (dvd_mul_left M 8) (ZMod M) (g (Fin.last m).castSucc.castSucc)=-7 := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (8*M) := ⟨by omega⟩
  let τ := zmodScaleHom 8 M
  let π := ZMod.castHom (dvd_mul_left M 8) (ZMod M)
  let x : Fin (m+3) := (Fin.last m).castSucc.castSucc
  let y : Fin (m+3) := (Fin.last (m+1)).castSucc
  let z : Fin (m+3) := Fin.last (m+2)
  let σ : ZMod M := ((2^m-m-1 : ℕ) : ZMod M)
  let r := σ-π (g x)-6
  have hp := Nat.lt_two_pow_self (n := m)
  have hpow : 2^m=2*2^(m-1) := by rw [← pow_succ']; congr 1; omega
  have hrpar : r.val%2=m%2 := by
    have heq : ((r.val+(g x).val+6 : ℕ) : ZMod M)=((2^m-m-1 : ℕ) : ZMod M) := by
      rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val]
      have hxcast : ((g x).val : ZMod M)=π (g x) := by
        simpa only [map_natCast] using congrArg π (ZMod.natCast_zmod_val (g x))
      rw [hxcast]
      dsimp [r, σ]
      abel
    have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp heq
    have hmodtwo := hmod.of_dvd hMeven.two_dvd
    change (r.val+(g x).val+6)%2=(2^m-m-1)%2 at hmodtwo
    have hxpar : (g x).val%2=1 := by obtain ⟨q, hq⟩ := hxodd; dsimp [x]; omega
    omega
  have hr : r.val=2^m-m := by
    by_contra hne
    have hcover := exists_fixed_multiset_sum_of_parity_except_hole (by omega) hM r hne hrpar
    let f : Fin m → Fin (m+3) := fun i ↦ i.castSucc.castSucc.castSucc
    have hxy : x ≠ y := by intro h; have h' := congrArg Fin.val h; simp [x, y] at h'
    have hxz : x ≠ z := by intro h; have h' := congrArg Fin.val h; simp [x, z] at h'
    have hyz : y ≠ z := by intro h; have h' := congrArg Fin.val h; simp [y, z] at h'
    have hfx (i : Fin m) : f i ≠ x := by
      intro h; have h' := congrArg Fin.val h; simp only [f, x, Fin.val_castSucc, Fin.val_last] at h'; omega
    have hfy (i : Fin m) : f i ≠ y := by
      intro h; have h' := congrArg Fin.val h; simp only [f, y, Fin.val_castSucc, Fin.val_last] at h'; omega
    have hfz (i : Fin m) : f i ≠ z := by
      intro h; have h' := congrArg Fin.val h; simp only [f, z, Fin.val_castSucc, Fin.val_last] at h'; omega
    apply not_validTuple_of_mapped_three_extra_block_rival τ g f hpref x y z hxy hxz hyz hfx hfy hfz
      (A := 1) (B := 1) (C := 3) (by omega) (by omega : m-2+1+1+3=m+3) r hcover ?_ hg
    have hτsix : zmodScaleHom 8 M 6=48 := by simpa using zmodScaleHom_natCast 8 M 6
    have htotal : (∑ i, g i)=τ σ+g x+g y+g z := by
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [hpref, ← map_sum, ← Nat.cast_sum, sum_fixed_eq_cover_hole, τ, σ, x, y, z]
    rw [htotal]
    dsimp only [τ, r, π]
    rw [map_sub, map_sub, zmodScaleHom_castHom, hτsix]
    dsimp only [x, y, z]
    rw [hdouble2, hdouble]
    simp only [nsmul_eq_mul]
    ring
  have hσ : σ+1=((2^m-m : ℕ) : ZMod M) := by
    have hn : 2^m-m-1+1=2^m-m := by omega
    simpa only [Nat.cast_add, Nat.cast_one, σ] using congrArg (fun k : ℕ ↦ (k : ZMod M)) hn
  have hrc : r=((2^m-m : ℕ) : ZMod M) := by rw [← hr, ZMod.natCast_zmod_val]
  rw [← hσ] at hrc
  change π (g x)=-7
  dsimp [r] at hrc
  linear_combination -hrc

/-- A full own-size cover also forbids the outside total being a
single repeated outside coordinate in the quotient. The fibre is arbitrary. -/
theorem not_validTuple_of_actual_fibre_cover_repeated_outside_total
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)] (hk : 2 ≤ k)
    (g : Fin (m+k) → ZMod (d*M)) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=zmodScaleHom d M (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z)
    (j : Fin k) (hquot : k • ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m j))=
      ∑ i : Fin k, ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m i))) : ¬ ValidTuple g := by
  let τ := zmodScaleHom d M
  let π := ZMod.castHom (dvd_mul_right d M) (ZMod d)
  let f : Fin m → Fin (m+k) := Fin.castAdd k
  let e : Fin k → Fin (m+k) := Fin.natAdd m
  have hπprefix (i : Fin m) : π (g (f i))=0 := by
    rw [hpref, ← ZMod.natCast_zmod_val (u i), zmodScaleHom_natCast,
      map_natCast π, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hker : π ((∑ i, g i)-k • g (e j))=0 := by
    rw [map_sub, map_sum, map_nsmul, Fin.sum_univ_add]
    simp only [show ∀ i : Fin m, π (g (Fin.castAdd k i))=0 from hπprefix, Finset.sum_const_zero, zero_add]
    change (∑ i : Fin k, π (g (e i)))-k • π (g (e j))=0
    rw [hquot, sub_self]
  obtain ⟨w, hw⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hker
  let l : Fin k := if j=⟨0, by omega⟩ then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hlj : l ≠ j := by
    dsimp [l]
    split_ifs with h
    · subst j; intro h; have hv := congrArg Fin.val h; norm_num at hv
    · exact Ne.symm h
  have heinj : Function.Injective e := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [e, Fin.val_natAdd] at hv
    omega
  apply not_validTuple_of_actual_mapped_fibre_cover τ u g f hpref w (hcover w)
    (Multiset.replicate k (e j)) (by simp) ?_ (e l) ?_ ?_
  · simp only [Multiset.map_replicate, Multiset.sum_replicate]
    rw [hw]
    abel
  · intro i h
    have hv := congrArg Fin.val h
    simp only [f, e, Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  · intro hmem
    exact hlj (heinj (Multiset.mem_replicate.mp hmem).2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Elementary quotient arithmetic only: an injective three-coordinate
cube without a tripled-coordinate rival is a dyadic chain up to permutation. -/
theorem zmod_eight_three_extra_cube_cases (q : Fin 3 → ZMod 8)
    (hcube : Function.Injective (fun S : Finset (Fin 3) ↦ ∑ j ∈ S, q j))
    (htrip : ∀ i : Fin 3, 3*q i ≠ ∑ j, q j) :
    ∃ p : Equiv.Perm (Fin 3), (q (p 0)).val%2=1 ∧
      q (p 1)=2*q (p 0) ∧ q (p 2)=2*q (p 1) := by
  revert q
  decide

/-- Reindex only the actual outside coordinates, fixing the entire prefix. -/
theorem exists_perm_extending_outside {m k : ℕ} (p : Equiv.Perm (Fin k)) :
    ∃ e : Equiv.Perm (Fin (m+k)),
      (∀ i : Fin m, e (Fin.castAdd k i)=Fin.castAdd k i) ∧
      (∀ j : Fin k, e (Fin.natAdd m j)=Fin.natAdd m (p j)) := by
  let e : Equiv.Perm (Fin (m+k)) := finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin m)) p).trans finSumFinEquiv)
  exact ⟨e, by intro i; simp [e], by intro j; simp [e]⟩

/-- Both adjacent quotient relations force adjacent ACTUAL affine
doubling relations, by applying the one-hole cover to actual children. -/
theorem affine_chain_of_valid_octupled_three_extra_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M ≤ 2^m-2)
    (g : Fin (m+3) → ZMod (8*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc=zmodScaleHom 8 M (a i.val : ZMod M))
    (hy : ZMod.castHom (dvd_mul_right 8 M) (ZMod 8) (g (Fin.last (m+1)).castSucc)=
      2*ZMod.castHom (dvd_mul_right 8 M) (ZMod 8) (g (Fin.last m).castSucc.castSucc))
    (hz : ZMod.castHom (dvd_mul_right 8 M) (ZMod 8) (g (Fin.last (m+2)))=
      2*ZMod.castHom (dvd_mul_right 8 M) (ZMod 8) (g (Fin.last (m+1)).castSucc)) :
    g (Fin.last (m+1)).castSucc=2*g (Fin.last m).castSucc.castSucc+8 ∧
      g (Fin.last (m+2))=2*g (Fin.last (m+1)).castSucc+8 := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (8*M) := ⟨by omega⟩
  let π := ZMod.castHom (dvd_mul_right 8 M) (ZMod 8)
  let x : Fin (m+3) := (Fin.last m).castSucc.castSucc
  let y : Fin (m+3) := (Fin.last (m+1)).castSucc
  let z : Fin (m+3) := Fin.last (m+2)
  have hxy : x ≠ y := by intro h; have h' := congrArg Fin.val h; simp [x, y] at h'
  have hxz : x ≠ z := by intro h; have h' := congrArg Fin.val h; simp [x, z] at h'
  have hyz : y ≠ z := by intro h; have h' := congrArg Fin.val h; simp [y, z] at h'
  have hswap (j k : Fin (m+3)) (hj : m ≤ j.val) (hk : m ≤ k.val) :
      ∀ i : Fin m, g (Equiv.swap j k i.castSucc.castSucc.castSucc)=zmodScaleHom 8 M (a i.val : ZMod M) := by
    intro i
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact hpref i
    · intro h; have h' := congrArg Fin.val h; simp only [Fin.val_castSucc] at h'; omega
    · intro h; have h' := congrArg Fin.val h; simp only [Fin.val_castSucc] at h'; omega
  have hstep (p : Equiv.Perm (Fin (m+3)))
      (hp : ∀ i : Fin m, g (p i.castSucc.castSucc.castSucc)=zmodScaleHom 8 M (a i.val : ZMod M))
      (hquot : π (g (p x))=2*π (g (p y))) : g (p x)=2*g (p y)+8 := by
    exact extra_eq_affine_double_of_valid_scaled_short_prefix hm hM
      (fun i : Fin (m+2) ↦ g (p i.castSucc))
      (validTuple_embedding ⟨Fin.castSucc, Fin.castSucc_injective (m+2)⟩
        (fun i ↦ g (p i)) (validTuple_embedding p.toEmbedding g hg)) hp
      (by change π (g (p x)-2*g (p y))=0; rw [map_sub, map_mul, map_ofNat, hquot, sub_self])
  constructor
  · have h := hstep (Equiv.swap x y) (hswap x y (by simp [x]) (by simp [y]))
      (by simpa [π, x, y] using hy)
    simpa using h
  · have h := hstep (Equiv.swap x z) (hswap x z (by simp [x]) (by simp [z]))
      (by simpa [Equiv.swap_apply_def, hxy.symm, hyz, π, x, y, z] using hz)
    simpa [Equiv.swap_apply_def, hxy.symm, hyz] using h

/-- The actual outside chain and its final projection close the whole
tuple under one affine doubling map, including the power-gap prefix wrap. -/
theorem octupled_three_extra_prefix_closed_of_extra_relations
    {m t M : ℕ} [NeZero M] (hm : 3 ≤ m) (htm : t < m)
    (hM : M=2^m-2^t) (g : Fin (m+3) → ZMod (8*M))
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc=((8*a i.val : ℕ) : ZMod (8*M)))
    (hdouble : g (Fin.last (m+1)).castSucc=2*g (Fin.last m).castSucc.castSucc+8)
    (hdouble2 : g (Fin.last (m+2))=2*g (Fin.last (m+1)).castSucc+8)
    (hproj : ZMod.castHom (dvd_mul_left M 8) (ZMod M) (g (Fin.last m).castSucc.castSucc)=-7) :
    ∀ i, ∃ j, g j=2 • g i+8 := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (8*M) := ⟨by omega⟩
  have height : 8 • g (Fin.last m).castSucc.castSucc=-56 := by
    rw [← zmodScaleHom_castHom, hproj, map_neg]
    have h7 : zmodScaleHom 8 M 7=56 := by simpa using zmodScaleHom_natCast 8 M 7
    rw [h7]
  have hzzero : 2 • g (Fin.last (m+2))+8=0 := by
    rw [hdouble2, hdouble]
    simp only [nsmul_eq_mul] at height ⊢
    linear_combination height
  intro i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · refine ⟨(⟨0, by omega⟩ : Fin m).castSucc.castSucc.castSucc, ?_⟩
    rw [hpref, hzzero]
    norm_num [a]
  · refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · exact ⟨Fin.last (m+2), by simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hdouble2⟩
    · refine Fin.lastCases ?_ (fun k ↦ ?_) k
      · exact ⟨(Fin.last (m+1)).castSucc, by simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hdouble⟩
      · by_cases hk : k.val+1 < m
        · let j : Fin m := ⟨k.val+1, hk⟩
          refine ⟨j.castSucc.castSucc.castSucc, ?_⟩
          rw [hpref, hpref]
          have hn : 8*a (k.val+1)=2*(8*a k.val)+8 := by
            have hp : 0 < 2^k.val := by positivity
            simp only [a, pow_succ']; omega
          simpa only [j, Fin.val_mk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul] using
            congrArg (fun z : ℕ ↦ (z : ZMod (8*M))) hn
        · let j : Fin m := ⟨t, htm⟩
          refine ⟨j.castSucc.castSucc.castSucc, ?_⟩
          rw [hpref, hpref]
          have hkv : k.val=m-1 := by omega
          have hpow : 2^m=2*2^(m-1) := by rw [← pow_succ']; congr 1; omega
          have hp : 0 < 2^(m-1) := by positivity
          have hpt : 0 < 2^t := by positivity
          have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2:ℕ)) htm.le
          have hn : 2*(8*a k.val)+8=8*a t+8*M := by simp only [a, hkv]; omega
          have hc := congrArg (fun z : ℕ ↦ (z : ZMod (8*M))) hn
          rw [Nat.cast_add (8*a t), ZMod.natCast_self, add_zero] at hc
          simpa only [j, Fin.val_mk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul] using hc.symm

/-- Every index-eight coherent three-extra tuple below the binary
threshold forces fixed-set validity at the SAME modulus, for n>=8. -/
theorem valid_fixed_of_valid_octupled_three_extra_prefix_lt_two_pow
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m) (hupper : 8*M < 2^(m+3))
    (g : Fin (m+3) → ZMod (8*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc=zmodScaleHom 8 M (a i.val : ZMod M)) :
    Valid (m+3) (8*M) := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (8*M) := ⟨by omega⟩
  have hpow : 2^(m+3)=8*2^m := by rw [pow_add]; norm_num; ring
  have hv : Valid m M := by
    apply valid_fixed_of_valid_divisor_fixed_prefix
      (fun i : Fin (m+1) ↦ g i.castSucc.castSucc)
      (validTuple_embedding ⟨fun i ↦ i.castSucc.castSucc,
        (Fin.castSucc_injective (m+2)).comp (Fin.castSucc_injective (m+1))⟩ g hg)
    simpa only [zmodScaleHom_natCast] using hpref
  have hcard := Fintype.card_le_of_injective _ (validTuple_injective _ (validTuple_fixed_of_valid hv))
  simp only [Fintype.card_fin, ZMod.card] at hcard
  obtain ⟨t, htm, hMgap⟩ := exists_power_gap_of_valid_fixed_lt_two_pow (by omega) (by omega) (by omega) hv
  by_cases ht : t=0
  · have hN : 8*M=2^(m+3)-8 := by rw [ht] at hMgap; norm_num at hMgap; omega
    rw [hN]
    simpa only [show 2^3=(8:ℕ) by norm_num] using
      valid_gap (n := m+3) (t := 3) (by omega) (by norm_num; omega)
  have hMeven : Even M := by
    apply even_iff_two_dvd.mpr
    rw [hMgap]
    exact Nat.dvd_sub (dvd_pow_self 2 (by omega : m ≠ 0)) (dvd_pow_self 2 ht)
  have htwo : 2 ≤ 2^t := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2:ℕ)) (by omega : 1 ≤ t)
  have hMsmall : M ≤ 2^m-2 := by omega
  let π := ZMod.castHom (dvd_mul_right 8 M) (ZMod 8)
  let q : Fin 3 → ZMod 8 := fun j ↦ π (g (Fin.natAdd m j))
  have hcube := (quotient_cube_of_valid_subbinary_large_index_three_extra_prefix hm
    (by omega : 6 ≤ 8) hupper g hg hpref).1
  have hgrowth := three_mul_le_mersenne_pred hm
  have hpowm : 2^m=2*2^(m-1) := by rw [← pow_succ']; congr 1; omega
  have hMcover : M ≤ (1+2)*(2^(m-1)-1)-(m-2) := by omega
  have hcover (z : ZMod M) : ∃ s : Multiset (Fin m), s.card=m ∧
      (s.map (fun i : Fin m ↦ (a i.val : ZMod M))).sum=z := by
    obtain ⟨s, hs, hsz⟩ := exists_fixed_multiset_sum_of_modulus_le_initial_interval
      (d := 1) (by omega : 2 ≤ m) hMcover z
    exact ⟨s, by omega, hsz⟩
  have htrip (i : Fin 3) : 3*q i ≠ ∑ j, q j := by
    intro h
    exact not_validTuple_of_actual_fibre_cover_repeated_outside_total (by omega : 2 ≤ 3)
      g (fun i : Fin m ↦ (a i.val : ZMod M)) hpref hcover i
      (by simpa only [nsmul_eq_mul, Nat.cast_ofNat, q, π] using h) hg
  obtain ⟨p, hpodd, hpdouble, hpdouble2⟩ := zmod_eight_three_extra_cube_cases q hcube htrip
  obtain ⟨e, hepre, heoutside⟩ := exists_perm_extending_outside (m := m) p
  let u : Fin (m+3) → ZMod (8*M) := fun i ↦ g (e i)
  have hu : ValidTuple u := validTuple_embedding e.toEmbedding g hg
  have hupre (i : Fin m) : u i.castSucc.castSucc.castSucc=zmodScaleHom 8 M (a i.val : ZMod M) := by
    change g (e (Fin.castAdd 3 i))=_
    rw [hepre]
    exact hpref i
  have hequot (j : Fin 3) : π (u (Fin.natAdd m j))=q (p j) := by
    change π (g (e (Fin.natAdd m j)))=_
    rw [heoutside]
  have huxodd : Odd (u (Fin.last m).castSucc.castSucc).val := by
    have hxval := castHom_index_val (d := 8) (u (Fin.last m).castSucc.castSucc)
    have hxq : π (u (Fin.last m).castSucc.castSucc)=q (p 0) := hequot 0
    change (π (u (Fin.last m).castSucc.castSucc)).val=_ at hxval
    rw [hxq] at hxval
    refine ⟨(u (Fin.last m).castSucc.castSucc).val/2, ?_⟩
    omega
  have hyquot : π (u (Fin.last (m+1)).castSucc)=2*π (u (Fin.last m).castSucc.castSucc) := by
    change π (u (Fin.natAdd m 1))=2*π (u (Fin.natAdd m 0))
    rw [hequot, hequot, hpdouble]
  have hzquot : π (u (Fin.last (m+2)))=2*π (u (Fin.last (m+1)).castSucc) := by
    change π (u (Fin.natAdd m 2))=2*π (u (Fin.natAdd m 1))
    rw [hequot, hequot, hpdouble2]
  obtain ⟨hdouble, hdouble2⟩ := affine_chain_of_valid_octupled_three_extra_prefix
    (by omega) hMsmall u hu hupre hyquot hzquot
  have hproj := odd_extra_projection_eq_neg_seven_of_valid_octupled_three_extra_prefix
    (by omega) hMeven hMsmall u hu hupre huxodd hdouble hdouble2
  have hclosed := octupled_three_extra_prefix_closed_of_extra_relations (by omega) htm hMgap u
    (by simpa only [zmodScaleHom_natCast] using hupre) hdouble hdouble2 hproj
  have hbound := global_lower_bound_of_valid_affine_doubling_closed (by omega) u hu 8 hclosed
  have hN : 8*M=2^(m+3)-2^(t+3) := by
    rw [hMgap, Nat.mul_sub_left_distrib, pow_add, pow_add]
    norm_num
    omega
  have hpowlt : 2^(t+3) < 2^(m+3) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hlog := Nat.pow_log_le_self 2 (by omega : m+3 ≠ 0)
  have hgaple : 2^(t+3) ≤ m+3 := by unfold globalBound at hbound; omega
  rw [hN]
  exact valid_gap (by omega) hgaple

/-- Original-modulus affine transport preserves the complete index-eight result. -/
theorem valid_fixed_of_valid_affine_octupled_three_extra_prefix_lt_two_pow
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m)
    (g : Fin (m+3) → ZMod (8*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (φ : ZMod (8*M) ≃+ ZMod (8*M)) (b : ZMod (8*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc)=φ (zmodScaleHom 8 M (a i.val : ZMod M))+b)
    (hupper : 8*M < 2^(m+3)) : Valid (m+3) (8*M) := by
  apply valid_fixed_of_valid_octupled_three_extra_prefix_lt_two_pow hm hupper
    (fun i ↦ φ.symm (g (e i)-b))
    (validTuple_comp (validTuple_sub_const _ (validTuple_embedding e.toEmbedding g hg) b)
      φ.symm.toAddMonoidHom φ.symm.injective)
  intro i
  simp only [hpref, add_sub_cancel_right, AddEquiv.symm_apply_apply]

/-- The global bound holds for every coherent index-eight three-extra
tuple, n>=8, with arbitrary outside entries and original affine transport. -/
theorem global_lower_bound_of_valid_affine_octupled_three_extra_prefix
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m)
    (g : Fin (m+3) → ZMod (8*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (φ : ZMod (8*M) ≃+ ZMod (8*M)) (b : ZMod (8*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc)=φ (zmodScaleHom 8 M (a i.val : ZMod M))+b) :
    globalBound (m+3) ≤ 8*M := by
  by_cases hupper : 8*M < 2^(m+3)
  · have hv := valid_fixed_of_valid_affine_octupled_three_extra_prefix_lt_two_pow hm g hg e φ b hpref hupper
    exact (nmin_eq (by omega : 2 ≤ m+3)).2 ⟨by have h := Nat.pos_of_ne_zero (NeZero.ne M); omega, hv⟩
  · exact (Nat.sub_le _ _).trans (by omega)

/-- All exact even-stratum thresholds hold for the entire index-eight class. -/
theorem stratum_lower_bound_of_valid_affine_octupled_three_extra_prefix
    {m M s q : ℕ} [NeZero M] (hm : 5 ≤ m) (hq : Odd q) (hN : 8*M=2^s*q)
    (g : Fin (m+3) → ZMod (8*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (φ : ZMod (8*M) ≃+ ZMod (8*M)) (b : ZMod (8*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc)=φ (zmodScaleHom 8 M (a i.val : ZMod M))+b) :
    stratumBound (m+3) s ≤ 8*M := by
  by_cases hupper : 8*M < 2^(m+3)
  · have hv := valid_fixed_of_valid_affine_octupled_three_extra_prefix_lt_two_pow hm g hg e φ b hpref hupper
    rw [hN] at hv
    simpa only [hN] using stratum_lower_bound_of_valid_fixed (by omega : 3 ≤ m+3) hq hv
  · exact (Nat.sub_le _ _).trans (by omega)

end MinModulus
