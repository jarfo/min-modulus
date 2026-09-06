import MinModulus.SIThreeDoubleBound

/-!
# Index-three coherent prefixes with three arbitrary extras

The binary bound holds for every n >= 9 and positive modulus 3*M,
including odd moduli, with three arbitrary extras and original-modulus
unit-affine transport. The proof constructs actual subgroup rivals:
prefix-only total covers, valid two-extra children, tight one-extra fibre
covers, or two separated top-interval targets. Elementary quotient
arithmetic modulo three exhausts the cases. No external tuple census or
unrestricted G1/G2/G3 input is assumed.
-/

namespace MinModulus
open Finset

/-- Localization needs no assumed lower bound on the modulus: if the
extra is not the next SI entry, validity itself forces its total past the
prefix cover and prevents wrapping. -/
theorem fixed_prefix_extra_localization_of_not_next
    {m N : ℕ} [NeZero N] (hm : 3 ≤ m)
    (g : Fin (m+1) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc = (a i.val : ZMod N))
    (hextra : g (Fin.last m) ≠ (a m : ZMod N)) :
    4*(2^(m-1)-1)+1 ≤ (2^m-m-1)+(g (Fin.last m)).val ∧
      (2^m-m-1)+(g (Fin.last m)).val < N := by
  have hp := Nat.lt_two_pow_self (n := m-1)
  have hpow : 2^m=2*2^(m-1) := by rw [← pow_succ']; congr 1; omega
  let S := 2^m-m-1
  let z : ZMod N := S+g (Fin.last m)
  have hsum : (∑ i, g i) = z := by
    rw [Fin.sum_univ_castSucc]
    simp only [hprefix, ← Nat.cast_sum, sum_fixed_eq_cover_hole, z, S]
  have hhole : z.val ≠ 4*(2^(m-1)-1)-(m-2) := by
    intro heq
    have hz : z = ((4*(2^(m-1)-1)-(m-2) : ℕ) : ZMod N) := by
      rw [← heq, ZMod.natCast_zmod_val]
    have hnat : 4*(2^(m-1)-1)-(m-2) = S+a m := by dsimp [S, a]; omega
    rw [hnat, Nat.cast_add] at hz
    exact hextra (add_left_cancel hz)
  have hlarge : 4*(2^(m-1)-1) < z.val := by
    by_contra hc
    obtain ⟨s, hcard, hs⟩ := exists_fixed_multiset_sum_of_le_four_mul_except_hole
      (N := N) hm (by omega : z.val ≤ _) hhole
    apply not_validTuple_of_multiset_omission g (s.map Fin.castSucc)
      (by simpa using hcard) ?_ (Fin.last m) ?_ hg
    · simpa only [Multiset.map_map, Function.comp_def, hprefix,
        ZMod.natCast_zmod_val, hsum] using hs
    · intro hmem
      obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
      exact Fin.castSucc_ne_last i hi
  have hzlt := z.val_lt
  have hzval : z.val = (S+(g (Fin.last m)).val) % N := by
    dsimp only [z]
    rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_add_mod]
  have hx := (g (Fin.last m)).val_lt
  have hS : S < N := by dsimp [S]; omega
  have htotal : S+(g (Fin.last m)).val < 2*N := by omega
  have hnowrap : S+(g (Fin.last m)).val < N := by
    by_contra hc
    have hrem : (S+(g (Fin.last m)).val) % N = S+(g (Fin.last m)).val-N :=
      Nat.mod_eq_sub_mod (by omega) |>.trans (Nat.mod_eq_of_lt (by omega))
    rw [hzval, hrem] at hlarge
    dsimp [S] at hlarge
    omega
  rw [hzval, Nat.mod_eq_of_lt hnowrap] at hlarge
  exact ⟨by dsimp [S] at hlarge; omega, hnowrap⟩

/-- Three translates cover the localized range with the tight coin budget. -/
theorem one_extra_tight_budget_interval_cover
    (m L M X R : ℤ) (hm : 4 ≤ m) (hM : M ≤ 6*L-2*m+4)
    (hXlo : 2*L+m ≤ X) (hXhi : 2*L-m+1+X < M) (hRhi : R < M) :
    (R < 4*L-m+2) ∨ (X ≤ R ∧ R < X+3*L-m+2) ∨
      (2*X ≤ R ∧ R < 2*X+2*L-m+2) := by
  omega

/-- A valid one-extra SI tuple covers its group using its own number of
coins throughout a uniform range beyond the binary threshold. -/
theorem exists_multiset_sum_of_valid_one_extra_tight_modulus
    {m M : ℕ} [NeZero M] (hm : 4 ≤ m)
    (hM : (M : ℤ) ≤ 6*(2^(m-1)-1)-2*m+4)
    (u : Fin (m+1) → ZMod M) (hu : ValidTuple u)
    (hpref : ∀ i : Fin m, u i.castSucc = (a i.val : ZMod M)) (z : ZMod M) :
    ∃ s : Multiset (Fin (m+1)), s.card = m+1 ∧ (s.map u).sum = z := by
  have hp := Nat.lt_two_pow_self (n := m-1)
  have hmexp := Nat.lt_two_pow_self (n := m)
  have hpow : 2^m=2*2^(m-1) := by rw [← pow_succ']; congr 1; omega
  let L : ℤ := 2^(m-1)-1
  have hLcast : ((2^(m-1)-1 : ℕ) : ℤ) = L := by
    dsimp [L]; rw [Int.natCast_sub (by omega), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have hScast : ((2^m-m-1 : ℕ) : ℤ) = 2*L-m+1 := by
    have hpowz : (2:ℤ)^m = 2*(2:ℤ)^(m-1) := by exact_mod_cast hpow
    rw [Int.natCast_sub (by omega), Int.natCast_sub (by omega), Nat.cast_pow]
    push_cast; dsimp [L]; omega
  by_cases hnext : u (Fin.last m) = (a m : ZMod M)
  · have hfull : ∀ i, u i = (a i.val : ZMod M) := by
      intro i; exact Fin.lastCases hnext (fun j ↦ hpref j) i
    have hMnat : M ≤ (1+2)*(2^((m+1)-1)-1)-((m+1)-2) := by
      have hMi : (M : ℤ) ≤ 6*((2^(m-1)-1 : ℕ) : ℤ)-2*m+4 := by
        simpa only [hLcast] using hM
      simp only [Nat.add_sub_cancel]
      omega
    obtain ⟨s, hcard, hs⟩ := exists_fixed_multiset_sum_of_modulus_le_initial_interval
      (m := m+1) (d := 1) (by omega) hMnat z
    exact ⟨s, by omega, by simpa only [hfull] using hs⟩
  have hloc := fixed_prefix_extra_localization_of_not_next (by omega : 3 ≤ m) u hu hpref hnext
  have hXlo : 2*L+m ≤ ((u (Fin.last m)).val : ℤ) := by
    have h' : (4:ℤ)*((2^(m-1)-1 : ℕ) : ℤ)+1 ≤
        ((2^m-m-1 : ℕ) : ℤ)+(u (Fin.last m)).val := by exact_mod_cast hloc.1
    rw [hLcast, hScast] at h'; omega
  have hXhi : 2*L-m+1+((u (Fin.last m)).val : ℤ) < M := by
    have h' : ((2^m-m-1 : ℕ) : ℤ)+(u (Fin.last m)).val < M := by exact_mod_cast hloc.2
    rwa [hScast] at h'
  have hzlo : 0 ≤ (z.val : ℤ) := by exact_mod_cast Nat.zero_le z.val
  have hzhi : (z.val : ℤ) < M := by exact_mod_cast z.val_lt
  rcases one_extra_tight_budget_interval_cover m L M (u (Fin.last m)).val z.val
      (by exact_mod_cast hm) hM hXlo hXhi hzhi with h | h | h
  · obtain ⟨s, hs, hsum⟩ := exists_one_extra_sum_of_residual_cover (c := 2) (k := 0)
      hm (by omega) (by omega) u hpref z 0
      (by change 0 ≤ (z.val : ℤ)-0*(u (Fin.last m)).val+0*M; omega)
      (by change (z.val : ℤ)-0*(u (Fin.last m)).val+0*M < (6-2)*L-m+2; omega)
    exact ⟨s, by omega, hsum⟩
  · obtain ⟨s, hs, hsum⟩ := exists_one_extra_sum_of_residual_cover (c := 2) (k := 1)
      hm (by omega) (by omega) u hpref z 0 (by omega)
      (by change (z.val : ℤ)-1*(u (Fin.last m)).val+0*M < (6-3)*L-m+2; omega)
    exact ⟨s, by omega, hsum⟩
  · obtain ⟨s, hs, hsum⟩ := exists_one_extra_sum_of_residual_cover (c := 2) (k := 2)
      hm (by omega) (by omega) u hpref z 0 (by omega)
      (by change (z.val : ℤ)-2*(u (Fin.last m)).val+0*M < (6-4)*L-m+2; omega)
    exact ⟨s, by omega, hsum⟩

/-- One subgroup extra and two equal quotient residues are incompatible
with validity whenever the actual one-extra fibre has the tight cover. -/
theorem not_validTuple_of_scaled_three_extra_one_subgroup_same_coset
    {m d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 4 ≤ m)
    (hM : (M : ℤ) ≤ 6*(2^(m-1)-1)-2*m+4)
    (g : Fin (m+3) → ZMod (d*M))
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.last m).castSucc.castSucc) = 0)
    (hyz : ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.last (m+1)).castSucc) =
      ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.last (m+2)))) : ¬ ValidTuple g := by
  intro hg
  let τ := zmodScaleHom d M
  let π := ZMod.castHom (dvd_mul_right d M) (ZMod d)
  obtain ⟨t, ht⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hx
  let u : Fin (m+1) → ZMod M := Fin.lastCases t (fun i : Fin m ↦ (a i.val : ZMod M))
  have hu : ValidTuple u := validTuple_fixed_extra_of_valid_scaled_short_prefix
    (fun i : Fin (m+2) ↦ g i.castSucc)
    (validTuple_embedding ⟨Fin.castSucc, Fin.castSucc_injective (m+2)⟩ g hg)
    hpref (Fin.last m).castSucc (by simp) t ht.symm
  let y : Fin (m+3) := (Fin.last (m+1)).castSucc
  let z : Fin (m+3) := Fin.last (m+2)
  have hker : π ((∑ i, g i) - 2 • g y) = 0 := by
    have htotal : (∑ i, g i) = τ (2^m-m-1 : ℕ) +
        g (Fin.last m).castSucc.castSucc + g y + g z := by
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [hpref, ← map_sum, ← Nat.cast_sum, sum_fixed_eq_cover_hole, τ, y, z]
    rw [htotal, map_sub, map_add, map_add, map_add, map_nsmul]
    have hzero : π (τ (2^m-m-1 : ℕ)) = 0 := by
      rw [zmodScaleHom_natCast, map_natCast π, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [hzero, show π (g (Fin.last m).castSucc.castSucc)=0 from hx,
      show π (g y)=π (g z) from hyz]
    abel
  obtain ⟨w, hw⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hker
  have hcover := exists_multiset_sum_of_valid_one_extra_tight_modulus hm hM u hu
    (by intro i; simp [u]) w
  let f : Fin (m+1) → Fin (m+3) := fun i ↦ i.castSucc.castSucc
  have hf (i : Fin (m+1)) : g (f i) = τ (u i) := by
    refine Fin.lastCases ?_ (fun k ↦ ?_) i
    · simpa only [f, u, Fin.lastCases_last] using ht.symm
    · simpa only [f, u, Fin.lastCases_castSucc] using hpref k
  apply not_validTuple_of_actual_mapped_fibre_cover τ u g f hf w hcover
    (Multiset.replicate 2 y) (by simp)
    (by simp only [Multiset.map_replicate, Multiset.sum_replicate]; rw [hw]; abel)
    z ?_ ?_ hg
  · intro i hi
    have hval := congrArg Fin.val hi
    simp only [f, z, Fin.val_castSucc, Fin.val_last] at hval
    omega
  · intro hmem
    have heq := (Multiset.mem_replicate.mp hmem).2
    exact Fin.castSucc_ne_last _ heq.symm

/-- Two actual subgroup extras reflect to a valid two-extra child, so
the child's proved global lower bound already excludes a small modulus. -/
theorem not_validTuple_of_scaled_three_extra_two_subgroup_extras
    {m d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 3 ≤ m)
    (hM : M < globalBound (m+2))
    (g : Fin (m+3) → ZMod (d*M))
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.last m).castSucc.castSucc) = 0)
    (hy : ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.last (m+1)).castSucc) = 0) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨x, hx'⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hx
  obtain ⟨y, hy'⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hy
  let u : Fin (m+2) → ZMod M := Fin.lastCases y (Fin.lastCases x (fun i : Fin m ↦ (a i.val : ZMod M)))
  have humap (i : Fin (m+2)) : zmodScaleHom d M (u i) = g i.castSucc := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [u, Fin.lastCases_last] using hy'
    · refine Fin.lastCases ?_ (fun k ↦ ?_) j
      · simpa only [u, Fin.lastCases_castSucc, Fin.lastCases_last] using hx'
      · simpa only [u, Fin.lastCases_castSucc] using (hpref k).symm
  have hu : ValidTuple u := by
    apply validTuple_of_comp (zmodScaleHom d M)
    have hv := validTuple_embedding ⟨Fin.castSucc, Fin.castSucc_injective (m+2)⟩ g hg
    change ValidTuple (fun i : Fin (m+2) ↦ g i.castSucc) at hv
    simpa only [humap] using hv
  have hb := global_lower_bound_of_valid_scaled_fixed_short_prefix hm u hu (Equiv.refl _) 1 0
    (by intro i; simp [u])
  omega

/-- A subgroup-valued total is represented entirely in the actual prefix
when its n-coin initial interval covers the whole subgroup. -/
theorem not_validTuple_of_scaled_three_extra_total_in_subgroup
    {m d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 2 ≤ m)
    (hM : M ≤ (4+2)*(2^(m-1)-1)-(m-2))
    (g : Fin (m+3) → ZMod (d*M))
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M))
    (htotal : ZMod.castHom (dvd_mul_right d M) (ZMod d) (∑ i, g i) = 0) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨w, hw⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ htotal
  obtain ⟨s, hcard, hs⟩ := exists_fixed_multiset_sum_of_modulus_le_initial_interval
    (d := 4) hm hM w
  apply not_validTuple_of_actual_mapped_fibre_cover (zmodScaleHom d M)
    (fun i : Fin m ↦ (a i.val : ZMod M)) g
    (fun i ↦ i.castSucc.castSucc.castSucc) hpref w ⟨s, hcard, hs⟩ 0
    (by simp; omega) (by simpa using hw) (Fin.last (m+2)) ?_ (by simp) hg
  intro i hi
  exact Fin.castSucc_ne_last _ hi

/-- Two actual pair targets in a subgroup force two separated points in
the top interval. This applies to any subgroup index, not only parity. -/
theorem not_validTuple_of_scaled_three_extra_two_subgroup_targets
    {m d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 4 ≤ m)
    (hM : M < (5*(2^(m-1)-1)-(m-2)) + (2^m-m-1) + 2)
    (g : Fin (m+3) → ZMod (d*M))
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M))
    (hyz : ZMod.castHom (dvd_mul_right d M) (ZMod d)
      (g (Fin.last (m+1)).castSucc + g (Fin.last (m+2))) = 0)
    (hxz : ZMod.castHom (dvd_mul_right d M) (ZMod d)
      (g (Fin.last m).castSucc.castSucc + g (Fin.last (m+2))) = 0) : ¬ ValidTuple g := by
  intro hg
  let τ := zmodScaleHom d M
  let π := ZMod.castHom (dvd_mul_right d M) (ZMod d)
  let x : Fin (m+3) := (Fin.last m).castSucc.castSucc
  let y : Fin (m+3) := (Fin.last (m+1)).castSucc
  let z : Fin (m+3) := Fin.last (m+2)
  let f : Fin m → Fin (m+3) := fun i ↦ i.castSucc.castSucc.castSucc
  have hxy : x ≠ y := by intro h; have h' := congrArg Fin.val h; simp [x, y] at h'
  have hxz' : x ≠ z := by intro h; have h' := congrArg Fin.val h; simp [x, z] at h'
  have hyz' : y ≠ z := by intro h; have h' := congrArg Fin.val h; simp [y, z] at h'
  have hfx (i : Fin m) : f i ≠ x := by
    intro h; have h' := congrArg Fin.val h; simp only [f, x, Fin.val_castSucc, Fin.val_last] at h'; omega
  have hfy (i : Fin m) : f i ≠ y := by
    intro h; have h' := congrArg Fin.val h; simp only [f, y, Fin.val_castSucc, Fin.val_last] at h'; omega
  have htotal : (∑ i, g i) = τ (2^m-m-1 : ℕ)+g x+g y+g z := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [hpref, ← map_sum, ← Nat.cast_sum, sum_fixed_eq_cover_hole, τ, x, y, z]
  obtain ⟨u', hu'⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hyz
  obtain ⟨v', hv'⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hxz
  let u : ZMod M := (2^m-m-1 : ℕ)+u'
  let v : ZMod M := (2^m-m-1 : ℕ)+v'
  have hu : τ u = (∑ i, g i)-g x := by dsimp [u]; rw [map_add, hu', htotal]; dsimp [y,z]; abel
  have hv : τ v = (∑ i, g i)-g y := by dsimp [v]; rw [map_add, hv', htotal]; dsimp [x,z]; abel
  have hU := three_extra_pair_target_large hm τ g hg f hpref y x hxy.symm hfy u hu
  have hV := three_extra_pair_target_large hm τ g hg f hpref x y hxy hfx v hv
  have hsep := three_extra_pair_targets_separated hm τ g hg f hpref x y z
    hxy hxz' hyz' hfx hfy htotal u v hu hv
  have huM := u.val_lt
  have hvM := v.val_lt
  omega

/-- All quotient triples modulo three fall into the four already
constructed rival mechanisms. This is only elementary quotient arithmetic. -/
theorem zmod_three_extra_subgroup_cases (x y z : ZMod 3) :
    x+y+z=0 ∨
    (x=0 ∧ y=0) ∨ (x=0 ∧ z=0) ∨ (y=0 ∧ z=0) ∨
    (x=0 ∧ y=z) ∨ (y=0 ∧ x=z) ∨ (z=0 ∧ x=y) ∨
    (y+z=0 ∧ x+z=0) ∨ (y+z=0 ∧ x+y=0) ∨ (x+z=0 ∧ x+y=0) := by
  revert x y z
  decide

/-- Every quotient-residue pattern is excluded at index three below the
binary threshold, uniformly in n>=9 and in all positive moduli. -/
theorem not_validTuple_of_tripled_three_extra_prefix_subbinary
    {m M : ℕ} [NeZero M] (hm : 6 ≤ m) (hupper : 3*M < 2^(m+3))
    (g : Fin (m+3) → ZMod (3*M))
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc = zmodScaleHom 3 M (a i.val : ZMod M)) :
    ¬ ValidTuple g := by
  intro hg
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (3*M) := ⟨by omega⟩
  have hgrowth := three_mul_le_mersenne_pred (m := m-1) (by omega)
  have he : m-1-1=m-2 := by omega
  rw [he] at hgrowth
  have hpow0 : 2^(m-1)=2*2^(m-2) := by rw [← pow_succ']; congr 1; omega
  have hpow : 2^m=2*2^(m-1) := by rw [← pow_succ']; congr 1; omega
  have hpow3 : 2^(m+3)=16*2^(m-1) := by rw [pow_add, hpow]; norm_num; ring
  have hpow2 : 2^(m+2)=8*2^(m-1) := by rw [pow_add, hpow]; norm_num; ring
  have hMtotal : M ≤ (4+2)*(2^(m-1)-1)-(m-2) := by omega
  have hMchild : M < globalBound (m+2) := by
    have hlog := Nat.pow_log_le_self 2 (by omega : m+2≠0)
    unfold globalBound
    omega
  have hMpair : M < (5*(2^(m-1)-1)-(m-2))+(2^m-m-1)+2 := by omega
  have hMtight : (M : ℤ) ≤ 6*(2^(m-1)-1)-2*m+4 := by
    have hnat : M+2*m+2 ≤ 6*2^(m-1) := by omega
    have hcast : (M : ℤ)+2*m+2 ≤ 6*(2:ℤ)^(m-1) := by exact_mod_cast hnat
    omega
  let π := ZMod.castHom (dvd_mul_right 3 M) (ZMod 3)
  let x : Fin (m+3) := (Fin.last m).castSucc.castSucc
  let y : Fin (m+3) := (Fin.last (m+1)).castSucc
  let z : Fin (m+3) := Fin.last (m+2)
  have hxy : x ≠ y := by intro h; have h' := congrArg Fin.val h; simp [x, y] at h'
  have hxz : x ≠ z := by intro h; have h' := congrArg Fin.val h; simp [x, z] at h'
  have hyz : y ≠ z := by intro h; have h' := congrArg Fin.val h; simp [y, z] at h'
  have hswap (j k : Fin (m+3)) (hj : m ≤ j.val) (hk : m ≤ k.val) :
      ∀ i : Fin m, g (Equiv.swap j k i.castSucc.castSucc.castSucc) =
        zmodScaleHom 3 M (a i.val : ZMod M) := by
    intro i
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact hpref i
    · intro heq; have h' := congrArg Fin.val heq; simp only [Fin.val_castSucc] at h'; omega
    · intro heq; have h' := congrArg Fin.val heq; simp only [Fin.val_castSucc] at h'; omega
  have h2 (p : Equiv.Perm (Fin (m+3)))
      (hp : ∀ i : Fin m, g (p i.castSucc.castSucc.castSucc) = zmodScaleHom 3 M (a i.val : ZMod M))
      (ha : π (g (p x)) = 0) (hb : π (g (p y)) = 0) : False :=
    not_validTuple_of_scaled_three_extra_two_subgroup_extras (by omega) hMchild
      (fun i ↦ g (p i)) hp ha hb (validTuple_embedding p.toEmbedding g hg)
  have h1 (p : Equiv.Perm (Fin (m+3)))
      (hp : ∀ i : Fin m, g (p i.castSucc.castSucc.castSucc) = zmodScaleHom 3 M (a i.val : ZMod M))
      (ha : π (g (p x)) = 0) (hb : π (g (p y)) = π (g (p z))) : False :=
    not_validTuple_of_scaled_three_extra_one_subgroup_same_coset (by omega) hMtight
      (fun i ↦ g (p i)) hp ha hb (validTuple_embedding p.toEmbedding g hg)
  have hT (p : Equiv.Perm (Fin (m+3)))
      (hp : ∀ i : Fin m, g (p i.castSucc.castSucc.castSucc) = zmodScaleHom 3 M (a i.val : ZMod M))
      (ha : π (g (p y))+π (g (p z)) = 0) (hb : π (g (p x))+π (g (p z)) = 0) : False :=
    not_validTuple_of_scaled_three_extra_two_subgroup_targets (by omega) hMpair
      (fun i ↦ g (p i)) hp (by simpa only [map_add] using ha)
      (by simpa only [map_add] using hb) (validTuple_embedding p.toEmbedding g hg)
  rcases zmod_three_extra_subgroup_cases (π (g x)) (π (g y)) (π (g z)) with
    h | h | h | h | h | h | h | h | h | h
  · have htotal : π (∑ i, g i) = 0 := by
      rw [map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      have hzero (i : Fin m) : π (g i.castSucc.castSucc.castSucc)=0 := by
        rw [hpref, zmodScaleHom_natCast, map_natCast π, Nat.cast_mul, ZMod.natCast_self, zero_mul]
      simpa only [hzero, Finset.sum_const_zero, zero_add, x, y, z] using h
    exact not_validTuple_of_scaled_three_extra_total_in_subgroup (by omega) hMtotal g hpref htotal hg
  · exact h2 (Equiv.refl _) hpref h.1 h.2
  · apply h2 (Equiv.swap y z) (hswap y z (by simp [y]) (by simp [z]))
    · simpa [Equiv.swap_apply_def, hxy, hxz] using h.1
    · simpa using h.2
  · apply h2 (Equiv.swap x z) (hswap x z (by simp [x]) (by simp [z]))
    · simpa using h.2
    · simpa [Equiv.swap_apply_def, hxy.symm, hyz] using h.1
  · exact h1 (Equiv.refl _) hpref h.1 h.2
  · apply h1 (Equiv.swap x y) (hswap x y (by simp [x]) (by simp [y]))
    · simpa using h.1
    · simpa [Equiv.swap_apply_def, hxz.symm, hyz.symm] using h.2
  · apply h1 (Equiv.swap x z) (hswap x z (by simp [x]) (by simp [z]))
    · simpa using h.1
    · simpa [Equiv.swap_apply_def, hxy.symm, hyz] using h.2.symm
  · exact hT (Equiv.refl _) hpref h.1 h.2
  · apply hT (Equiv.swap y z) (hswap y z (by simp [y]) (by simp [z]))
    · simpa [add_comm] using h.1
    · simpa [Equiv.swap_apply_def, hxy, hxz] using h.2
  · apply hT (Equiv.swap x z) (hswap x z (by simp [x]) (by simp [z]))
    · simpa [Equiv.swap_apply_def, hxy.symm, hyz, add_comm] using h.2
    · simpa [add_comm] using h.1

/-- A coherent index-three n-3 prefix with three arbitrary extras forces
the binary lower bound, for all n>=9 and positive moduli. -/
theorem binary_lower_bound_of_valid_affine_tripled_three_extra_prefix
    {m M : ℕ} [NeZero M] (hm : 6 ≤ m)
    (g : Fin (m+3) → ZMod (3*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (φ : ZMod (3*M) ≃+ ZMod (3*M)) (b : ZMod (3*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (zmodScaleHom 3 M (a i.val : ZMod M))+b) :
    2^(m+3) ≤ 3*M := by
  by_contra h
  apply not_validTuple_of_tripled_three_extra_prefix_subbinary hm (by omega)
    (fun i ↦ φ.symm (g (e i)-b))
    (by intro i; simp only [hpref, add_sub_cancel_right, AddEquiv.symm_apply_apply])
  exact validTuple_comp (validTuple_sub_const _ (validTuple_embedding e.toEmbedding g hg) b)
    φ.symm.toAddMonoidHom φ.symm.injective

/-- The index-three binary bound implies the global and all stratum
thresholds, including odd moduli, without G1/G2/G3 assumptions. -/
theorem global_and_stratum_lower_bound_of_valid_affine_tripled_three_extra_prefix
    {m M : ℕ} [NeZero M] (hm : 6 ≤ m)
    (g : Fin (m+3) → ZMod (3*M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (φ : ZMod (3*M) ≃+ ZMod (3*M)) (b : ZMod (3*M))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc) = φ (zmodScaleHom 3 M (a i.val : ZMod M))+b) :
    globalBound (m+3) ≤ 3*M ∧ ∀ s : ℕ, stratumBound (m+3) s ≤ 3*M := by
  have h := binary_lower_bound_of_valid_affine_tripled_three_extra_prefix hm g hg e φ b hpref
  exact ⟨(Nat.sub_le _ _).trans h, fun s ↦ (Nat.sub_le _ _).trans h⟩

end MinModulus
