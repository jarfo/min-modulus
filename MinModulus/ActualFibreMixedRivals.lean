import MinModulus.ActualFibreSumsetPacking

/-!
# Complete mixed-rival criterion for arbitrary actual fibres

For a cyclic actual fibre with two extras, parent validity is equivalent
to fibre validity and avoidance of every nonstandard outside-multiplicity
residual in the corresponding exact coin sumset. There is no restriction
to an omitted outside coordinate: this criterion also includes
mixed rivals in which both outsiders occur with positive multiplicity.

For two odd outsiders x,y modulo 2M, set alpha=x mod M and extract the
ACTUAL divided difference tau(w)=y-x. With 2q outside coins, B of them
on y, the residual target is
  T(q,B)=sum(u)+alpha+w-q*alpha-B*w,
and the prefix budget is m+2-2q. Validity is exactly fibre validity plus
T(q,B) not in C_(m+2-2q), for all 2q<=m+2, B<=2q, (q,B)!=(1,1).
The criterion is general in m and M and requires no SI or criticality.
It does NOT prove that a target must be covered at every critical modulus;
that is the remaining obstruction in the two-outsider G1 case.
-/

namespace MinModulus
open Finset

/-- Natural multiplicities give an actual multiset with the same exact
cardinality and weighted sum, in any additive commutative group. -/
theorem exists_multiset_sum_card_of_nat_weights
    {m : ℕ} {G : Type*} [AddCommGroup G] (u : Fin m → G) (c : Fin m → ℕ) :
    ∃ s : Multiset (Fin m), s.card=∑ i, c i ∧ (s.map u).sum=∑ i, c i • u i := by
  induction m with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨s, hs, hsum⟩ := ih (fun i ↦ u i.castSucc) (fun i ↦ c i.castSucc)
    refine ⟨s.map Fin.castSucc+Multiset.replicate (c (Fin.last m)) (Fin.last m), ?_, ?_⟩
    · simp only [Multiset.card_add, Multiset.card_map, Multiset.card_replicate, hs, Fin.sum_univ_castSucc]
    · simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_map, Function.comp_def,
        Multiset.map_replicate, Multiset.sum_replicate, hsum, Fin.sum_univ_castSucc]

/-- Scaling into the actual cyclic subgroup is injective. -/
theorem zmodScaleHom_injective
    {d M : ℕ} [NeZero M] [NeZero (d*M)] : Function.Injective (zmodScaleHom d M) := by
  have hNpos := Nat.pos_of_ne_zero (NeZero.ne (d*M))
  have hdpos := Nat.pos_of_mul_pos_right hNpos
  intro x y h
  have hcast : ((d*x.val : ℕ) : ZMod (d*M))=((d*y.val : ℕ) : ZMod (d*M)) := by
    simpa only [← zmodScaleHom_natCast, ZMod.natCast_zmod_val] using h
  have hx : d*x.val < d*M := Nat.mul_lt_mul_of_pos_left x.val_lt hdpos
  have hy : d*y.val < d*M := Nat.mul_lt_mul_of_pos_left y.val_lt hdpos
  have hval := congrArg ZMod.val hcast
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hval
  apply ZMod.val_injective
  nlinarith

/-- A nonstandard pair of outside multiplicities and an actual fibre
cover gives a full rival, without requiring any outside omission. -/
theorem not_validTuple_of_actual_fibre_two_extra_rival
    {m d M K A B : ℕ} [NeZero M]
    (g : Fin (m+2) → ZMod (d*M)) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc=zmodScaleHom d M (u i))
    (hcard : K+A+B=m+2) (hcounts : A ≠ 1 ∨ B ≠ 1)
    (z : ZMod M) (hcover : z ∈ actualFibreCoinCover u K)
    (hsum : zmodScaleHom d M z+A • g (Fin.last m).castSucc+B • g (Fin.last (m+1))=∑ i, g i) :
    ¬ ValidTuple g := by
  classical
  intro hg
  obtain ⟨s, hs, hsz⟩ := (Finset.mem_filter.mp hcover).2
  let τ := zmodScaleHom d M
  let f : Fin m → Fin (m+2) := fun i ↦ i.castSucc.castSucc
  let x : Fin (m+2) := (Fin.last m).castSucc
  let y : Fin (m+2) := Fin.last (m+1)
  let t := s.map f+Multiset.replicate A x+Multiset.replicate B y
  have hxy : x ≠ y := Fin.castSucc_ne_last _
  have hx (i : Fin m) : f i ≠ x := by
    intro h; exact Fin.castSucc_ne_last i (Fin.castSucc_injective (m+1) h)
  have hy (i : Fin m) : f i ≠ y := Fin.castSucc_ne_last _
  have htcard : t.card=m+2 := by
    simpa only [t, Multiset.card_add, Multiset.card_map, Multiset.card_replicate, hs] using hcard
  have hmap : ((s.map f).map g).sum=τ z := by
    rw [Multiset.map_map]
    change (s.map (fun i ↦ g (f i))).sum=τ z
    simp only [show ∀ i, g (f i)=τ (u i) from hpref]
    simpa only [map_multiset_sum, Multiset.map_map, Function.comp_def] using congrArg τ hsz
  have htsum : (t.map g).sum=∑ i, g i := by
    simpa only [t, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, hmap] using hsum
  have hnot (j : Fin (m+2)) (hj : ∀ i, f i ≠ j) : j ∉ s.map f := by
    intro hmem
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
    exact hj i hi
  rcases hcounts with hA | hB
  · have h := multiset_count_eq_one_of_validTuple g hg t htcard htsum x
    apply hA
    simpa [t, Multiset.count_replicate, Multiset.count_eq_zero.mpr (hnot x hx), hxy, Ne.symm hxy] using h
  · have h := multiset_count_eq_one_of_validTuple g hg t htcard htsum y
    apply hB
    simpa [t, Multiset.count_replicate, Multiset.count_eq_zero.mpr (hnot y hy), hxy, Ne.symm hxy] using h

/-- COMPLETE actual-fibre criterion: fibre validity plus exclusion of
all nonstandard two-extra residual targets is equivalent to parent validity.
No SI structure or omission-only restriction is imposed. -/
theorem validTuple_iff_actual_fibre_two_extra_targets
    {m d M : ℕ} [NeZero M] [NeZero (d*M)]
    (g : Fin (m+2) → ZMod (d*M)) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc=zmodScaleHom d M (u i)) :
    ValidTuple g ↔ ValidTuple u ∧
      ∀ K A B : ℕ, K+A+B=m+2 → (A ≠ 1 ∨ B ≠ 1) → ∀ z : ZMod M,
        zmodScaleHom d M z+A • g (Fin.last m).castSucc+B • g (Fin.last (m+1))=∑ i, g i →
        z ∉ actualFibreCoinCover u K := by
  constructor
  · intro hg
    constructor
    · apply validTuple_of_comp (zmodScaleHom d M)
      have hv := validTuple_embedding ⟨fun i : Fin m ↦ i.castSucc.castSucc,
        (Fin.castSucc_injective (m+1)).comp (Fin.castSucc_injective m)⟩ g hg
      change ValidTuple (fun i : Fin m ↦ g i.castSucc.castSucc) at hv
      simpa only [hpref] using hv
    · intro K A B hcard hcounts z hz hcover
      exact not_validTuple_of_actual_fibre_two_extra_rival g u hpref hcard hcounts z hcover hz hg
  · rintro ⟨hu, havoid⟩ c hc hsum
    let A := c (Fin.last m).castSucc
    let B := c (Fin.last (m+1))
    let K := ∑ i : Fin m, c i.castSucc.castSucc
    let z : ZMod M := ∑ i : Fin m, c i.castSucc.castSucc • u i
    have hcard : K+A+B=m+2 := by
      simpa only [Fin.sum_univ_castSucc, K, A, B] using hc
    have hvalue : zmodScaleHom d M z+A • g (Fin.last m).castSucc+B • g (Fin.last (m+1))=∑ i, g i := by
      simpa only [Fin.sum_univ_castSucc, hpref, ← map_nsmul, ← map_sum, z, A, B] using hsum
    have hzmem : z ∈ actualFibreCoinCover u K := by
      classical
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, exists_multiset_sum_card_of_nat_weights u (fun i ↦ c i.castSucc.castSucc)⟩
    have hAB : A=1 ∧ B=1 := by
      by_contra h
      have hne : A ≠ 1 ∨ B ≠ 1 := by tauto
      exact havoid K A B hcard hne z hvalue hzmem
    have hK : K=m := by omega
    have hz : z=∑ i, u i := by
      apply zmodScaleHom_injective (d := d) (M := M)
      have htotal : (∑ i, g i)=zmodScaleHom d M (∑ i, u i)+g (Fin.last m).castSucc+g (Fin.last (m+1)) := by
        simp only [Fin.sum_univ_castSucc, hpref, ← map_sum]
      rw [hAB.1, hAB.2, one_nsmul, one_nsmul, htotal] at hvalue
      exact add_right_cancel (add_right_cancel hvalue)
    have hones := hu (fun i : Fin m ↦ c i.castSucc.castSucc) hK hz
    intro i
    refine Fin.lastCases hAB.2 (fun j ↦ ?_) i
    exact Fin.lastCases hAB.1 (fun l ↦ hones l) j

/-- The residual target for 2q outside coins, B of them on the second
odd outside entry. Here alpha is the first entry's projection to M and
w is the ACTUAL divided difference between the outside entries. -/
def actualTwoOddTarget {m M : ℕ} (u : Fin m → ZMod M) (alpha w : ZMod M) (q B : ℕ) : ZMod M :=
  (∑ i, u i)+alpha+w-q • alpha-B • w

/-- Exact upstairs identity for every mixed outside multiplicity pair. -/
theorem actual_two_odd_target_identity
    {m M A B q : ℕ} [NeZero M] [NeZero (2*M)]
    (g : Fin (m+2) → ZMod (2*M)) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc=zmodScaleHom 2 M (u i))
    (w : ZMod M) (hw : zmodScaleHom 2 M w=g (Fin.last (m+1))-g (Fin.last m).castSucc)
    (hAB : A+B=2*q) :
    zmodScaleHom 2 M (actualTwoOddTarget u
      (ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last m).castSucc)) w q B)+
      A • g (Fin.last m).castSucc+B • g (Fin.last (m+1))=∑ i, g i := by
  let τ := zmodScaleHom 2 M
  have htotal : (∑ i, g i)=τ (∑ i, u i)+g (Fin.last m).castSucc+g (Fin.last (m+1)) := by
    simp only [Fin.sum_univ_castSucc, hpref, ← map_sum, τ]
  rw [htotal]
  simp only [actualTwoOddTarget, map_sub, map_add, map_nsmul, zmodScaleHom_castHom, hw]
  simp only [nsmul_eq_mul]
  have hcast : (A : ZMod (2*M))+(B : ZMod (2*M))=2*(q : ZMod (2*M)) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun n : ℕ ↦ (n : ZMod (2*M))) hAB
  dsimp only [τ]
  linear_combination g (Fin.last m).castSucc*hcast

/-- COMPLETE grid criterion for two odd outsiders in an arbitrary
actual fibre. All allowed outside multiplicities are covered, not only
omission rivals. The remaining target-cover problem is explicit. -/
theorem validTuple_iff_actual_two_odd_target_grid
    {m M : ℕ} [NeZero M] [NeZero (2*M)]
    (g : Fin (m+2) → ZMod (2*M)) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc=zmodScaleHom 2 M (u i))
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last m).castSucc)=1)
    (hy : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last (m+1)))=1)
    (w : ZMod M) (hw : zmodScaleHom 2 M w=g (Fin.last (m+1))-g (Fin.last m).castSucc) :
    ValidTuple g ↔ ValidTuple u ∧
      ∀ q B : ℕ, 2*q ≤ m+2 → B ≤ 2*q → (q ≠ 1 ∨ B ≠ 1) →
        actualTwoOddTarget u (ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last m).castSucc)) w q B
          ∉ actualFibreCoinCover u (m+2-2*q) := by
  rw [validTuple_iff_actual_fibre_two_extra_targets g u hpref]
  constructor
  · rintro ⟨hu, havoid⟩
    refine ⟨hu, ?_⟩
    intro q B hq hB hnonstd
    apply havoid (m+2-2*q) (2*q-B) B (by omega) (by omega)
    exact actual_two_odd_target_identity g u hpref w hw (by omega)
  · rintro ⟨hu, hgrid⟩
    refine ⟨hu, ?_⟩
    intro K A B hcard hnonstd z hz
    let π := ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
    have hπscale (v : ZMod M) : π (zmodScaleHom 2 M v)=0 := by
      rw [← ZMod.natCast_zmod_val v, zmodScaleHom_natCast, map_natCast π,
        Nat.cast_mul, ZMod.natCast_self, zero_mul]
    have hπtotal : π (∑ i, g i)=0 := by
      rw [map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      have hpre (i : Fin m) : π (g i.castSucc.castSucc)=0 := by rw [hpref, hπscale]
      simp only [hpre, Finset.sum_const_zero, zero_add]
      rw [hx, hy]
      decide
    have hABcast : ((A+B : ℕ) : ZMod 2)=0 := by
      have h := congrArg π hz
      rw [map_add, map_add, hπscale, map_nsmul, map_nsmul, hx, hy, hπtotal] at h
      simpa only [zero_add, nsmul_eq_mul, mul_one, Nat.cast_add] using h
    obtain ⟨q, hAB⟩ := (ZMod.natCast_eq_zero_iff (A+B) 2).mp hABcast
    have hq : 2*q ≤ m+2 := by omega
    have hB : B ≤ 2*q := by omega
    have hstd : q ≠ 1 ∨ B ≠ 1 := by omega
    have hidentity := actual_two_odd_target_identity g u hpref w hw hAB
    have hzt : z=actualTwoOddTarget u
        (ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last m).castSucc)) w q B := by
      apply zmodScaleHom_injective (d := 2) (M := M)
      exact add_right_cancel (add_right_cancel (hz.trans hidentity.symm))
    have hK : K=m+2-2*q := by omega
    rw [hzt, hK]
    exact hgrid q B hq hB hstd

/-- The divided difference required by the complete grid is extracted
from the actual two odd entries, not assumed as a normal-form input. -/
theorem exists_actual_two_odd_target_grid
    {m M : ℕ} [NeZero M] [NeZero (2*M)]
    (g : Fin (m+2) → ZMod (2*M)) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc=zmodScaleHom 2 M (u i))
    (hx : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last m).castSucc)=1)
    (hy : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g (Fin.last (m+1)))=1) :
    ∃ w : ZMod M, zmodScaleHom 2 M w=g (Fin.last (m+1))-g (Fin.last m).castSucc ∧
      (ValidTuple g ↔ ValidTuple u ∧
        ∀ q B : ℕ, 2*q ≤ m+2 → B ≤ 2*q → (q ≠ 1 ∨ B ≠ 1) →
          actualTwoOddTarget u (ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last m).castSucc)) w q B
            ∉ actualFibreCoinCover u (m+2-2*q)) := by
  obtain ⟨w, hw⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero
    (g (Fin.last (m+1))-g (Fin.last m).castSucc)
    (by rw [map_sub, hy, hx, sub_self])
  exact ⟨w, hw, validTuple_iff_actual_two_odd_target_grid g u hpref hx hy w hw⟩

end MinModulus
