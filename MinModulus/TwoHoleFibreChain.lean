import MinModulus.OneHoleFibreChain

/-!
# Two-hole parity extraction and retained outside chains

An integer-valued character proves that a two-hole cube of dimension
at least two has one hole of each parity and an actual odd coordinate.
For odd half order, one odd-coordinate deletion removes any half entry
or the unique possible antipodal collision. Retained doubles are then
nonzero and injective, and the single even hole permits at most one
escape. Almost-doubling geometry gives an actual retained quotient chain.

This applies to arbitrary actual full-cover fibres under the proved
represented-double rival rule. For cycle fibres, thin covers lift the
chain upstairs after an actual same-modulus subtuple deletion. The
resulting size bound excludes the almost-half first-even endpoint for
cycle size at least three, giving the stronger binary bound in all
dimensions. The valid size-two endpoint is explicitly not excluded.
Cube deletion here is not asserted to be G1 valid-tuple half descent.
-/

namespace MinModulus
open Finset

/-- A two-hole injective cube of dimension at least two has an odd
coordinate and exactly one missing value of each parity. Character
factorization proves this without assuming quotient tuple validity. -/
theorem exists_odd_coordinate_and_unique_even_hole_of_two_hole_cube
    {k M : ℕ} [NeZero M] (hk : 2 ≤ k) (hcard : 2*M=2^k+2)
    (q : Fin k → ZMod (2*M))
    (hi : Function.Injective (fun S : Finset (Fin k) ↦ ∑ i ∈ S, q i)) :
    (∃ a, ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (q a)=1) ∧
    ∃ w : ZMod (2*M), ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) w=0 ∧
      (¬ ∃ S : Finset (Fin k), (∑ i ∈ S, q i)=w) ∧
      ∀ z : ZMod (2*M), ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) z=0 →
        (¬ ∃ S : Finset (Fin k), (∑ i ∈ S, q i)=z) → z=w := by
  classical
  letI : NeZero (2*M) := ⟨Nat.mul_ne_zero (by omega) (NeZero.ne M)⟩
  let π := ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
  let χ₂ : AddChar (ZMod 2) ℤ := AddChar.zmodChar 2 (by norm_num : (-1 : ℤ)^2=1)
  have hχ0 : χ₂ 0=1 := χ₂.map_zero_eq_one
  have hχ1 : χ₂ 1=-1 := by norm_num [χ₂,AddChar.zmodChar_apply,show (1 : ZMod 2).val=1 by rfl]
  let χ : AddChar (ZMod (2*M)) ℤ := χ₂.compAddMonoidHom π.toAddMonoidHom
  have hχ (z : ZMod (2*M)) : χ z=χ₂ (π z) := rfl
  have hbits (z : ZMod (2*M)) : π z=0 ∨ π z=1 := by
    have h : ∀ t : ZMod 2, t=0 ∨ t=1 := by decide
    exact h _
  have hχne : χ ≠ 0 := by
    intro heq
    have hv := congrArg (fun ψ : AddChar (ZMod (2*M)) ℤ ↦ ψ 1) heq
    change χ₂ (π 1)=1 at hv
    rw [map_one,hχ1] at hv
    omega
  have hall : (∑ z : ZMod (2*M), χ z)=0 := AddChar.sum_eq_zero_iff_ne_zero.mpr hχne
  let C : Finset (ZMod (2*M)) := Finset.univ.image (fun S : Finset (Fin k) ↦ ∑ i ∈ S, q i)
  have hCcard : C.card=2^k := by
    simp only [C,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_finset,Fintype.card_fin]
  have hcomplcard : Cᶜ.card=2 := by
    have hc := Finset.card_compl_add_card C
    simp only [ZMod.card,hcard,hCcard] at hc
    omega
  obtain ⟨x,y,hxy,hcomp⟩ := Finset.card_eq_two.mp hcomplcard
  have hsumC : (∑ z ∈ C, χ z)=∏ i, (1+χ (q i)) := by
    rw [Finset.sum_image (fun _ _ _ _ heq ↦ hi heq)]
    exact sum_addChar_all_subsets_eq_prod q χ
  have htotal : (∏ i, (1+χ (q i)))+χ x+χ y=0 := by
    have hs := Finset.sum_compl_add_sum C χ
    rw [hall,hcomp,Finset.sum_pair hxy,hsumC] at hs
    omega
  have hodd : ∃ a, π (q a)=1 := by
    by_contra hnot
    have heven (i : Fin k) : π (q i)=0 := (hbits (q i)).resolve_right (fun h ↦ hnot ⟨i,h⟩)
    have hprod : (∏ i, (1+χ (q i)))=(2 : ℤ)^k := by
      simp only [hχ,heven,hχ0,show (1 : ℤ)+1=2 by omega,Finset.prod_const,
        Finset.card_univ,Fintype.card_fin]
    rw [hprod] at htotal
    have hp : (4 : ℤ) ≤ 2^k := by
      exact_mod_cast (show (4 : ℕ) ≤ 2^k by
        simpa only [show (2 : ℕ)^2=4 by decide] using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hk)
    rcases hbits x with hx | hx <;> rcases hbits y with hy | hy <;>
      rw [hχ x,hχ y,hx,hy] at htotal <;> simp only [hχ0,hχ1] at htotal <;> omega
  obtain ⟨a,ha⟩ := hodd
  have hprod0 : (∏ i, (1+χ (q i)))=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    rw [hχ,ha,hχ1]
    omega
  rw [hprod0,zero_add] at htotal
  have hopposite : π x ≠ π y := by
    intro heq
    rw [hχ x,hχ y,heq] at htotal
    rcases hbits y with hy | hy <;> rw [hy] at htotal <;> simp only [hχ0,hχ1] at htotal <;> omega
  have hmissing (z : ZMod (2*M)) : (¬ ∃ S : Finset (Fin k), (∑ i ∈ S, q i)=z) ↔ z=x ∨ z=y := by
    have hmem : z ∈ C ↔ ∃ S : Finset (Fin k), (∑ i ∈ S, q i)=z := by simp [C]
    rw [← hmem,← Finset.mem_compl,hcomp,Finset.mem_insert,Finset.mem_singleton]
  refine ⟨⟨a,ha⟩,?_⟩
  rcases hbits x with hx | hx
  · refine ⟨x,hx,(hmissing x).mpr (Or.inl rfl),?_⟩
    intro z hz hmiss
    rcases (hmissing z).mp hmiss with hzx | hzy
    · exact hzx
    · exact False.elim (hopposite (hx.trans (hzy ▸ hz).symm))
  · have hy : π y=0 := (hbits y).resolve_right (fun hy ↦ hopposite (hx.trans hy.symm))
    refine ⟨y,hy,(hmissing y).mpr (Or.inr rfl),?_⟩
    intro z hz hmiss
    rcases (hmissing z).mp hmiss with hzx | hzy
    · have hh : (0 : ZMod 2)=1 := (hzx ▸ hz).symm.trans hx
      exact False.elim (zero_ne_one hh)
    · exact hzy

/-- An antipodal pair in an injective subset cube accounts for ALL
doubling collisions: removing either endpoint restores injectivity.
No ValidTuple premise is needed. -/
theorem doubling_injective_off_antipodal_of_subset_sum_injective
    {k M : ℕ} [NeZero M] (q : Fin k → ZMod (2*M))
    (hi : Function.Injective (fun S : Finset (Fin k) ↦ ∑ i ∈ S, q i))
    (a b : Fin k) (hab : a ≠ b) (hpair : q a=q b+(M : ZMod (2*M))) :
    ∀ i, i ≠ a → ∀ j, j ≠ a → 2 • q i=2 • q j → i=j := by
  classical
  have hqi : Function.Injective q := by
    intro i j heq
    exact Finset.singleton_injective (hi (by simpa only [Finset.sum_singleton] using heq))
  intro i hia j hja heq
  rcases eq_or_eq_add_half_of_castHom_eq (q i) (q j)
    (castHom_eq_of_two_nsmul_eq _ _ heq) with hij | hij
  · exact hqi hij
  · have hib : i ≠ b := by
      intro hib
      have hval : q a=q j := by
        rw [hpair,← hib,hij,add_assoc,half_add_half rfl,add_zero]
      exact hja (hqi hval).symm
    have hsum : (∑ c ∈ ({i,b} : Finset (Fin k)), q c)=
        ∑ c ∈ ({j,a} : Finset (Fin k)), q c := by
      rw [Finset.sum_pair hib,Finset.sum_pair hja,hij,hpair]
      abel
    have hsets := hi hsum
    have hamem : a ∈ ({i,b} : Finset (Fin k)) := hsets.symm ▸ (by simp : a ∈ ({j,a} : Finset (Fin k)))
    rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hamem : a=i ∨ a=b) with hai | hab'
    · exact False.elim (hia hai.symm)
    · exact False.elim (hab hab')

/-- For odd half order, deleting one ACTUAL odd coordinate makes all
remaining quotient doubles nonzero and injective. It removes the half
coordinate if present, otherwise the odd endpoint of the unique possible
antipodal pair, otherwise any odd coordinate. -/
theorem exists_odd_deletion_with_nonzero_injective_doubling_of_subset_cube
    {k M : ℕ} [NeZero M] (hM : Odd M) (q : Fin k → ZMod (2*M))
    (hi : Function.Injective (fun S : Finset (Fin k) ↦ ∑ i ∈ S, q i))
    (hodd : ∃ a, ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (q a)=1) :
    ∃ a, ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (q a)=1 ∧
      (∀ i, i ≠ a → 2 • q i ≠ 0) ∧
      ∀ i, i ≠ a → ∀ j, j ≠ a → 2 • q i=2 • q j → i=j := by
  classical
  let π := ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
  have hhalf : π (M : ZMod (2*M))=1 := by
    rw [map_natCast]
    obtain ⟨t,ht⟩ := hM
    rw [ht,Nat.cast_add,Nat.cast_mul]
    norm_num
    left
    decide
  have hqi : Function.Injective q := by
    intro i j heq
    exact Finset.singleton_injective (hi (by simpa only [Finset.sum_singleton] using heq))
  have hqn (i : Fin k) : q i ≠ 0 := by
    intro heq
    have hs : ({i} : Finset (Fin k))=∅ := hi (by simpa only [Finset.sum_singleton,Finset.sum_empty] using heq)
    have hc := congrArg Finset.card hs
    simp only [Finset.card_singleton,Finset.card_empty] at hc
    omega
  have hzero (i : Fin k) (hz : 2 • q i=0) : q i=(M : ZMod (2*M)) := by
    have hz' : 2 • q i=2 • (0 : ZMod (2*M)) := by simpa only [smul_zero] using hz
    rcases eq_or_eq_add_half_of_castHom_eq (q i) 0
      (castHom_eq_of_two_nsmul_eq _ _ hz') with h0 | hh
    · exact False.elim (hqn i h0)
    · simpa only [zero_add] using hh
  by_cases hhas : ∃ a, q a=(M : ZMod (2*M))
  · obtain ⟨a,ha⟩ := hhas
    refine ⟨a,by rw [ha]; exact hhalf,?_,?_⟩
    · intro i hia hz
      exact hia (hqi ((hzero i hz).trans ha.symm))
    · intro i _ j hja heq
      rcases eq_or_eq_add_half_of_castHom_eq (q i) (q j)
        (castHom_eq_of_two_nsmul_eq _ _ heq) with hij | hij
      · exact hqi hij
      · have hsum : (∑ b ∈ ({j,a} : Finset (Fin k)), q b)=q i := by
          rw [Finset.sum_pair hja,ha]
          exact hij.symm
        have hsets : ({j,a} : Finset (Fin k))={i} := hi (by simpa only [Finset.sum_singleton] using hsum)
        have hc := congrArg Finset.card hsets
        simp only [Finset.card_pair hja,Finset.card_singleton] at hc
        omega
  · have hnz (i : Fin k) : 2 • q i ≠ 0 := fun hz ↦ hhas ⟨i,hzero i hz⟩
    by_cases hcol : ∃ a b, a ≠ b ∧ 2 • q a=2 • q b
    · obtain ⟨a,b,hab,hdouble⟩ := hcol
      have hpair : q a=q b+(M : ZMod (2*M)) :=
        (eq_or_eq_add_half_of_castHom_eq (q a) (q b)
          (castHom_eq_of_two_nsmul_eq _ _ hdouble)).resolve_left (fun h ↦ hab (hqi h))
      have hpar : π (q a)=π (q b)+1 := by rw [hpair,map_add,hhalf]
      have hcases : π (q a)=0 ∨ π (q a)=1 := by
        have h : ∀ t : ZMod 2, t=0 ∨ t=1 := by decide
        exact h _
      rcases hcases with ha0 | ha1
      · have hb1 : π (q b)=1 := by
          have h : ∀ t : ZMod 2, t=0 ∨ t=1 := by decide
          rcases h (π (q b)) with hb0 | hb1
          · rw [ha0,hb0,zero_add] at hpar
            exact False.elim (zero_ne_one hpar)
          · exact hb1
        have hpair' : q b=q a+(M : ZMod (2*M)) := by
          rw [hpair,add_assoc,half_add_half rfl,add_zero]
        exact ⟨b,hb1,fun i _ ↦ hnz i,
          doubling_injective_off_antipodal_of_subset_sum_injective q hi b a hab.symm hpair'⟩
      · exact ⟨a,ha1,fun i _ ↦ hnz i,
          doubling_injective_off_antipodal_of_subset_sum_injective q hi a b hab hpair⟩
    · obtain ⟨a,ha⟩ := hodd
      exact ⟨a,ha,fun i _ ↦ hnz i,fun i _ j _ heq ↦ by
        by_contra hne
        exact hcol ⟨i,j,hne,heq⟩⟩

/-- With odd half order and the actual represented-double constraint,
deleting one odd coordinate from a two-hole cube leaves ONE complete
actual quotient chain. This is cube geometry, not G1 tuple descent. -/
theorem exists_odd_deletion_chain_of_two_hole_subset_cube
    {k M : ℕ} [NeZero M] (hk : 1 ≤ k) (hM : Odd M)
    (hcard : 2*M=2^(k+1)+2) (q : Fin (k+1) → ZMod (2*M))
    (hi : Function.Injective (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i))
    (hrep : ∀ i, (∃ S : Finset (Fin (k+1)), (∑ j ∈ S, q j)=2 • q i) →
      2 • q i=0 ∨ ∃ j, q j=2 • q i) :
    ∃ a, ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (q a)=1 ∧
      ∃ E : Equiv.Perm (Fin k), ∃ x : ZMod (2*M),
        ∀ i, q (a.succAbove (E i))=2^i.val • x := by
  classical
  obtain ⟨hodd,w,hwpar,hwmiss,hunique⟩ :=
    exists_odd_coordinate_and_unique_even_hole_of_two_hole_cube (by omega) hcard q hi
  obtain ⟨a,ha,hnz,hdinj⟩ :=
    exists_odd_deletion_with_nonzero_injective_doubling_of_subset_cube hM q hi hodd
  let q' : Fin k → ZMod (2*M) := fun i ↦ q (a.succAbove i)
  have hqi : Function.Injective (fun S : Finset (Fin k) ↦ ∑ i ∈ S, q' i) := by
    intro S T hsum
    apply Finset.image_injective (Fin.succAbove_right_injective (p := a))
    apply hi
    change (∑ i ∈ S.image a.succAbove, q i)=∑ i ∈ T.image a.succAbove, q i
    rw [Finset.sum_image (fun _ _ _ _ heq ↦ Fin.succAbove_right_injective (p := a) heq),
      Finset.sum_image (fun _ _ _ _ heq ↦ Fin.succAbove_right_injective (p := a) heq)]
    exact hsum
  have hinj : Function.Injective (fun i ↦ 2 • q' i) := by
    intro i j heq
    apply Fin.succAbove_right_injective
    exact hdinj _ (Fin.succAbove_ne _ _) _ (Fin.succAbove_ne _ _) heq
  let π := ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
  have hclosed (i : Fin k) (hiw : 2 • q' i ≠ w) : ∃ j, q' j=2 • q' i := by
    have hpar : π (2 • q' i)=0 := by
      rw [two_nsmul,map_add]
      have h : ∀ z : ZMod 2, z+z=0 := by decide
      exact h _
    have hrepresented : ∃ S : Finset (Fin (k+1)), (∑ j ∈ S, q j)=2 • q' i := by
      by_contra hnot
      exact hiw (hunique _ hpar hnot)
    rcases hrep (a.succAbove i) hrepresented with hz | ⟨j,hj⟩
    · exact False.elim (hnz _ (Fin.succAbove_ne _ _) hz)
    · have hja : j ≠ a := by
        intro heq
        have hp := congrArg π hj
        rw [heq,ha,hpar] at hp
        exact one_ne_zero hp
      obtain ⟨j',hj'⟩ := Fin.exists_succAbove_eq hja
      exact ⟨j',by simpa only [q',hj'] using hj⟩
  have hone : ∃ b : Fin k, ∀ i, i ≠ b → ∃ j, q' j=2 • q' i := by
    by_cases hex : ∃ b : Fin k, 2 • q' b=w
    · obtain ⟨b,hb⟩ := hex
      exact ⟨b,fun i hib ↦ hclosed i (fun heq ↦ hib (hinj (heq.trans hb.symm)))⟩
    · exact ⟨⟨0,by omega⟩,fun i _ ↦ hclosed i (fun heq ↦ hex ⟨i,heq⟩)⟩
  obtain ⟨b,hb⟩ := hone
  obtain ⟨P,hP⟩ := exists_almost_doubling_perm_of_one_escape q' b 0
    (fun i _ j _ heq ↦ hinj heq) (by simpa only [add_zero] using hb)
  obtain ⟨E,x,hchain⟩ := exists_perm_chain_of_injective_subset_sums_almost_doubling q' hqi P b
    (by simpa only [add_zero] using hP)
  exact ⟨a,ha,E,x,hchain⟩

/-- For ANY actual full-cover fibre with two quotient holes and odd
half index, one actual outside deletion exposes a complete retained
quotient chain. No SI or cycle hypothesis is used in this extraction. -/
theorem exists_odd_outside_deletion_chain_of_two_hole_actual_fibre_cover
    {m k D M : ℕ} [NeZero D] [NeZero M] (hm : 0 < m) (hk : 1 ≤ k) (hD : Odd D)
    (hcard : 2*D=2^(k+1)+2)
    (g : Fin (m+(k+1)) → ZMod ((2*D)*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i, g (Fin.castAdd (k+1) i)=zmodScaleHom (2*D) M (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z) :
    ∃ a : Fin (k+1), ∃ E : Equiv.Perm (Fin k), ∃ x : ZMod (2*D), ∀ i,
      ZMod.castHom (dvd_mul_right (2*D) M) (ZMod (2*D))
        (g (Fin.natAdd m (a.succAbove (E i))))=2^i.val • x := by
  letI : NeZero ((2*D)*M) := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (NeZero.ne D)) (NeZero.ne M)⟩
  obtain ⟨a,_,E,x,hchain⟩ := exists_odd_deletion_chain_of_two_hole_subset_cube hk hD hcard _
    (quotient_subset_sum_injective_of_actual_fibre_cover hm g hg u hpref hcover)
    (quotient_double_eq_zero_or_entry_of_actual_fibre_cover hm g hg u hpref hcover)
  exact ⟨a,E,x,hchain⟩

/-- The retained chain transports through any injective cyclic subgroup
map, with all original outsider choices and lifts allowed. -/
theorem exists_outside_deletion_chain_of_two_hole_mapped_fibre_cover
    {m k D M : ℕ} [NeZero D] [NeZero M] (hm : 0 < m) (hk : 1 ≤ k) (hD : Odd D)
    (hcard : 2*D=2^(k+1)+2)
    (τ : ZMod M →+ ZMod ((2*D)*M)) (hτ : Function.Injective τ)
    (g : Fin (m+(k+1)) → ZMod ((2*D)*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i, g (Fin.castAdd (k+1) i)=τ (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z) :
    ∃ a : Fin (k+1), ∃ E : Equiv.Perm (Fin k), ∃ x : ZMod (2*D), ∀ i,
      ZMod.castHom (dvd_mul_right (2*D) M) (ZMod (2*D))
        (g (Fin.natAdd m (a.succAbove (E i))))=2^i.val • x := by
  letI : NeZero ((2*D)*M) := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (NeZero.ne D)) (NeZero.ne M)⟩
  obtain ⟨β,hβ,hfactor⟩ := exists_bijective_scale_factor_of_injective_cyclic_hom τ hτ
  apply exists_odd_outside_deletion_chain_of_two_hole_actual_fibre_cover hm hk hD hcard g hg
    (fun i ↦ β (u i)) (by intro i; rw [hfactor]; exact hpref i)
  intro z
  obtain ⟨w,hw⟩ := hβ.2 z
  obtain ⟨s,hs,hvalue⟩ := hcover w
  refine ⟨s,hs,?_⟩
  rw [← hw,← hvalue,map_multiset_sum,Multiset.map_map]
  rfl

/-- Two-hole capacity beside an actual cycle forces the retained-chain
size bound after ONE outside deletion, not a logarithmic hypothesis. -/
theorem two_pow_pred_outside_le_length_pred_of_valid_two_hole_mapped_cycle
    {m k D : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k) [NeZero (2^m-1)] [NeZero D] (hD : Odd D)
    (hcard : 2*D=2^(k+1)+2)
    (τ : ZMod (2^m-1) →+ ZMod ((2*D)*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+(k+1)) → ZMod ((2*D)*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd (k+1) i)=τ ((2^i.val : ℕ) : ZMod (2^m-1))) :
    2^k ≤ m+k := by
  classical
  letI : NeZero ((2*D)*(2^m-1)) := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (NeZero.ne D)) (NeZero.ne _)⟩
  obtain ⟨a,E,x,hchain⟩ := exists_outside_deletion_chain_of_two_hole_mapped_fibre_cover
    (by omega) hk hD hcard τ hτ g hg (fun i ↦ ((2^i.val : ℕ) : ZMod (2^m-1))) hpref
    (exists_power_multiset_sum_at_mersenne hm)
  let f : Fin (m+k) ↪ Fin (m+(k+1)) := finSumFinEquiv.symm.toEmbedding.trans
    (((Function.Embedding.refl (Fin m)).sumMap (E.toEmbedding.trans a.succAboveEmb)).trans
      finSumFinEquiv.toEmbedding)
  have hleft (i : Fin m) : f (Fin.castAdd k i)=Fin.castAdd (k+1) i := by simp [f]
  have hright (i : Fin k) : f (Fin.natAdd m i)=Fin.natAdd m (a.succAbove (E i)) := by simp [f]
  apply two_pow_outside_le_length_of_valid_mapped_cycle_quotient_chain hm τ hτ
    (fun i ↦ g (f i)) (validTuple_embedding f g hg)
    (by intro i; rw [hleft,hpref]) (Equiv.refl _) x
  intro i
  simpa only [Equiv.refl_apply,hright] using hchain i

/-- Two-hole capacity for an arbitrary ACTUAL doubling cycle forces
the retained-chain bound. Its subgroup map and ordering are extracted. -/
theorem two_pow_outside_pred_le_length_pred_of_valid_two_hole_doubling_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hN : N=(2^(k+1)+2)*(2^m-1))
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (Fin.castAdd (k+1) (R i))=2 • g (Fin.castAdd (k+1) i)) :
    2^k ≤ m+k := by
  classical
  subst N
  have hpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  letI : NeZero (2^m-1) := ⟨hpos.ne'⟩
  let u : Fin m → ZMod ((2^(k+1)+2)*(2^m-1)) := fun i ↦ g (Fin.castAdd (k+1) i)
  have hu : ValidTuple u := validTuple_embedding ⟨Fin.castAdd (k+1),Fin.castAdd_injective m (k+1)⟩ g hg
  obtain ⟨a,e,he⟩ := exists_doubling_orbit_equiv_of_valid_zmod (by omega) u hu R hd
  have ho := addOrderOf_eq_mersenne_of_valid_doubling hm u hu R hd a
  obtain ⟨τ,hτ,hτone⟩ := exists_cyclic_subgroup_hom_of_addOrderOf (u a) ho
  have hτnat (r : ℕ) : τ (r : ZMod (2^m-1))=r • u a := by
    have hr : (r : ZMod (2^m-1))=r • (1 : ZMod (2^m-1)) := by simp
    rw [hr,map_nsmul,hτone]
  let F : Equiv.Perm (Fin (m+(k+1))) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin (k+1)))).trans finSumFinEquiv)
  have hleft (i : Fin m) : F (Fin.castAdd (k+1) i)=Fin.castAdd (k+1) (e i) := by simp [F]
  have hD : Odd (2^k+1) := by
    obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [hr,pow_succ']
    exact ⟨2^r,rfl⟩
  letI : NeZero (2^k+1) := ⟨by positivity⟩
  have hsize := two_pow_pred_outside_le_length_pred_of_valid_two_hole_mapped_cycle
    (m := m) (k := k) (D := 2^k+1) hm hk hD
  have hindex : 2*(2^k+1)=2^(k+1)+2 := by rw [pow_succ']; ring
  rw [hindex] at hsize
  apply hsize rfl τ hτ (fun i ↦ g (F i)) (validTuple_embedding F.toEmbedding g hg)
  intro i
  rw [hleft,hτnat]
  exact he i

/-- The almost-half cycle class of size m>=3 satisfies the STRONGER
binary bound. The apparent first-even endpoint is excluded by the
two-hole retained-chain obstruction; the valid m=2 endpoint is preserved. -/
theorem binary_lower_bound_of_valid_almost_half_affine_doubling_cycle
    {m k N : ℕ} [NeZero N] (hm : 3 ≤ m) (hk : k=m+1)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    2^(m+k) ≤ N := by
  by_contra hnot
  have heq := modulus_eq_binary_sub_two_of_valid_almost_half_cycle (by omega) hk (by omega) g hg E b R hd
  subst k
  have hQ : (2^m-1)+1=2^m := Nat.sub_add_cancel Nat.one_le_two_pow
  have hP : 2^(m+(m+1))=2^m*(2*2^m) := by rw [pow_add,pow_succ']
  have hprod : (2^(m+1)+2)*(2^m-1)+2=2^(m+(m+1)) := by rw [pow_succ']; nlinarith
  have hscale : N=(2^(m+1)+2)*(2^m-1) := by omega
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  have hpow := two_pow_outside_pred_le_length_pred_of_valid_two_hole_doubling_cycle
    (by omega) (by omega) hscale _ hv R
    (by intro i; rw [hd]; simp only [two_nsmul]; abel)
  have hstrict (r : ℕ) (hr : 3 ≤ r) : 2*r < 2^r := by
    induction r, hr using Nat.le_induction with
    | base => norm_num
    | succ r hr ih => rw [pow_succ']; omega
  have hstrict' := hstrict m hm
  omega

end MinModulus
