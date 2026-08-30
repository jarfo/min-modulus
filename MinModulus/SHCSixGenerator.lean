/-
# Six-coordinate generator theorem: two-prime exceptional cases

This file closes the tight subgroup-cover cases at orders 75, 99, and 117.
In each case, the lower-dimensional SHC bounds force the six coordinates into
two exact annihilator-subgroup blocks.  Pigeonhole collisions among subset
sums of both blocks then produce more distinct combined sums than fit in their
intersection subgroup, contradicting dissociation.

Order 75 uses two choices from the order-25 block and three from the order-15
block to overfill an intersection of order 5.  Orders 99 and 117 use two
choices from each forced `4+2` block to overfill an intersection of order 3.
Thus generator-coordinate existence is proved at 30 of the 31 odd orders in
the six-coordinate strict window; only the three-prime order 105 remains.
-/
import MinModulus.SHCSixGeneratorReduction
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin

namespace MinModulus

open Finset

set_option maxRecDepth 100000

private def blockSetSix {r s : ℕ} (S : Finset (Fin r)) (T : Finset (Fin s)) :
    Finset (Fin (r + s)) :=
  S.map (Fin.castAddEmb s) ∪ T.map (Fin.natAddEmb r)

private theorem blockSetSix_injective {r s : ℕ} :
    Function.Injective
      (fun p : Finset (Fin r) × Finset (Fin s) ↦ blockSetSix p.1 p.2) := by
  rintro ⟨S, T⟩ ⟨S', T'⟩ heq
  apply Prod.ext
  · apply Finset.ext
    intro i
    have hi := Finset.ext_iff.mp heq (Fin.castAddEmb s i)
    have hmem (U : Finset (Fin r)) (V : Finset (Fin s)) :
        Fin.castAddEmb s i ∈ blockSetSix U V ↔ i ∈ U := by
      constructor
      · intro hz
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hz
          have hji' : j = i := (Fin.castAddEmb s).injective hji
          simpa [hji'] using hj
        · obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hz
          have hv := congrArg Fin.val hji
          simp only [Fin.natAddEmb, Fin.castAddEmb, Fin.castLEEmb,
            Function.Embedding.coeFn_mk, Fin.val_castLE, Fin.val_natAdd] at hv
          omega
      · intro hiU
        exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨i, hiU, rfl⟩)
    simpa only [hmem] using hi
  · apply Finset.ext
    intro i
    have hi := Finset.ext_iff.mp heq (Fin.natAddEmb r i)
    have hmem (U : Finset (Fin r)) (V : Finset (Fin s)) :
        Fin.natAddEmb r i ∈ blockSetSix U V ↔ i ∈ V := by
      constructor
      · intro hz
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hz
          have hv := congrArg Fin.val hji
          simp only [Fin.natAddEmb, Fin.castAddEmb, Fin.castLEEmb,
            Function.Embedding.coeFn_mk, Fin.val_castLE, Fin.val_natAdd] at hv
          omega
        · obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hz
          have hji' : j = i := (Fin.natAddEmb r).injective hji
          simpa [hji'] using hj
      · intro hiV
        exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨i, hiV, rfl⟩)
    simpa only [hmem] using hi

private theorem sum_blockSetSix {N r s : ℕ} [NeZero N]
    (a : Fin r → ZMod N) (b : Fin s → ZMod N)
    (S : Finset (Fin r)) (T : Finset (Fin s)) :
    (∑ j ∈ blockSetSix S T, Fin.append a b j) =
      (∑ i ∈ S, a i) + ∑ i ∈ T, b i := by
  rw [blockSetSix, Finset.sum_union]
  · rw [Finset.sum_map, Finset.sum_map]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      exact Fin.append_left a b i
    · apply Finset.sum_congr rfl
      intro i hi
      exact Fin.append_right a b i
  · rw [Finset.disjoint_left]
    intro z hzS hzT
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hzS
    obtain ⟨j, hj, heq⟩ := Finset.mem_map.mp hzT
    have hv := congrArg Fin.val heq
    simp only [Fin.natAddEmb, Fin.castAddEmb, Fin.castLEEmb, Function.Embedding.coeFn_mk,
      Fin.val_castLE, Fin.val_natAdd] at hv
    omega

private theorem exists_collision_choices {α β k : ℕ} [NeZero β]
    (f : Finset (Fin α) → ZMod β) (hcard : β * k < 2 ^ α) :
    ∃ pick : Fin (k + 1) ↪ Finset (Fin α), ∀ i j, f (pick i) = f (pick j) := by
  let s : Finset (Finset (Fin α)) := Finset.univ
  let t : Finset (ZMod β) := Finset.univ
  have hmaps : ∀ x ∈ s, f x ∈ t := by simp [t]
  have hs_card : s.card = 2 ^ α := by simp [s]
  have ht_card : t.card = β := by simp [t]
  obtain ⟨y, hy, hfiber⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := s) (t := t) (f := f) hmaps (by simpa [hs_card, ht_card] using hcard)
  let F := s.filter fun x ↦ f x = y
  have hk : k + 1 ≤ F.card := by
    change k + 1 ≤ #{x ∈ s | f x = y}
    omega
  obtain ⟨pick, hpick⟩ :=
    Function.Embedding.exists_of_card_le_finset
      (α := Fin (k + 1)) (s := F) (by simpa using hk)
  refine ⟨pick, ?_⟩
  intro i j
  have hiF : pick i ∈ F := hpick ⟨i, rfl⟩
  have hjF : pick j ∈ F := hpick ⟨j, rfl⟩
  exact (Finset.mem_filter.mp hiF).2.trans (Finset.mem_filter.mp hjF).2.symm

private theorem no_shc_of_block_collision
    {N r s u v D : ℕ} [NeZero N] [NeZero D] [NeZero u] [NeZero v]
    (hDN : D ∣ N)
    (a : Fin r → ZMod N) (b : Fin s → ZMod N)
    (pickA : Fin u ↪ Finset (Fin r)) (pickB : Fin v ↪ Finset (Fin s))
    (hA : ∀ i j, ZMod.castHom hDN (ZMod D)
        (∑ x ∈ pickA i, a x) = ZMod.castHom hDN (ZMod D)
        (∑ x ∈ pickA j, a x))
    (hB : ∀ i j, ZMod.castHom hDN (ZMod D)
        (∑ x ∈ pickB i, b x) = ZMod.castHom hDN (ZMod D)
        (∑ x ∈ pickB j, b x))
    (hover : Fintype.card
        ((ZMod.castHom hDN (ZMod D)).toAddMonoidHom.ker) < u * v) :
    ¬ SHC (Fin.append a b) := by
  intro hs
  let K : AddSubgroup (ZMod N) :=
    (ZMod.castHom hDN (ZMod D)).toAddMonoidHom.ker
  let base : ZMod N := (∑ x ∈ pickA 0, a x) + ∑ x ∈ pickB 0, b x
  let d : Fin u × Fin v → K := fun p ↦
    ⟨(∑ x ∈ pickA p.1, a x) + (∑ x ∈ pickB p.2, b x) - base, by
      change ZMod.castHom hDN (ZMod D) _ = 0
      rw [map_sub, map_add]
      change _ - ZMod.castHom hDN (ZMod D)
        ((∑ x ∈ pickA 0, a x) + ∑ x ∈ pickB 0, b x) = 0
      rw [map_add, hA p.1 0, hB p.2 0, sub_self]⟩
  have hd_inj : Function.Injective d := by
    rintro ⟨pi, pj⟩ ⟨qi, qj⟩ hpq
    have hsum :
        (∑ x ∈ pickA pi, a x) + (∑ x ∈ pickB pj, b x) =
        (∑ x ∈ pickA qi, a x) + (∑ x ∈ pickB qj, b x) := by
      have hv := congrArg Subtype.val hpq
      simpa [d] using hv
    have hsets : blockSetSix (pickA pi) (pickB pj) =
        blockSetSix (pickA qi) (pickB qj) := by
      apply hs.dis
      calc
        (∑ x ∈ blockSetSix (pickA pi) (pickB pj), Fin.append a b x) =
            (∑ x ∈ pickA pi, a x) + ∑ x ∈ pickB pj, b x :=
          sum_blockSetSix _ _ _ _
        _ = (∑ x ∈ pickA qi, a x) + ∑ x ∈ pickB qj, b x := hsum
        _ = (∑ x ∈ blockSetSix (pickA qi) (pickB qj), Fin.append a b x) :=
          (sum_blockSetSix _ _ _ _).symm
    have hpicks : (pickA pi, pickB pj) = (pickA qi, pickB qj) :=
      blockSetSix_injective hsets
    exact Prod.ext (pickA.injective (congrArg Prod.fst hpicks))
      (pickB.injective (congrArg Prod.snd hpicks))
  have hc := Fintype.card_le_of_injective d hd_inj
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  change u * v ≤ Fintype.card
    ((ZMod.castHom hDN (ZMod D)).toAddMonoidHom.ker) at hc
  omega

private noncomputable def tightIndex {N m : ℕ} [NeZero N]
    (h : Fin m → ZMod N) (H : AddSubgroup (ZMod N)) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i ↦ h i ∈ H

private theorem generator_of_tight_two_cover
    {N r s : ℕ} [NeZero N]
    (H J : AddSubgroup (ZMod N))
    (hcover : ∀ z : ZMod N, ¬ IsUnit z → z ∈ H ∨ z ∈ J)
    (hblock : ∀ (a : Fin r → H) (b : Fin s → J),
      ¬ SHC (Fin.append (fun i ↦ (a i : ZMod N)) (fun i ↦ (b i : ZMod N))))
    (h : Fin (r + s) → ZMod N) (hs : SHC h)
    (hA_lt : (tightIndex h H).card < r + 1)
    (hB_lt : (tightIndex h J).card < s + 1) :
    HasGeneratorCoordinate h := by
  classical
  by_contra hno
  have hnonunit : ∀ i, ¬ IsUnit (h i) := by
    intro i hi
    apply hno
    exact ⟨i, zmod_generator_of_isUnit _ hi⟩
  let A := tightIndex h H
  let B := tightIndex h J
  have hcover' : (Finset.univ : Finset (Fin (r + s))) ⊆ A ∪ B := by
    intro i hi
    rcases hcover (h i) (hnonunit i) with hiH | hiJ
    · exact Finset.mem_union_left B
        (by simp [A, tightIndex, hiH])
    · exact Finset.mem_union_right A
        (by simp [B, tightIndex, hiJ])
  have hcard : r + s ≤ A.card + B.card := by
    have hle := Finset.card_le_card hcover'
    have hu := Finset.card_union_le A B
    simpa using hle.trans hu
  have hA_bound : A.card ≤ r := by
    dsimp only [A]
    omega
  have hB_bound : B.card ≤ s := by
    dsimp only [B]
    omega
  have hAcard : A.card = r := by
    omega
  have hBcard : B.card = s := by omega
  have hUcard : (A ∪ B).card = r + s := by
    have hle := Finset.card_le_card hcover'
    have hle' : r + s ≤ (A ∪ B).card := by simpa using hle
    have hu : (A ∪ B).card ≤ r + s := by
      simpa using Finset.card_le_univ (A ∪ B)
    exact Nat.le_antisymm hu hle'
  have hIcard : (A ∩ B).card = 0 := by
    have hsum := Finset.card_union_add_card_inter A B
    omega
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.card_eq_zero.mp hIcard
  let eA : Fin r ↪ Fin (r + s) := (A.orderEmbOfFin hAcard).toEmbedding
  let eB : Fin s ↪ Fin (r + s) := (B.orderEmbOfFin hBcard).toEmbedding
  have hrange : Disjoint (Set.range eA) (Set.range eB) := by
    rw [Set.disjoint_left]
    intro i hiA hiB
    obtain ⟨j, rfl⟩ := hiA
    obtain ⟨k, hik⟩ := hiB
    have hjeA : eA j ∈ A := A.orderEmbOfFin_mem hAcard j
    have hkeB : eB k ∈ B := B.orderEmbOfFin_mem hBcard k
    apply (Finset.disjoint_left.mp hdisj hjeA)
    simpa [hik] using hkeB
  let e : Fin (r + s) ↪ Fin (r + s) := Fin.Embedding.append hrange
  have hebij : Function.Bijective e :=
    (Fintype.bijective_iff_injective_and_card e).mpr ⟨e.injective, by simp⟩
  let p : Fin (r + s) ≃ Fin (r + s) := Equiv.ofBijective e hebij
  let a : Fin r → H := fun i ↦
    ⟨h (eA i), by
      have hi := A.orderEmbOfFin_mem hAcard i
      change eA i ∈ Finset.univ.filter (fun j ↦ h j ∈ H) at hi
      exact (Finset.mem_filter.mp hi).2⟩
  let b : Fin s → J := fun i ↦
    ⟨h (eB i), by
      have hi := B.orderEmbOfFin_mem hBcard i
      change eB i ∈ Finset.univ.filter (fun j ↦ h j ∈ J) at hi
      exact (Finset.mem_filter.mp hi).2⟩
  have happend :
      Fin.append (fun i ↦ (a i : ZMod N)) (fun i ↦ (b i : ZMod N)) = h ∘ p := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [a, eA, p, e, Fin.Embedding.append]
    | right i => simp [b, eB, p, e, Fin.Embedding.append]
  apply hblock a b
  rw [happend]
  exact hs.reindex_equiv h p

private abbrev H75 : AddSubgroup (ZMod 75) := (nsmulAddMonoidHom 25).ker
private abbrev J75 : AddSubgroup (ZMod 75) := (nsmulAddMonoidHom 15).ker

private theorem cast_fifteen_eq_of_H75_of_cast_five_eq (x y : ZMod 75)
    (hx : x ∈ H75) (hy : y ∈ H75)
    (hxy : ZMod.castHom (show 5 ∣ 75 by norm_num) (ZMod 5) x =
      ZMod.castHom (show 5 ∣ 75 by norm_num) (ZMod 5) y) :
    ZMod.castHom (show 15 ∣ 75 by norm_num) (ZMod 15) x =
      ZMod.castHom (show 15 ∣ 75 by norm_num) (ZMod 15) y := by
  revert x y
  decide

private theorem cast_fifteen_eq_of_J75_of_cast_three_eq (x y : ZMod 75)
    (hx : x ∈ J75) (hy : y ∈ J75)
    (hxy : ZMod.castHom (show 3 ∣ 75 by norm_num) (ZMod 3) x =
      ZMod.castHom (show 3 ∣ 75 by norm_num) (ZMod 3) y) :
    ZMod.castHom (show 15 ∣ 75 by norm_num) (ZMod 15) x =
      ZMod.castHom (show 15 ∣ 75 by norm_num) (ZMod 15) y := by
  revert x y
  decide

private theorem no_shc_three_H75_three_J75
    (a : Fin 3 → H75) (b : Fin 3 → J75) :
    ¬ SHC (Fin.append (fun i ↦ (a i : ZMod 75)) (fun i ↦ (b i : ZMod 75))) := by
  let qa : Finset (Fin 3) → ZMod 5 := fun S ↦
    ZMod.castHom (show 5 ∣ 75 by norm_num) (ZMod 5) (∑ i ∈ S, (a i : ZMod 75))
  obtain ⟨pickA, hpickA⟩ :=
    exists_collision_choices (α := 3) (β := 5) (k := 1) qa (by norm_num)
  let qb : Finset (Fin 3) → ZMod 3 := fun S ↦
    ZMod.castHom (show 3 ∣ 75 by norm_num) (ZMod 3) (∑ i ∈ S, (b i : ZMod 75))
  obtain ⟨pickB, hpickB⟩ :=
    exists_collision_choices (α := 3) (β := 3) (k := 2) qb (by norm_num)
  apply no_shc_of_block_collision (N := 75) (D := 15) (by norm_num)
      (fun i ↦ (a i : ZMod 75)) (fun i ↦ (b i : ZMod 75)) pickA pickB
  · intro i j
    apply cast_fifteen_eq_of_H75_of_cast_five_eq
    · apply H75.sum_mem
      intro x hx
      exact (a x).2
    · apply H75.sum_mem
      intro x hx
      exact (a x).2
    · exact hpickA i j
  · intro i j
    apply cast_fifteen_eq_of_J75_of_cast_three_eq
    · apply J75.sum_mem
      intro x hx
      exact (b x).2
    · apply J75.sum_mem
      intro x hx
      exact (b x).2
    · exact hpickB i j
  · decide

theorem shc_hasGeneratorCoordinate_zmod_six_seventy_five
    (h : Fin 6 → ZMod 75) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  have hHcard : Fintype.card H75 = 25 := by decide
  have hJcard : Fintype.card J75 = 15 := by decide
  apply generator_of_tight_two_cover H75 J75
      (fun z hz ↦ by revert z; decide) no_shc_three_H75_three_J75 h hs
  · apply shc_index_card_lt_of_cyclic_lower_bound (k := 4) H75
      cyclicSHCOddLowerBound_four
    · rw [hHcard]
      norm_num
    · rw [hHcard]
      norm_num
    · exact hs
    · intro i hi
      simpa [tightIndex] using hi
  · apply shc_index_card_lt_of_cyclic_lower_bound (k := 4) J75
      cyclicSHCOddLowerBound_four
    · rw [hJcard]
      norm_num
    · rw [hJcard]
      norm_num
    · exact hs
    · intro i hi
      simpa [tightIndex] using hi

private abbrev H99 : AddSubgroup (ZMod 99) := (nsmulAddMonoidHom 33).ker
private abbrev J99 : AddSubgroup (ZMod 99) := (nsmulAddMonoidHom 9).ker

private theorem cast_thirty_three_eq_of_H99_of_cast_eleven_eq (x y : ZMod 99)
    (hx : x ∈ H99) (hy : y ∈ H99)
    (hxy : ZMod.castHom (show 11 ∣ 99 by norm_num) (ZMod 11) x =
      ZMod.castHom (show 11 ∣ 99 by norm_num) (ZMod 11) y) :
    ZMod.castHom (show 33 ∣ 99 by norm_num) (ZMod 33) x =
      ZMod.castHom (show 33 ∣ 99 by norm_num) (ZMod 33) y := by
  revert x y
  decide

private theorem cast_thirty_three_eq_of_J99_of_cast_three_eq (x y : ZMod 99)
    (hx : x ∈ J99) (hy : y ∈ J99)
    (hxy : ZMod.castHom (show 3 ∣ 99 by norm_num) (ZMod 3) x =
      ZMod.castHom (show 3 ∣ 99 by norm_num) (ZMod 3) y) :
    ZMod.castHom (show 33 ∣ 99 by norm_num) (ZMod 33) x =
      ZMod.castHom (show 33 ∣ 99 by norm_num) (ZMod 33) y := by
  revert x y
  decide

private theorem no_shc_four_H99_two_J99
    (a : Fin 4 → H99) (b : Fin 2 → J99) :
    ¬ SHC (Fin.append (fun i ↦ (a i : ZMod 99)) (fun i ↦ (b i : ZMod 99))) := by
  let qa : Finset (Fin 4) → ZMod 11 := fun S ↦
    ZMod.castHom (show 11 ∣ 99 by norm_num) (ZMod 11) (∑ i ∈ S, (a i : ZMod 99))
  obtain ⟨pickA, hpickA⟩ :=
    exists_collision_choices (α := 4) (β := 11) (k := 1) qa (by norm_num)
  let qb : Finset (Fin 2) → ZMod 3 := fun S ↦
    ZMod.castHom (show 3 ∣ 99 by norm_num) (ZMod 3) (∑ i ∈ S, (b i : ZMod 99))
  obtain ⟨pickB, hpickB⟩ :=
    exists_collision_choices (α := 2) (β := 3) (k := 1) qb (by norm_num)
  apply no_shc_of_block_collision (N := 99) (D := 33) (by norm_num)
      (fun i ↦ (a i : ZMod 99)) (fun i ↦ (b i : ZMod 99)) pickA pickB
  · intro i j
    apply cast_thirty_three_eq_of_H99_of_cast_eleven_eq
    · exact H99.sum_mem fun x hx ↦ (a x).2
    · exact H99.sum_mem fun x hx ↦ (a x).2
    · exact hpickA i j
  · intro i j
    apply cast_thirty_three_eq_of_J99_of_cast_three_eq
    · exact J99.sum_mem fun x hx ↦ (b x).2
    · exact J99.sum_mem fun x hx ↦ (b x).2
    · exact hpickB i j
  · decide

theorem shc_hasGeneratorCoordinate_zmod_six_ninety_nine
    (h : Fin 6 → ZMod 99) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  have hHcard : Fintype.card H99 = 33 := by decide
  have hJcard : Fintype.card J99 = 9 := by decide
  apply generator_of_tight_two_cover H99 J99
      (fun z hz ↦ by revert z; decide) no_shc_four_H99_two_J99 h hs
  · apply shc_index_card_lt_of_cyclic_lower_bound (k := 5) H99
      cyclicSHCOddLowerBound_five
    · rw [hHcard]
      norm_num
    · rw [hHcard]
      norm_num
    · exact hs
    · intro i hi
      simpa [tightIndex] using hi
  · apply shc_index_card_lt_of_cyclic_lower_bound (k := 3) J99
      cyclicSHCOddLowerBound_three
    · rw [hJcard]
      norm_num
    · rw [hJcard]
      norm_num
    · exact hs
    · intro i hi
      simpa [tightIndex] using hi

private abbrev H117 : AddSubgroup (ZMod 117) := (nsmulAddMonoidHom 39).ker
private abbrev J117 : AddSubgroup (ZMod 117) := (nsmulAddMonoidHom 9).ker

private theorem cast_thirty_nine_eq_of_H117_of_cast_thirteen_eq (x y : ZMod 117)
    (hx : x ∈ H117) (hy : y ∈ H117)
    (hxy : ZMod.castHom (show 13 ∣ 117 by norm_num) (ZMod 13) x =
      ZMod.castHom (show 13 ∣ 117 by norm_num) (ZMod 13) y) :
    ZMod.castHom (show 39 ∣ 117 by norm_num) (ZMod 39) x =
      ZMod.castHom (show 39 ∣ 117 by norm_num) (ZMod 39) y := by
  revert x y
  decide

private theorem cast_thirty_nine_eq_of_J117_of_cast_three_eq (x y : ZMod 117)
    (hx : x ∈ J117) (hy : y ∈ J117)
    (hxy : ZMod.castHom (show 3 ∣ 117 by norm_num) (ZMod 3) x =
      ZMod.castHom (show 3 ∣ 117 by norm_num) (ZMod 3) y) :
    ZMod.castHom (show 39 ∣ 117 by norm_num) (ZMod 39) x =
      ZMod.castHom (show 39 ∣ 117 by norm_num) (ZMod 39) y := by
  revert x y
  decide

private theorem no_shc_four_H117_two_J117
    (a : Fin 4 → H117) (b : Fin 2 → J117) :
    ¬ SHC (Fin.append (fun i ↦ (a i : ZMod 117)) (fun i ↦ (b i : ZMod 117))) := by
  let qa : Finset (Fin 4) → ZMod 13 := fun S ↦
    ZMod.castHom (show 13 ∣ 117 by norm_num) (ZMod 13)
      (∑ i ∈ S, (a i : ZMod 117))
  obtain ⟨pickA, hpickA⟩ :=
    exists_collision_choices (α := 4) (β := 13) (k := 1) qa (by norm_num)
  let qb : Finset (Fin 2) → ZMod 3 := fun S ↦
    ZMod.castHom (show 3 ∣ 117 by norm_num) (ZMod 3)
      (∑ i ∈ S, (b i : ZMod 117))
  obtain ⟨pickB, hpickB⟩ :=
    exists_collision_choices (α := 2) (β := 3) (k := 1) qb (by norm_num)
  apply no_shc_of_block_collision (N := 117) (D := 39) (by norm_num)
      (fun i ↦ (a i : ZMod 117)) (fun i ↦ (b i : ZMod 117)) pickA pickB
  · intro i j
    apply cast_thirty_nine_eq_of_H117_of_cast_thirteen_eq
    · exact H117.sum_mem fun x hx ↦ (a x).2
    · exact H117.sum_mem fun x hx ↦ (a x).2
    · exact hpickA i j
  · intro i j
    apply cast_thirty_nine_eq_of_J117_of_cast_three_eq
    · exact J117.sum_mem fun x hx ↦ (b x).2
    · exact J117.sum_mem fun x hx ↦ (b x).2
    · exact hpickB i j
  · decide

theorem shc_hasGeneratorCoordinate_zmod_six_one_hundred_seventeen
    (h : Fin 6 → ZMod 117) (hs : SHC h) : HasGeneratorCoordinate h := by
  classical
  have hHcard : Fintype.card H117 = 39 := by decide
  have hJcard : Fintype.card J117 = 9 := by decide
  apply generator_of_tight_two_cover H117 J117
      (fun z hz ↦ by revert z; decide) no_shc_four_H117_two_J117 h hs
  · apply shc_index_card_lt_of_cyclic_lower_bound (k := 5) H117
      cyclicSHCOddLowerBound_five
    · rw [hHcard]
      norm_num
    · rw [hHcard]
      norm_num
    · exact hs
    · intro i hi
      simpa [tightIndex] using hi
  · apply shc_index_card_lt_of_cyclic_lower_bound (k := 3) J117
      cyclicSHCOddLowerBound_three
    · rw [hJcard]
      norm_num
    · rw [hJcard]
      norm_num
    · exact hs
    · intro i hi
      simpa [tightIndex] using hi

/-- Every six-coordinate SHC family in the odd strict window has a generator
coordinate away from the sole remaining three-prime exception at order 105. -/
theorem shc_hasGeneratorCoordinate_zmod_six_of_odd_window_ne_one_hundred_five
    {N : ℕ} (hodd : Odd N) (hlower : 65 ≤ N) (hupper : N ≤ 125)
    (h105 : N ≠ 105) (h : Fin 6 → ZMod N) (hs : SHC h) :
    HasGeneratorCoordinate h := by
  by_cases h75 : N = 75
  · subst N
    exact shc_hasGeneratorCoordinate_zmod_six_seventy_five h hs
  by_cases h99 : N = 99
  · subst N
    exact shc_hasGeneratorCoordinate_zmod_six_ninety_nine h hs
  by_cases h117 : N = 117
  · subst N
    exact shc_hasGeneratorCoordinate_zmod_six_one_hundred_seventeen h hs
  exact shc_hasGeneratorCoordinate_zmod_six_of_odd_window_ne_exceptions
    hodd hlower hupper h75 h99 h105 h117 h hs

end MinModulus
