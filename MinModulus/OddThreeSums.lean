import MinModulus.ActualFibreSidon
import MinModulus.OneExtraMultisetRigidity

/-!
# Three-coin counting at odd order

Repeated triples form the union of n translates of the doubled coordinate
set. Sidon uniqueness makes each pair of translates intersect in at most
one point, giving at least binom(n+1,2) repeated sums. The binom(n,3)
squarefree sums are distinct and disjoint from these repeated sums.

No repeated triple can complete an (n-3)-coin sum to the all-ones total.
For n=6 this packs at least 21+41=62 residues; oddness gives N>=63.
The proof is uniform in the modulus and uses no finite certificates.
-/

namespace MinModulus
open Finset

/-- A union loses at most one element for each pair of intersecting members. -/
theorem sum_card_le_biUnion_card_add_choose_two
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (B : ι → Finset α)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (B i ∩ B j).card ≤ 1) :
    (∑ i ∈ s, (B i).card) ≤ (s.biUnion B).card + s.card.choose 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs := ih (by
      intro i hi j hj hij
      exact h i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)
    have hint : (B a ∩ s.biUnion B).card ≤ s.card := by
      rw [Finset.inter_biUnion]
      calc
        _ ≤ ∑ j ∈ s, (B a ∩ B j).card := Finset.card_biUnion_le
        _ ≤ ∑ _j ∈ s, 1 := by
          apply Finset.sum_le_sum
          intro j hj
          exact h a (mem_insert_self _ _) j (mem_insert_of_mem hj)
            (by intro he; exact ha (he ▸ hj))
        _ = s.card := by simp
    have hu := Finset.card_union_add_card_inter (B a) (s.biUnion B)
    rw [Finset.sum_insert ha, Finset.biUnion_insert, Finset.card_insert_of_notMem ha]
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    norm_num only [Nat.succ_eq_add_one] at *
    omega

/-- The repeated-coordinate three-coin sums. -/
noncomputable def repeatedThreeSums {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) : Finset (ZMod N) := by
  classical
  exact Finset.univ.biUnion (fun j ↦ Finset.univ.image (fun i ↦ 2 • g i + g j))

/-- A Sidon tuple at odd order has at least n(n+1)/2 repeated three-coin sums. -/
theorem choose_two_le_repeatedThreeSums_card
    {n N : ℕ} [NeZero N] (hN : Odd N) (g : Fin n → ZMod N)
    (hg : ValidTuple g) : (n+1).choose 2 ≤ (repeatedThreeSums g).card := by
  classical
  have hd : Function.Injective (fun x : ZMod N ↦ 2 • x) := by
    intro a b h
    apply ((ZMod.isUnit_iff_coprime 2 N).mpr hN.coprime_two_left).mul_left_cancel
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using h
  have hi := validTuple_injective g hg
  have hp (a b c d : Fin n) (he : g a+g b=g c+g d) :
      (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
    rcases pair_sum_eq_or_diagonal_of_validTuple g hg a b c d he with h | ⟨hab,hcd⟩
    · exact h
    · subst b; subst d
      have hac := hi (hd (by simpa only [two_nsmul] using he))
      exact Or.inl ⟨hac,hac⟩
  let B : Fin n → Finset (ZMod N) := fun j ↦ Finset.univ.image (fun i ↦ 2 • g i + g j)
  have hB (j : Fin n) : (B j).card=n := by
    dsimp [B]
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b h
      exact hi (hd (add_right_cancel h))
  have hint (j : Fin n) (_ : j ∈ (Finset.univ : Finset (Fin n)))
      (l : Fin n) (_ : l ∈ (Finset.univ : Finset (Fin n))) (hjl : j ≠ l) :
      (B j ∩ B l).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxj,hxl⟩ := Finset.mem_inter.mp hx
    obtain ⟨hyj,hyl⟩ := Finset.mem_inter.mp hy
    obtain ⟨a,_,hax⟩ := Finset.mem_image.mp hxj
    obtain ⟨b,_,hbx⟩ := Finset.mem_image.mp hxl
    obtain ⟨c,_,hcy⟩ := Finset.mem_image.mp hyj
    obtain ⟨d,_,hdy⟩ := Finset.mem_image.mp hyl
    have hab : a ≠ b := by
      intro he
      subst b
      exact hjl (hi (add_left_cancel (hax.trans hbx.symm)))
    have he : g a+g d=g b+g c := by
      apply hd
      simp only [nsmul_add]
      have hx := hax.trans hbx.symm
      have hy := hcy.trans hdy.symm
      linear_combination hx - hy
    rcases hp a d b c he with ⟨hab',_⟩ | ⟨hac,_⟩
    · exact (hab hab').elim
    · subst c
      exact hax.symm.trans hcy
  have hb := sum_card_le_biUnion_card_add_choose_two Finset.univ B hint
  simp only [hB, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hb
  have hn : (n+1).choose 2 = n.choose 2 + n := by
    simpa [Nat.choose_one_right, add_comm] using Nat.choose_succ_succ n 1
  have hc : 2 * n.choose 2 = n * (n-1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  change _ ≤ (Finset.univ.biUnion B).card
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_sub_one] at hc
    nlinarith

/-- Sums of three distinct coordinates. -/
noncomputable def squarefreeThreeSums {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) : Finset (ZMod N) := by
  classical
  exact ((Finset.univ : Finset (Fin n)).powersetCard 3).image (fun S ↦ ∑ i ∈ S, g i)

theorem squarefreeThreeSums_card
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) :
    (squarefreeThreeSums g).card = n.choose 3 := by
  classical
  dsimp [squarefreeThreeSums]
  rw [Finset.card_image_iff.mpr]
  · simp [Finset.card_powersetCard]
  · intro S hS T hT he
    apply Finset.val_injective
    exact multiset_eq_finset_of_validTuple_card_sum g hg T S.val
      (by change S.card=T.card; rw [(mem_powersetCard.mp hS).2, (mem_powersetCard.mp hT).2]) he

theorem repeatedThreeSums_disjoint_squarefree
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) :
    Disjoint (repeatedThreeSums g) (squarefreeThreeSums g) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hz hzs
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨i,_,hij⟩ := Finset.mem_image.mp hj
  obtain ⟨S,hS,hSz⟩ := Finset.mem_image.mp hzs
  have he : (i ::ₘ i ::ₘ ({j} : Multiset (Fin n)))=S.val := by
    apply multiset_eq_finset_of_validTuple_card_sum g hg S _
    · simpa using (Finset.mem_powersetCard.mp hS).2.symm
    · simpa only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
        Multiset.sum_singleton, two_nsmul, add_assoc] using hij.trans hSz.symm
  have hn := S.nodup
  rw [← he] at hn
  simp at hn

theorem repeatedThreeSums_subset_coinCover
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) :
    repeatedThreeSums g ⊆ actualFibreCoinCover g 3 := by
  classical
  intro z hz
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨i,_,hij⟩ := Finset.mem_image.mp hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i ::ₘ i ::ₘ ({j} : Multiset (Fin n)),
    by simp, by simpa only [Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
      Multiset.sum_singleton, two_nsmul, add_assoc] using hij⟩

/-- A uniform cubic lower bound for all valid tuples at odd cyclic order. -/
theorem choose_three_add_choose_two_le_three_coin_card
    {n N : ℕ} [NeZero N] (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g) :
    n.choose 3 + (n+1).choose 2 ≤ (actualFibreCoinCover g 3).card := by
  classical
  have hs : squarefreeThreeSums g ⊆ actualFibreCoinCover g 3 := by
    intro z hz
    obtain ⟨S,hS,hSz⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.val, (mem_powersetCard.mp hS).2, hSz⟩
  have h := Finset.card_le_card (Finset.union_subset
    (repeatedThreeSums_subset_coinCover g) hs)
  rw [Finset.card_union_of_disjoint (repeatedThreeSums_disjoint_squarefree g hg),
    squarefreeThreeSums_card g hg] at h
  have hd := choose_two_le_repeatedThreeSums_card hN g hg
  omega

/-- A repeated three-coin sum cannot complete any complementary coin sum
to the all-ones total. -/
theorem repeatedThreeSums_add_coinCover_ne_total
    {n N r : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hr : r+3=n) (a b : ZMod N) (ha : a ∈ repeatedThreeSums g)
    (hb : b ∈ actualFibreCoinCover g r) : a+b ≠ ∑ i, g i := by
  classical
  intro he
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨i,_,hij⟩ := Finset.mem_image.mp hj
  obtain ⟨s,hcard,hsum⟩ := (Finset.mem_filter.mp hb).2
  let t := i ::ₘ i ::ₘ j ::ₘ s
  have htcard : t.card=n := by simp [t,hcard]; omega
  have htsum : (t.map g).sum=∑ i, g i := by
    simp only [t,Multiset.map_cons,Multiset.sum_cons,hsum]
    rw [← he, ← hij, two_nsmul]
    abel
  have hc := multiset_count_eq_one_of_validTuple g hg t htcard htsum i
  simp only [t,Multiset.count_cons_self] at hc
  omega

/-- Repeated triples force a deficit in every complementary coin sumset. -/
theorem repeatedThreeSums_card_add_coinCover_card_le
    {n N r : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hr : r+3=n) :
    (repeatedThreeSums g).card+(actualFibreCoinCover g r).card ≤ N := by
  exact card_add_card_le_modulus_of_sum_ne _ _ (∑ i, g i)
    (fun a ha b hb ↦ repeatedThreeSums_add_coinCover_ne_total g hg hr a b ha hb)

/-- Dimension six of G2 follows from Sidon counting and complementary sums,
without a finite enumeration of moduli or tuples. -/
theorem odd_modulus_ge_sixty_three_of_valid_six
    {N : ℕ} (hN : Odd N) (g : Fin 6 → ZMod N) (hg : ValidTuple g) : 63 ≤ N := by
  haveI : NeZero N := ⟨hN.pos.ne'⟩
  have hD := choose_two_le_repeatedThreeSums_card hN g hg
  have hC := choose_three_add_choose_two_le_three_coin_card hN g hg
  have hP := repeatedThreeSums_card_add_coinCover_card_le g hg (by decide : 3+3=6)
  norm_num [Nat.choose] at hD hC
  obtain ⟨k,hk⟩ := hN
  omega

end MinModulus
