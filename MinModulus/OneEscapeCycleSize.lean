import MinModulus.DyadicCycleLift

/-!
# Extract the useful cycle-size bound from one-escape closure

Validity in a group with at most one nonzero involution allows at most
one unordered equal-double pair, without any closure premise. Protecting
an actual cycle, discard one OUTSIDE coordinate to restore injectivity.
All outside coordinates except this deletion and the escape have distinct
outside doubling targets. Splitting them beside the zero-sum cycle forces
k-2<m, hence k<=m+1. No size or valuation hypothesis is assumed.

Consequently EVERY nontrivial actual affine cycle in a cyclic one-escape
tuple yields the full global and exact-stratum bounds and excludes G3.
The arbitrary-depth quotient cycle consumers likewise no longer need a
half-size premise. General cycle existence is not proved: the remaining
one-escape exceptional case must be acyclic (apart from small dimensions).
The unrestricted three global gates remain open.
-/

namespace MinModulus
open Finset

/-- Validity permits only one unordered equal-double pair, without any
closure assumption on the coordinate set. -/
theorem equal_double_collision_mem_pair_of_valid
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    {h : G} (hh : h+h=0)
    (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    {a b c d : Fin n} (hab : a ≠ b) (hab2 : 2 • g a=2 • g b)
    (hcd : c ≠ d) (hcd2 : 2 • g c=2 • g d) : c=a ∨ c=b := by
  have hpair : ∀ {u v : Fin n}, u ≠ v → 2 • g u=2 • g v → g u-g v=h := by
    intro u v huv heq
    have hzero : (g u-g v)+(g u-g v)=0 := by
      simp only [two_nsmul] at heq
      rw [show (g u-g v)+(g u-g v)=(g u+g u)-(g v+g v) by abel,heq,sub_self]
    rcases hinv _ hzero with hz | hz
    · exact False.elim (huv (validTuple_injective g hg (sub_eq_zero.mp hz)))
    · exact hz
  have hne : h ≠ 0 := by
    rw [← hpair hab hab2]
    exact sub_ne_zero.mpr ((validTuple_injective g hg).ne hab)
  let w : Fin n → ℤ := fun i ↦ (if i=c then 1 else 0)-(if i=d then 1 else 0)
  have hw : Witness g h w := by
    refine ⟨?_,?_,?_,?_⟩
    · intro hw
      have := congrFun hw c
      simp [w,hcd] at this
    · intro i; simp only [w]; split_ifs <;> norm_num
    · simp [w,Finset.sum_sub_distrib]
    · simp only [w,sub_smul,ite_smul,one_smul,zero_smul]
      simpa [Finset.sum_sub_distrib] using hpair hcd hcd2
  have ha := common_touched_of_pair_difference g hg hh hne (hpair hab.symm hab2.symm) w hw
  have hb := common_touched_of_pair_difference g hg hh hne (hpair hab hab2) w hw
  have hacd : a=c ∨ a=d := by
    by_contra hc
    push Not at hc
    exact ha (by simp [w,hc.1,hc.2])
  have hbcd : b=c ∨ b=d := by
    by_contra hc
    push Not at hc
    exact hb (by simp [w,hc.1,hc.2])
  rcases hacd with hac | had
  · exact Or.inl hac.symm
  rcases hbcd with hbc | hbd
  · exact Or.inr hbc.symm
  exact False.elim (hab (had.trans hbd.symm))

/-- One coordinate outside any protected injective-doubling subset can
be discarded to make doubling injective on all remaining coordinates. -/
theorem exists_doubling_injective_compl_outside_protected_set
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (C : Finset (Fin n)) (hC : Set.InjOn (fun i ↦ 2 • g i) C)
    (hproper : ∃ j, j ∉ C) :
    ∃ j, j ∉ C ∧ ∀ i, i ≠ j → ∀ l, l ≠ j → 2 • g i=2 • g l → i=l := by
  classical
  by_cases hi : Function.Injective (fun i ↦ 2 • g i)
  · obtain ⟨j,hj⟩ := hproper
    exact ⟨j,hj,fun i _ l _ heq ↦ hi heq⟩
  obtain ⟨u,v,heq,hne⟩ : ∃ u v, 2 • g u=2 • g v ∧ u ≠ v := by
    simpa [Function.Injective] using hi
  have aux : ∀ u v : Fin n, u ∉ C → u ≠ v → 2 • g u=2 • g v →
      ∃ j, j ∉ C ∧ ∀ i, i ≠ j → ∀ l, l ≠ j → 2 • g i=2 • g l → i=l := by
    intro u v hu huv huv2
    refine ⟨u,hu,?_⟩
    intro i hi l hl hil
    by_contra hne
    have hic := equal_double_collision_mem_pair_of_valid g hg hh hinv huv huv2 hne hil
    have hlc := equal_double_collision_mem_pair_of_valid g hg hh hinv huv huv2 (Ne.symm hne) hil.symm
    exact hne ((hic.resolve_left hi).trans (hlc.resolve_left hl).symm)
  by_cases hu : u ∈ C
  · exact aux v u (fun hv ↦ hne (hC hu hv heq)) hne.symm heq.symm
  · exact aux u v hu hne heq

/-- Any actual cycle in a valid one-escape tuple forces the half-sized
cutoff. At most two outside arrows are lost: the escape and the unique
doubling collision. All other targets split simultaneously. -/
theorem outside_le_cycle_add_one_of_valid_one_escape_cycle
    {m k : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (a : Fin (m+k)) (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i)
    (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (Fin.castAdd k (R i))=2 • g (Fin.castAdd k i)) : k ≤ m+1 := by
  classical
  by_cases hk : 0 < k
  · let C : Finset (Fin (m+k)) := Finset.univ.image (Fin.castAdd k)
    have hC : Set.InjOn (fun i ↦ 2 • g i) C := by
      intro i hi j hj heq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hj
      have he := validTuple_injective g hg ((hcycle i).trans (heq.trans (hcycle j).symm))
      exact congrArg (Fin.castAdd k) (R.injective (Fin.castAdd_injective m k he))
    have hproper : ∃ j, j ∉ C := by
      refine ⟨Fin.natAdd m (⟨0,hk⟩ : Fin k),?_⟩
      intro hj
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hj
      have hv := congrArg Fin.val hi
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    obtain ⟨j,hj,hinj⟩ := exists_doubling_injective_compl_outside_protected_set g hg hh hinv C hC hproper
    have hjval : m ≤ j.val := by
      by_contra hnot
      apply hj
      exact Finset.mem_image.mpr ⟨⟨j.val,by omega⟩,Finset.mem_univ _,Fin.ext rfl⟩
    let j' : Fin k := ⟨j.val-m,by omega⟩
    have hj' : Fin.natAdd m j'=j := Fin.ext (by simp only [j',Fin.val_natAdd]; omega)
    let a' : Fin k := if ha : m ≤ a.val then ⟨a.val-m,by omega⟩ else j'
    let S : Finset (Fin k) := (Finset.univ.erase j').erase a'
    have hS (i : Fin k) (hi : i ∈ S) : Fin.natAdd m i ≠ a ∧ Fin.natAdd m i ≠ j := by
      have hia : i ≠ a' := (Finset.mem_erase.mp hi).1
      have hij : i ≠ j' := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      constructor
      · intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_natAdd] at hv
        apply hia
        apply Fin.ext
        simp only [a',dif_pos (by omega : m ≤ a.val),Fin.val_mk]
        omega
      · intro heq
        apply hij
        apply Fin.ext
        have hv := congrArg Fin.val (heq.trans hj'.symm)
        simp only [Fin.val_natAdd] at hv
        omega
    have htarget : ∀ i ∈ S, ∃ l : Fin k, g (Fin.natAdd m l)=2 • g (Fin.natAdd m i) := by
      intro i hi
      obtain ⟨l,hl⟩ := hclosed _ (hS i hi).1
      have hlval : m ≤ l.val := by
        by_contra hnot
        let c : Fin m := ⟨l.val,by omega⟩
        have hc : Fin.castAdd k c=l := Fin.ext rfl
        have hpred : Fin.castAdd k (R.symm c) ≠ j := by
          intro heq
          apply hj
          exact heq ▸ Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
        have heq : 2 • g (Fin.natAdd m i)=2 • g (Fin.castAdd k (R.symm c)) := by
          rw [← hl,← hc,← hcycle,R.apply_symm_apply]
        have he := hinj _ (hS i hi).2 _ hpred heq
        have hv := congrArg Fin.val he
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      exact ⟨⟨l.val-m,by omega⟩,by convert hl using 1; congr 1; apply Fin.ext; simp; omega⟩
    let f : Fin k → Fin k := fun i ↦ if hi : i ∈ S then Classical.choose (htarget i hi) else i
    have hf : ∀ i ∈ S, g (Fin.natAdd m (f i))=2 • g (Fin.natAdd m i) := by
      intro i hi
      simpa only [f,dif_pos hi] using Classical.choose_spec (htarget i hi)
    have hfinj : Set.InjOn f S := by
      intro i hi l hl heq
      have he := hinj _ (hS i hi).2 _ (hS l hl).2
        ((hf i hi).symm.trans ((congrArg (fun t ↦ g (Fin.natAdd m t)) heq).trans (hf l hl)))
      apply Fin.ext
      have hv := congrArg Fin.val he
      simp only [Fin.val_natAdd] at hv
      omega
    have hzero : (∑ i : Fin m, g (Fin.castAdd k i))=0 :=
      sum_eq_zero_of_doubling_invariant R _ hcycle Finset.univ (by simp)
    have hlt := doubling_targets_card_lt_fibre_of_valid_zero_sum_fibre hm g hg hzero S f hfinj hf
    have hcard : k ≤ S.card+2 := by
      by_cases ha : a' ∈ Finset.univ.erase j'
      · have h2 := Finset.card_erase_add_one ha
        simp only [Finset.card_erase_of_mem (Finset.mem_univ j'),Finset.card_univ,Fintype.card_fin] at h2
        change k ≤ ((Finset.univ.erase j').erase a').card+2
        omega
      · simp only [S,Finset.erase_eq_of_notMem ha,Finset.card_erase_of_mem (Finset.mem_univ j'),Finset.card_univ,Fintype.card_fin]
        omega
    omega
  · omega

/-- Affine reindexing and cyclic two-torsion instantiate the extracted
cutoff at every cyclic modulus, without a unit or valuation restriction. -/
theorem outside_le_cycle_add_one_of_valid_one_escape_affine_cycle
    {m k N : ℕ} [NeZero N] (hm : 0 < m)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (a : Fin (m+k)) (b : ZMod N)
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    k ≤ m+1 := by
  let u : Fin (m+k) → ZMod N := fun i ↦ g (E i)+b
  have hu : ValidTuple u := by
    simpa only [u,sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  have hc : ∀ i, i ≠ E.symm a → ∃ j, u j=2 • u i := by
    intro i hi
    obtain ⟨j,hj⟩ := hclosed (E i) (by intro heq; exact hi (E.injective (heq.trans (E.apply_symm_apply a).symm)))
    refine ⟨E.symm j,?_⟩
    simp only [u,E.apply_symm_apply,hj,two_nsmul]
    abel
  have hd : ∀ i, u (Fin.castAdd k (R i))=2 • u (Fin.castAdd k i) := by
    intro i
    simp only [u,hcycle,two_nsmul]
    abel
  rcases Nat.even_or_odd N with hN | hN
  · obtain ⟨M,hM⟩ := hN
    have hNM : N=2*M := by omega
    exact outside_le_cycle_add_one_of_valid_one_escape_cycle hm u hu (half_add_half hNM)
      (fun x hx ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hNM x hx) (E.symm a) hc R hd
  · apply outside_le_cycle_add_one_of_valid_one_escape_cycle hm u hu (h := 0) (by simp) ?_ (E.symm a) hc R hd
    intro x hx
    left
    apply add_self_injective_zmod hN
    simpa using hx

/-- Full global bound from ANY nontrivial actual cycle and one-escape
closure. The half-size requirement is now extracted, not assumed. -/
theorem global_lower_bound_of_valid_one_escape_affine_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (a : Fin (m+k)) (b : ZMod N)
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    globalBound (m+k) ≤ N :=
  global_lower_bound_of_valid_half_sized_affine_doubling_cycle hm
    (outside_le_cycle_add_one_of_valid_one_escape_affine_cycle (by omega) g hg a b hclosed E R hcycle)
    g hg E b R hcycle

/-- The same extracted cycle size gives EVERY exact-stratum bound,
including odd and higher-even strata, without a component-size premise. -/
theorem stratum_lower_bound_of_valid_one_escape_affine_cycle
    {m k s q : ℕ} (hm : 2 ≤ m) (hq : Odd q)
    (g : Fin (m+k) → ZMod (2^s*q)) (hg : ValidTuple g)
    (a : Fin (m+k)) (b : ZMod (2^s*q))
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    stratumBound (m+k) s ≤ 2^s*q := by
  letI : NeZero (2^s*q) := ⟨Nat.mul_ne_zero (by positivity) hq.pos.ne'⟩
  exact stratum_lower_bound_of_valid_half_sized_affine_doubling_cycle hm
    (outside_le_cycle_add_one_of_valid_one_escape_affine_cycle (by omega) g hg a b hclosed E R hcycle)
    hq g hg E b R hcycle

/-- Direct G3 exclusion for ALL one-escape tuples with a nontrivial
actual cycle. The outsider count is unrestricted and is bounded by validity. -/
theorem not_validTuple_exceptional_of_one_escape_affine_cycle
    {m k : ℕ} (hm : 2 ≤ m) (hnpow : 2^Nat.log 2 (m+k) ≠ m+k)
    (g : Fin (m+k) → ZMod (2*globalBound (m+k-1)))
    (a : Fin (m+k)) (b : ZMod (2*globalBound (m+k-1)))
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    ¬ ValidTuple g := by
  intro hg
  have hn3 : 3 ≤ m+k := by
    by_contra hnot
    have hn2 : m+k=2 := by omega
    norm_num [hn2] at hnpow
  have hB : 2 ≤ globalBound (m+k-1) := (nmin_eq (by omega : 2 ≤ m+k-1)).1.1
  letI : NeZero (2*globalBound (m+k-1)) := ⟨by omega⟩
  exact not_validTuple_exceptional_of_half_sized_affine_doubling_cycle hm
    (outside_le_cycle_add_one_of_valid_one_escape_affine_cycle (by omega) g hg a b hclosed E R hcycle)
    hnpow g E b R hcycle hg

/-- At ANY dyadic depth, a quotient cycle avoiding the exceptional image
now gives the full global bound with NO assumed half-size cutoff. -/
theorem global_lower_bound_of_one_escape_dyadic_quotient_cycle
    {r m k M : ℕ} [NeZero M] (hm : 2 ≤ m)
    (g : Fin (m+k) → ZMod (2^r*M)) (hg : ValidTuple g)
    (a : Fin (m+k)) (b : ZMod (2^r*M))
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b)
    (e : Fin m → Fin (m+k)) (R : Equiv.Perm (Fin m))
    (hinj : Function.Injective (fun i ↦
      ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e i))))
    (havoid : ∀ i, ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e i)) ≠
      ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g a))
    (hcycle : ∀ i, ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e (R i)))=
      2 • ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) (g (e i))+
      ZMod.castHom (dvd_mul_left M (2^r)) (ZMod M) b) :
    globalBound (m+k) ≤ 2^r*M := by
  letI : NeZero (2^r*M) := ⟨Nat.mul_ne_zero (by positivity) (NeZero.ne M)⟩
  obtain ⟨E,hE⟩ := exists_perm_actual_affine_cycle_of_one_escape_dyadic_quotient_cycle
    g a b hclosed e R hinj havoid hcycle
  exact global_lower_bound_of_valid_one_escape_affine_cycle hm g hg a b hclosed E R hE

end MinModulus
