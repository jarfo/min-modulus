import MinModulus.FullSupportBinaryCore

namespace MinModulus
open Finset
open scoped Classical

/-- Full-support cores inject into the solutions of the doubled-sum
equation, even when doubling itself is not injective. -/
theorem full_support_core_card_le_doubling_fibre_card
    {n : ℕ} {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (b : G)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2) :
    ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=Finset.univ)).card ≤
      (Finset.univ.filter (fun z : G ↦ 2 • z=∑ i, (g i+b))).card := by
  classical
  let C := (tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=Finset.univ)
  let D := Finset.univ.filter (fun z : G ↦ 2 • z=∑ i, (g i+b))
  let f : C → D := fun uv ↦ ⟨∑ i ∈ uv.val.1, (g i+b),Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    two_nsmul_full_binary_core_sum_eq_total g b uv.val
      (Finset.mem_filter.mp uv.property).1 (Finset.mem_filter.mp uv.property).2⟩⟩
  have hf : Function.Injective f := by
    intro uv st he
    apply Subtype.ext
    exact full_support_binary_core_eq_of_equal_sum g b hcap uv.val st.val
      (Finset.mem_filter.mp uv.property).1 (Finset.mem_filter.mp st.property).1
      (Finset.mem_filter.mp uv.property).2 (Finset.mem_filter.mp st.property).2
      (congrArg Subtype.val he)
  have hc := Fintype.card_le_of_injective f hf
  simpa only [C,D,Fintype.card_coe] using hc

/-- A doubled-sum equation modulo any nonzero N has at most two solutions.
The quotient of twice the representative by N distinguishes its solutions. -/
theorem zmod_doubling_fibre_card_le_two
    {N : ℕ} [NeZero N] (t : ZMod N) :
    (Finset.univ.filter (fun z : ZMod N ↦ 2 • z=t)).card ≤ 2 := by
  classical
  have hN : 0 < N := NeZero.pos N
  let D := Finset.univ.filter (fun z : ZMod N ↦ 2 • z=t)
  have hmod (z : D) : (2*z.val.val)%N=t.val := by
    have he := congrArg ZMod.val (Finset.mem_filter.mp z.property).2
    simpa only [nsmul_eq_mul,ZMod.val_mul,ZMod.val_natCast,Nat.mod_mul_mod] using he
  let f : D → Fin 2 := fun z ↦ ⟨(2*z.val.val)/N,by
    apply (Nat.div_lt_iff_lt_mul hN).mpr
    have := ZMod.val_lt z.val
    omega⟩
  have hf : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    apply ZMod.val_injective
    have hq : (2*u.val.val)/N=(2*v.val.val)/N := congrArg Fin.val he
    have hu := Nat.mod_add_div (2*u.val.val) N
    have hv := Nat.mod_add_div (2*v.val.val) N
    rw [hmod u,hq] at hu
    rw [hmod v] at hv
    omega
  have hc := Fintype.card_le_of_injective f hf
  simpa only [D,Fintype.card_coe,Fintype.card_fin] using hc

/-- At every nonzero cyclic modulus, at most two full-support cores
can occur under a two-point fibre cap. -/
theorem cyclic_full_support_core_card_le_two
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (b : ZMod N)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2) :
    ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=Finset.univ)).card ≤ 2 := by
  refine (full_support_core_card_le_doubling_fibre_card g b ?_).trans ?_
  · intro z
    convert hcap z using 1
    congr
  · convert zmod_doubling_fibre_card_le_two (∑ i, (g i+b)) using 1 <;> congr

/-- Only full-support cores have odd dyadic charge, so they determine
parity of the complete core charge sum. -/
theorem binary_core_sum_mod_two_eq_full_core_count
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) :
    (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card))%2=
      ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=Finset.univ)).card%2 := by
  classical
  have hterm (uv : Finset (Fin n) × Finset (Fin n)) :
      2^(n-(uv.1 ∪ uv.2).card)%2=if uv.1 ∪ uv.2=Finset.univ then 1 else 0 := by
    by_cases hfull : uv.1 ∪ uv.2=Finset.univ
    · simp [hfull]
    · have hle := Finset.card_le_card (Finset.subset_univ (uv.1 ∪ uv.2))
      simp only [Finset.card_univ,Fintype.card_fin] at hle
      have hne : (uv.1 ∪ uv.2).card ≠ n := fun h ↦ hfull (Finset.eq_univ_of_card _ (by simpa using h))
      have hd : 2 ∣ 2^(n-(uv.1 ∪ uv.2).card) := by
        simpa only [pow_one] using pow_dvd_pow 2 (by omega : 1 ≤ n-(uv.1 ∪ uv.2).card)
      simp only [if_neg hfull,Nat.mod_eq_zero_of_dvd hd]
  rw [Finset.sum_nat_mod]
  simp_rw [hterm]
  simp

/-- For a valid tuple without triple fibres, intrinsic loss has the same
parity as the number of its full-support actual relation cores. -/
theorem intrinsic_loss_mod_two_eq_full_core_count
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2) :
    tupleBinaryCollisionLoss g b%2=
      ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=Finset.univ)).card%2 := by
  rw [intrinsic_loss_eq_binary_core_cube_sum_of_fibres_le_two g hg b hcap]
  exact binary_core_sum_mod_two_eq_full_core_count g b

/-- Odd intrinsic loss extracts a unique full-support core at every
nonzero cyclic modulus, including even modulus where doubling is not injective. -/
theorem exists_unique_full_support_core_of_cyclic_odd_loss
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2)
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃! uv, uv ∈ tupleBinaryCollisionCores g b ∧ uv.1 ∪ uv.2=Finset.univ := by
  classical
  have hm : tupleBinaryCollisionLoss g b%2=
      ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=Finset.univ)).card%2 := by
    apply intrinsic_loss_mod_two_eq_full_core_count g hg b
    intro z
    convert hcap z using 1
    congr
  have hc := cyclic_full_support_core_card_le_two g b hcap
  have ho := Nat.odd_iff.mp hodd
  have hle : ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=Finset.univ)).card ≤ 1 := by omega
  have hpos : 0 < ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=Finset.univ)).card := by omega
  obtain ⟨uv,huv⟩ := Finset.card_pos.mp hpos
  refine ⟨uv,Finset.mem_filter.mp huv,?_⟩
  intro st hst
  exact Finset.card_le_one.mp hle _ (Finset.mem_filter.mpr hst) _ huv

/-- The intrinsic small-loss condition gives unique full-support core
extraction from odd loss at all nonzero cyclic moduli. -/
theorem exists_unique_full_support_core_of_cyclic_odd_small_loss
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsmall : 3*Nat.log 2 (tupleBinaryCollisionLoss g b) < n)
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃! uv, uv ∈ tupleBinaryCollisionCores g b ∧ uv.1 ∪ uv.2=Finset.univ := by
  apply exists_unique_full_support_core_of_cyclic_odd_loss g hg b ?_ hodd
  intro z
  convert tuple_subset_fibre_card_le_two_of_small_intrinsic_loss g b hsmall z using 1
  congr

end MinModulus
