import MinModulus.ChainForestDominantQuotient
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Ring.GeomSum

/-! Exact companion balance forces a wrapping axis in a cyclic quotient.
For the remaining large three-escape forests, parity makes the dominant
dyadic index at most one companion width, hence at most twice the parent
length. The sharp global conjecture remains open. -/

namespace MinModulus
open Finset

/-- Uniform fibres preserve finite sums up to the common multiplicity. -/
theorem sum_comp_of_balanced_fibres
    {B Q : Type*} [Fintype B] [Fintype Q] (f : B → Q) (m : ℕ)
    (hm : ∀ z, Nat.card {p : B // f p=z}=m) (χ : Q → ℂ) :
    (∑ p, χ (f p))=(m : ℂ)*∑ z, χ z := by
  classical
  have he := Fintype.sum_equiv (Equiv.sigmaFiberEquiv f)
    (fun p ↦ χ p.1) (fun p ↦ χ (f p)) (fun p ↦ congrArg χ p.2.property.symm)
  rw [Fintype.sum_sigma] at he
  rw [← he]
  simp only [sum_const,card_univ,← Nat.card_eq_fintype_card,hm,nsmul_eq_mul]
  exact (Finset.mul_sum Finset.univ χ (m : ℂ)).symm

/-- An additive character takes a finite sum to the product of its values. -/
theorem forest_character_sum_to_prod
    {I G : Type*} [AddCommMonoid G] (χ : AddChar G ℂ) (S : Finset I) (f : I → G) :
    χ (∑ i ∈ S, f i)=∏ i ∈ S, χ (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => simp only [sum_insert ha,prod_insert ha,χ.map_add_eq_mul,ih]

/-- A uniformly distributed cyclic box has an axis whose entire width
annihilates its seed. This follows by factoring its primitive character sum. -/
theorem exists_zero_boundary_of_balanced_cyclic_box
    {d : ℕ} [NeZero d] (hd : 1 < d) {I : Type*} [Fintype I]
    (K : I → ℕ) (hK : ∀ i, 0 < K i) (x : I → ZMod d)
    (m : ℕ) (hm : ∀ z : ZMod d,
      Nat.card {p : (∀ i, Fin (K i)) // (∑ i, (p i).val • x i)=z}=m) :
    ∃ i, x i ≠ 0 ∧ K i • x i=0 := by
  classical
  let χ : AddChar (ZMod d) ℂ := ZMod.stdAddChar
  have hχ : χ ≠ 1 := by
    intro h
    have he : χ 1=χ 0 := by rw [h]; rfl
    have : (1 : ZMod d)=0 := ZMod.injective_stdAddChar he
    have hh := (ZMod.natCast_eq_zero_iff 1 d).mp (by simpa using this)
    have := Nat.le_of_dvd (by decide : 0 < 1) hh
    omega
  have hzero : (∑ p : (∀ i, Fin (K i)), χ (∑ i, (p i).val • x i))=0 := by
    rw [sum_comp_of_balanced_fibres _ m hm χ,AddChar.sum_eq_zero_of_ne_one hχ,mul_zero]
  have hprod : (∏ i, ∑ t : Fin (K i), χ (x i)^t.val)=0 := by
    rw [Fintype.prod_sum]
    convert hzero using 1
    apply Finset.sum_congr rfl
    intro p _
    rw [forest_character_sum_to_prod]
    simp only [χ.map_nsmul_eq_pow]
  obtain ⟨i,_,hi⟩ := Finset.prod_eq_zero_iff.mp hprod
  refine ⟨i,?_,?_⟩
  · intro hx
    have hh : (K i : ℂ)=0 := by simpa only [hx,χ.map_zero_eq_one,one_pow,sum_const,
      card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hi
    have : K i=0 := by exact_mod_cast hh
    exact (Nat.ne_of_gt (hK i)) this
  · have hh := geom_sum_mul (χ (x i)) (K i)
    rw [← Fin.sum_univ_eq_sum_range,hi,zero_mul] at hh
    apply ZMod.injective_stdAddChar
    change χ (K i • x i)=χ 0
    rw [χ.map_nsmul_eq_pow,χ.map_zero_eq_one]
    exact (sub_eq_zero.mp hh.symm)

/-- Exact balance descends through any surjective quotient map that kills
the dominant seed. -/
theorem balanced_companion_projection_of_subbinary_dominant_chain
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G Q : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup Q] [Finite Q]
    (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (j : β)
    (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (π : G →+ Q) (hπ : Function.Surjective π) (hx : π (x j)=0) :
    ∃ m, Nat.card Q*m=2^(n-L j) ∧ ∀ z : Q,
      Nat.card {p : (∀ i : {i : β // i ≠ j}, Fin (2^(L i.val))) //
        (∑ i, (p i).val • π (x i.val))=z}=m := by
  classical
  obtain ⟨m,hcard,hm⟩ := balanced_companion_quotient_of_subbinary_dominant_chain
    L hL g hg E x b hchain hsub j hlarge π.ker hx
  let e := QuotientAddGroup.quotientKerEquivOfSurjective π hπ
  have he : ∀ a, e (QuotientAddGroup.mk' π.ker a)=π a := by intro a; rfl
  refine ⟨m,?_,?_⟩
  · rw [← Nat.card_congr e.toEquiv]
    exact hcard
  · intro z
    rw [← hm (e.symm z)]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro p
    rw [← e.injective.eq_iff,e.apply_symm_apply,he,map_sum]
    simp only [map_nsmul]

/-- If every companion seed is odd, a nontrivial dominant index
must divide the binary width of one actual companion chain. -/
theorem dominant_index_divides_companion_width_of_odd_companions
    {n N : ℕ} [NeZero N] {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : N < 2^n) (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (hodd : ∀ i, i ≠ j → Odd (x i).val) :
    ∃ e ≤ n-L j, N.gcd (x j).val=2^e ∧
      (e=0 ∨ ∃ i, i ≠ j ∧ e ≤ L i) := by
  classical
  obtain ⟨e,he,hgcd⟩ := gcd_two_power_of_subbinary_dominant_chain
    L hL g hg E x b hchain hsub j hlarge
  refine ⟨e,he,hgcd,?_⟩
  by_cases he0 : e=0
  · exact Or.inl he0
  right
  letI : NeZero (2^e) := ⟨by positivity⟩
  have hdiv : 2^e ∣ N := by rw [← hgcd]; exact Nat.gcd_dvd_left _ _
  let π : ZMod N →+ ZMod (2^e) := (ZMod.castHom hdiv (ZMod (2^e))).toAddMonoidHom
  have hπval : ∀ a : ZMod N, π a=(a.val : ZMod (2^e)) := by
    intro a
    change (a.cast : ZMod (2^e))=(a.val : ZMod (2^e))
    exact ZMod.cast_eq_val a
  have hx : π (x j)=0 := by
    rw [hπval,ZMod.natCast_eq_zero_iff,← hgcd]
    exact Nat.gcd_dvd_right _ _
  obtain ⟨m,_,hm⟩ := balanced_companion_projection_of_subbinary_dominant_chain
    L hL g hg E x b hchain (by simpa only [ZMod.card] using hsub) j hlarge
    π (ZMod.castHom_surjective hdiv) hx
  obtain ⟨i,_,hi⟩ := exists_zero_boundary_of_balanced_cyclic_box (Nat.one_lt_two_pow he0)
    (fun i : {i : β // i ≠ j} ↦ 2^(L i.val)) (fun _ ↦ by positivity)
    (fun i ↦ π (x i.val)) m hm
  have hu : IsUnit (π (x i.val)) := by
    rw [hπval,ZMod.isUnit_iff_coprime]
    exact (hodd i.val i.property).coprime_two_right.pow_right e
  have hdvd : 2^e ∣ 2^(L i.val) := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    exact hu.mul_left_eq_zero.mp (by simpa only [nsmul_eq_mul] using hi)
  exact ⟨i.val,i.property,(Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp hdvd⟩

/-- Among three seeds with at least two odd, a non-odd seed has only
odd companions. -/
theorem odd_companions_of_three_seeds
    {β : Type*} [Fintype β] [DecidableEq β] (hr : Fintype.card β=3)
    (v : β → ℕ) (hodd : 2 ≤ (Finset.univ.filter (fun i ↦ Odd (v i))).card)
    (j : β) (hj : ¬ Odd (v j)) : ∀ i, i ≠ j → Odd (v i) := by
  classical
  have hsub : Finset.univ.filter (fun i ↦ Odd (v i)) ⊆ Finset.univ.erase j := by
    intro i hi
    have hoi := (Finset.mem_filter.mp hi).2
    exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hj hoi,Finset.mem_univ _⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,hr]
    exact hodd)
  intro i hij
  have hi : i ∈ Finset.univ.filter (fun i ↦ Odd (v i)) := by
    rw [heq]
    exact Finset.mem_erase.mpr ⟨hij,Finset.mem_univ _⟩
  exact (Finset.mem_filter.mp hi).2

/-- The dominant gcd in a three-chain forest with two odd seeds is
one, or its dyadic exponent fits inside one companion chain. -/
theorem dominant_index_exponent_le_one_companion_of_three_chains
    {n N : ℕ} [NeZero N] {β : Type*} [Fintype β] [DecidableEq β]
    (hr : Fintype.card β=3) (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : N < 2^n) (j : β) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (hodd : 2 ≤ (Finset.univ.filter (fun i ↦ Odd (x i).val)).card) :
    ∃ e ≤ n-L j, N.gcd (x j).val=2^e ∧
      (e=0 ∨ ∃ i, i ≠ j ∧ e ≤ L i) := by
  classical
  by_cases hj : Odd (x j).val
  · obtain ⟨e,he,hgcd⟩ := gcd_two_power_of_subbinary_dominant_chain
      L hL g hg E x b hchain hsub j hlarge
    have hone : N.gcd (x j).val=1 := Nat.eq_one_of_dvd_coprimes
      (hj.coprime_two_right.pow_right e) (Nat.gcd_dvd_right N (x j).val) (by rw [hgcd])
    exact ⟨0,by omega,by simpa only [pow_zero] using hone,Or.inl rfl⟩
  · exact dominant_index_divides_companion_width_of_odd_companions L hL g hg E x b hchain
      hsub j hlarge (odd_companions_of_three_seeds hr (fun i ↦ (x i).val) hodd j hj)

/-- Original large three-escape no-half data force the dominant gcd
below the width of a single logarithmic companion. The actual forest,
genuine endpoints, parity, and spanning information are retained. -/
theorem exists_dominant_small_index_of_critical_three_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 66 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    A.card=3 ∧ ∃ L : A → ℕ, (∀ a, 0 < L a) ∧ (∑ a, L a)=n+1 ∧
      ∃ E : (Σ a : A, Fin (L a)) ≃ Fin (n+1), ∃ x : A → ZMod (2^(s+1)*q),
      (∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) ∧
      (∀ a (i : Fin (L a)), i.val+1=L a → E ⟨a,i⟩=a.val) ∧
      (∀ a : A, ∀ j, g j ≠ 2 • g a.val+b) ∧
      2 ≤ (Finset.univ.filter (fun a ↦ Odd (x a).val)).card ∧
      AddSubgroup.closure (Set.range x)=⊤ ∧
      ∃ j, (∀ a, a ≠ j → 2^(L a) ≤ 2*(n+1)) ∧
        n+1-2*Nat.log 2 (2*(n+1)) ≤ L j ∧
        (∃ e ≤ Nat.log 2 (2*(n+1)), (2^(s+1)*q).gcd (x j).val=2^e ∧
          (e=0 ∨ ∃ a, a ≠ j ∧ e ≤ L a)) ∧
        (2^(s+1)*q).gcd (x j).val ≤ 2*(n+1) ∧
        (Odd (x j).val → IsUnit (x j)) ∧
        q.Coprime (x j).val ∧ q ∣ addOrderOf (x j) := by
  classical
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan⟩ :=
    exists_spanning_three_chain_forest_of_critical_without_half hq (by omega) g hg hc A hA b hclosed hnohalf
  have hr : Fintype.card A=3 := by simpa only [Fintype.card_coe] using hcard
  have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
    intro a t
    have he := hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)
    rw [he]
    exact hgenuine a t
  have hsub : 2^(s+1)*q < 2^(n+1) := hc.trans_le (Nat.sub_le _ _)
  obtain ⟨j,hrest,hlong,hlarge,_⟩ := exists_dominant_two_primary_seed_of_subbinary_genuine_three_chains
    (by omega) hr L hL g hg E x b hchain hgen (by simpa only [ZMod.card] using hsub)
  obtain ⟨e,_,he,hfit⟩ := dominant_index_exponent_le_one_companion_of_three_chains
    hr L hL g hg E x b hchain hsub j hlarge hodd
  have hwidth : 2^e ≤ 2*(n+1) := by
    rcases hfit with he0 | ⟨a,haj,ha⟩
    · rw [he0,pow_zero]; omega
    · exact (Nat.pow_le_pow_right (by decide : 0 < 2) ha).trans (hrest a haj)
  refine ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan,j,hrest,hlong,?_,?_,?_,?_⟩
  · exact ⟨e,Nat.le_log_of_pow_le (by decide : 1 < 2) hwidth,he,hfit⟩
  · rwa [he]
  · exact isUnit_of_odd_subbinary_dominant_seed L hL g hg E x b hchain hsub j hlarge
  · exact odd_part_of_subbinary_dominant_seed hq L hL g hg E x b hchain hsub j hlarge

end MinModulus
