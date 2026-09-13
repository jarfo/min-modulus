import research.NegativeAffineBlock

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- Three distinct coordinates of a valid cyclic tuple cannot have the
same triple. No oddness or invertibility of three is assumed. -/
theorem cyclic_triple_fibre_card_le_two
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (t : ZMod N) :
    ((Finset.univ : Finset (Fin n)).filter (fun i ↦ 3 • g i=t)).card ≤ 2 := by
  classical
  let F := (Finset.univ : Finset (Fin n)).filter (fun i ↦ 3 • g i=t)
  let q : Fin n → ℕ := fun i ↦ (3*(g i).val)/N
  have hrep (i : Fin n) (hi : i ∈ F) : 3*(g i).val=t.val+N*q i := by
    have hi' := (Finset.mem_filter.mp hi).2
    have he : ((3*(g i).val : ℕ) : ZMod N)=t := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val,
        nsmul_eq_mul,Nat.cast_ofNat] using hi'
    have hm := congrArg ZMod.val he
    simp only [ZMod.val_natCast] at hm
    have h := Nat.mod_add_div (3*(g i).val) N
    rw [hm] at h
    exact h.symm
  have hlt (i : Fin n) : q i < 3 := by
    apply (Nat.div_lt_iff_lt_mul (NeZero.pos N)).mpr
    have h := ZMod.val_lt (g i)
    omega
  have hqi : Set.InjOn q F := by
    intro i hi j hj he
    have h1 := hrep i hi
    have h2 := hrep j hj
    rw [he] at h1
    apply validTuple_injective g hg
    apply ZMod.val_injective N
    omega
  have hprogress (a b c : Fin n) (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F)
      (hab : a ≠ b) (hac : a ≠ c) (he : q a+q b=2*q c) : False := by
    have h1 := hrep a ha
    have h2 := hrep b hb
    have h3 := hrep c hc
    have hmul := congrArg (fun z : ℕ ↦ N*z) he
    have hv : (g a).val+(g b).val=(g c).val+(g c).val := by nlinarith
    have hv' : g a+g b=g c+g c := by
      simpa only [Nat.cast_add,ZMod.natCast_zmod_val] using
        congrArg (fun z : ℕ ↦ (z : ZMod N)) hv
    rcases pair_sum_eq_of_validTuple g hg a b c c hab hv' with h | h
    · exact hac h.1
    · exact hac h.1
  change F.card ≤ 2
  by_contra hcard
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ :=
    Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge hcard)
  have hab' : q a ≠ q b := fun he ↦ hab (hqi ha hb he)
  have hac' : q a ≠ q c := fun he ↦ hac (hqi ha hc he)
  have hbc' : q b ≠ q c := fun he ↦ hbc (hqi hb hc he)
  have hla := hlt a
  have hlb := hlt b
  have hlc := hlt c
  have hmid : q a+q b=2*q c ∨ q a+q c=2*q b ∨ q b+q c=2*q a := by omega
  rcases hmid with h | h | h
  · exact hprogress a b c ha hb hc hab hac h
  · exact hprogress a c b ha hc hb hac hab h
  · exact hprogress b c a hb hc ha hbc hab.symm h

/-- A partial negative affine map on a valid cyclic tuple has at most
two fixed coordinates, even when three is not invertible. -/
theorem cyclic_negative_affine_fixed_card_le_two
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (S : Finset (Fin n)) (f : Fin n → Fin n) (t : ZMod N)
    (hd : ∀ i ∈ S, g (f i)+2 • g i=t) :
    (S.filter (fun i ↦ f i=i)).card ≤ 2 := by
  classical
  have hsub : S.filter (fun i ↦ f i=i) ⊆
      (Finset.univ : Finset (Fin n)).filter (fun i ↦ 3 • g i=t) := by
    intro i hi
    obtain ⟨hiS,hfi⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [show (3 : ℕ)=1+2 from rfl,add_nsmul,one_nsmul]
    simpa only [hfi] using hd i hiS
  exact (Finset.card_le_card hsub).trans (cyclic_triple_fibre_card_le_two g hg t)

/-- For cyclic tuples the negative affine domain bound loses at most
two fixed points, uniformly in the tuple dimension. -/
theorem cyclic_negative_affine_domain_twice_card_le_add_two
    {n N : ℕ} [NeZero N]
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (S : Finset (Fin n))
    (f : Fin n → Fin n) (t : ZMod N)
    (hd : ∀ i ∈ S, g (f i)+2 • g i=t) :
    2*S.card ≤ n+2 := by
  have h := negative_affine_domain_twice_card_le_add_fixed hinj g hg S f t hd
  exact h.trans (Nat.add_le_add_left (cyclic_negative_affine_fixed_card_le_two g hg S f t hd) n)

/-- A valid tuple at odd modulus closed under a negative affine doubling
map has dimension at most two. The closure assumption is explicit. -/
theorem odd_valid_negative_affine_closed_dimension_le_two
    {n N : ℕ} [NeZero N] (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (f : Fin n → Fin n) (t : ZMod N)
    (hd : ∀ i, g (f i)+2 • g i=t) : n ≤ 2 := by
  have hinj : ∀ u v : ZMod N, u+u=v+v → u=v := by
    intro u v he
    apply ((ZMod.isUnit_iff_coprime 2 N).mpr hN.coprime_two_left).mul_left_cancel
    simpa only [Nat.cast_ofNat,two_mul] using he
  have h := cyclic_negative_affine_domain_twice_card_le_add_two hinj g hg
    Finset.univ f t (fun i _ ↦ hd i)
  simp only [Finset.card_univ,Fintype.card_fin] at h
  omega

end MinModulus.Research
