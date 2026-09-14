import research.RepresentedTriangleCounts
import research.MissingPairTriangleCount

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- A pair family covering every unrepresented doubled difference
bounds how small all full positive affine domains can be. -/
theorem missing_pair_cover_bounds_positive_affine_domains
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n)
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (D : Finset (Finset (Fin n)))
    (hD : ∀ P ∈ D, P.card=2)
    (hmissing : ∀ a b, a≠b →
      (¬ ∃ p q, 2 • (g a-g b)=g p-g q) → ({a,b} : Finset (Fin n)) ∈ D)
    (M : ℕ) (hMtwo : 2 ≤ M) (hM : ∀ t, (positiveAffineDomain g t).card ≤ M) :
    n*n.choose 2 ≤ (2*M+4)*n.choose 2+6*(n-2)*D.card := by
  classical
  let Ts := ((Finset.univ : Finset (Fin n)).powersetCard 3).filter
    (fun T ↦ ∀ a ∈ T, ∀ b ∈ T, a≠b → ∃ p q, 2 • (g a-g b)=g p-g q)
  have hTs : ∀ T ∈ Ts, T.card=3 ∧
      ∀ a ∈ T, ∀ b ∈ T, a≠b → ∃ p q, 2 • (g a-g b)=g p-g q := by
    intro T hT
    obtain ⟨hc,he⟩ := Finset.mem_filter.mp hT
    exact ⟨(Finset.mem_powersetCard.mp hc).2,he⟩
  have hcover : ∀ T ∈ (Finset.univ : Finset (Fin n)).powersetCard 3,
      (∀ P ∈ D, ¬ P ⊆ T) → T ∈ Ts := by
    intro T hT havoid
    apply Finset.mem_filter.mpr
    refine ⟨hT,?_⟩
    intro a ha b hb hab
    by_contra hnone
    apply havoid {a,b} (hmissing a b hab hnone)
    intro i hi
    rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hi : i=a ∨ i=b) with rfl | rfl
    · exact ha
    · exact hb
  have hlow := triangle_family_card_add_missing_pair_bound Ts D hD hcover
  have hhigh := represented_triangle_family_card_upper_bound hinj g hg Ts hTs M hM
  have hcoeff : 2*(M-2)+(n-2)+6=2*M+n := by omega
  rw [hcoeff] at hhigh
  have hchoose := Nat.choose_succ_right_eq n 2
  have hB : n.choose 2*(n-2)+2*n.choose 2=n*n.choose 2 := by
    calc
      _ = n.choose 2*((n-2)+2) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hn,Nat.mul_comm]
  nlinarith

/-- In the dense represented-pair regime, every upper bound M on full
positive affine domain sizes is within twenty of half the dimension. -/
theorem positive_affine_domain_bound_of_few_missing_pairs
    {n N : ℕ} [NeZero N] (hn : 16 ≤ n)
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (D : Finset (Finset (Fin n)))
    (hD : ∀ P ∈ D, P.card=2)
    (hmissing : ∀ a b, a≠b →
      (¬ ∃ p q, 2 • (g a-g b)=g p-g q) → ({a,b} : Finset (Fin n)) ∈ D)
    (hdense : (n-9)*D.card < 3*n.choose 2)
    (M : ℕ) (hMtwo : 2 ≤ M) (hM : ∀ t, (positiveAffineDomain g t).card ≤ M) :
    n < 2*M+40 := by
  have hbound := missing_pair_cover_bounds_positive_affine_domains (by omega : 2 ≤ n)
    hinj g hg D hD hmissing M hMtwo hM
  have hcoef : n-2 ≤ 2*(n-9) := by omega
  have hprod : (n-2)*D.card ≤ 2*((n-9)*D.card) := by
    calc
      _ ≤ (2*(n-9))*D.card := Nat.mul_le_mul_right _ hcoef
      _ = _ := by ring
  by_contra hsize
  have hsize' : 2*M+40 ≤ n := by omega
  have hmul := Nat.mul_le_mul_right (n.choose 2) hsize'
  nlinarith

/-- A valid cyclic tuple with sufficiently few unrepresented pairs has
an actual full positive affine domain of size greater than (n-40)/2. -/
theorem exists_large_positive_affine_domain_of_few_missing_pairs
    {n N : ℕ} [NeZero N] (hn : 44 ≤ n)
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (D : Finset (Finset (Fin n)))
    (hD : ∀ P ∈ D, P.card=2)
    (hmissing : ∀ a b, a≠b →
      (¬ ∃ p q, 2 • (g a-g b)=g p-g q) → ({a,b} : Finset (Fin n)) ∈ D)
    (hdense : (n-9)*D.card < 3*n.choose 2) :
    ∃ t, n < 2*(positiveAffineDomain g t).card+40 := by
  classical
  let S := Finset.univ.image (fun t : ZMod N ↦ (positiveAffineDomain g t).card)
  have hS : S.Nonempty := ⟨(positiveAffineDomain g 0).card,
    Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩
  let M := S.max' hS
  have hM : ∀ t, (positiveAffineDomain g t).card ≤ M := by
    intro t
    exact Finset.le_max' S _ (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩)
  have hMtwo : 2 ≤ M := by
    by_contra hsmall
    have hmax : ∀ t, (positiveAffineDomain g t).card ≤ 2 := fun t ↦ (hM t).trans (by omega)
    have hh := positive_affine_domain_bound_of_few_missing_pairs (by omega : 16 ≤ n)
      hinj g hg D hD hmissing hdense 2 (by omega) hmax
    omega
  have hsize := positive_affine_domain_bound_of_few_missing_pairs (by omega : 16 ≤ n)
    hinj g hg D hD hmissing hdense M hMtwo hM
  obtain ⟨t,_,ht⟩ := Finset.mem_image.mp (Finset.max'_mem S hS)
  exact ⟨t,by simpa only [ht] using hsize⟩

end MinModulus.Research
