import research.CoordinateDifferenceRecursion
import research.QuarticResidualGraph
import MinModulus.TriplingClosure

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- A coordinate representation of the doubled difference in an
all-degree single-repeat collision uses endpoints in the residual supports. -/
theorem doubled_difference_endpoints_mem_residual_union
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (a b p q : Fin n) (hpq : p ≠ q)
    (S T : Finset (Fin n)) (hc : S.card = T.card)
    (he : 2 • g a+(∑ i ∈ S, g i)=2 • g b+(∑ i ∈ T, g i))
    (hd : 2 • (g a-g b)=g p-g q) :
    p ∈ S ∪ T ∧ q ∈ S ∪ T := by
  have hshift : (∑ i ∈ S, g i)+(g p-g q)=∑ i ∈ T, g i := by
    apply add_right_cancel (b := 2 • g b)
    calc
      _ = 2 • g a+(∑ i ∈ S, g i) := by rw [← hd,two_nsmul,two_nsmul]; abel
      _ = 2 • g b+(∑ i ∈ T, g i) := he
      _ = _ := by abel
  apply coordinate_difference_match_endpoints_mem_any_degree g hg p q hpq S T hc
  calc
    _ = ((∑ i ∈ S, g i)+(g p-g q))+g q := by abel
    _ = _ := congrArg (fun x ↦ x+g q) hshift

/-- If a doubled difference between two anchors of a single-repeat fibre
is a nonzero coordinate difference, both representing coordinates lie
outside the whole anchor family. This is uniform in the residual degree. -/
theorem single_repeat_fibre_doubled_difference_endpoints_outside
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (x : G) (R : Finset (Fin n)) (B : Fin n → Finset (Fin n))
    (hc : ∀ a ∈ R, (B a).card=k)
    (ha : ∀ a ∈ R, a ∉ B a)
    (hv : ∀ a ∈ R, 2 • g a+(∑ i ∈ B a, g i)=x)
    (a b : Fin n) (haR : a ∈ R) (hbR : b ∈ R)
    (p q : Fin n) (hpq : p ≠ q)
    (hd : 2 • (g a-g b)=g p-g q) :
    p ∉ R ∧ q ∉ R := by
  have havoid := residual_support_disjoint_anchor_family g hg x R B hc ha hv
  obtain ⟨hp,hq⟩ := doubled_difference_endpoints_mem_residual_union g hg a b p q hpq
    (B a) (B b) ((hc a haR).trans (hc b hbR).symm)
    ((hv a haR).trans (hv b hbR).symm) hd
  have hout (i : Fin n) (hi : i ∈ B a ∪ B b) : i ∉ R := by
    intro hiR
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.disjoint_left.mp (havoid a haR) hi hiR
    · exact Finset.disjoint_left.mp (havoid b hbR) hi hiR
  exact ⟨hout p hp,hout q hq⟩

/-- Ordered pairs of fibre anchors whose doubled differences are
coordinate differences inject into ordered pairs outside the fibre.
No bound on the residual degree is required. -/
theorem single_repeat_fibre_coordinate_difference_edges_card_le
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (hd : Function.Injective (fun z : G ↦ 2 • z))
    (x : G) (R : Finset (Fin n)) (B : Fin n → Finset (Fin n))
    (hc : ∀ a ∈ R, (B a).card=k)
    (ha : ∀ a ∈ R, a ∉ B a)
    (hv : ∀ a ∈ R, 2 • g a+(∑ i ∈ B a, g i)=x)
    (E : Finset (Fin n × Fin n))
    (P Q : (Fin n × Fin n) → Fin n)
    (hE : ∀ ab ∈ E, ab.1 ∈ R ∧ ab.2 ∈ R ∧ ab.1 ≠ ab.2)
    (he : ∀ ab ∈ E, 2 • (g ab.1-g ab.2)=g (P ab)-g (Q ab)) :
    E.card ≤ (n-R.card)*(n-R.card-1) := by
  classical
  have hpair (ab : Fin n × Fin n) (hab : ab ∈ E) : P ab ≠ Q ab := by
    intro hpq
    have hz : 2 • (g ab.1-g ab.2)=2 • (0 : G) := by
      rw [he ab hab,hpq,sub_self,smul_zero]
    exact (hE ab hab).2.2 (validTuple_injective g hg (sub_eq_zero.mp (hd hz)))
  have hinj : ∀ u v : G, u+u=v+v → u=v := by
    intro u v huv
    apply hd
    simpa only [two_nsmul] using huv
  have hbound : E.card ≤ (Rᶜ.offDiag).card := by
    apply Finset.card_le_card_of_injOn (fun ab ↦ (P ab,Q ab))
    · intro ab hab
      obtain ⟨haR,hbR,_⟩ := hE ab hab
      obtain ⟨hp,hq⟩ := single_repeat_fibre_doubled_difference_endpoints_outside
        g hg x R B hc ha hv ab.1 ab.2 haR hbR (P ab) (Q ab) (hpair ab hab) (he ab hab)
      exact Finset.mem_offDiag.mpr
        ⟨Finset.mem_compl.mpr hp,Finset.mem_compl.mpr hq,hpair ab hab⟩
    · intro ab hab cd hcd heq
      have hp : P ab=P cd := congrArg Prod.fst heq
      have hq : Q ab=Q cd := congrArg Prod.snd heq
      have hdiff : g ab.1-g ab.2=g cd.1-g cd.2 := by
        apply hd
        change 2 • (g ab.1-g ab.2)=2 • (g cd.1-g cd.2)
        rw [he ab hab,he cd hcd,hp,hq]
      obtain ⟨hfirst,hsecond⟩ := pair_eq_of_sub_eq_sub_of_validTuple hinj g hg
        ab.1 ab.2 cd.1 cd.2 (hE ab hab).2.2 hdiff
      exact Prod.ext hfirst hsecond
  simpa only [Finset.offDiag_card,Finset.card_compl,Fintype.card_fin,
    Nat.mul_sub_one] using hbound

/-- If every pair of distinct anchors in a single-repeat fibre has a
doubled difference represented by coordinates, a fibre with at least two
anchors occupies at most half the coordinates, in every degree. -/
theorem single_repeat_fibre_card_le_complement_of_all_differences
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (hd : Function.Injective (fun z : G ↦ 2 • z))
    (x : G) (R : Finset (Fin n)) (B : Fin n → Finset (Fin n))
    (hc : ∀ a ∈ R, (B a).card=k)
    (ha : ∀ a ∈ R, a ∉ B a)
    (hv : ∀ a ∈ R, 2 • g a+(∑ i ∈ B a, g i)=x)
    (hr : 2 ≤ R.card)
    (hrep : ∀ a ∈ R, ∀ b ∈ R, a ≠ b →
      ∃ p q : Fin n, 2 • (g a-g b)=g p-g q) :
    R.card ≤ n-R.card := by
  classical
  have hex (ab : Fin n × Fin n) (hab : ab ∈ R.offDiag) :
      ∃ pq : Fin n × Fin n, 2 • (g ab.1-g ab.2)=g pq.1-g pq.2 := by
    obtain ⟨haR,hbR,hne⟩ := Finset.mem_offDiag.mp hab
    obtain ⟨p,q,hpq⟩ := hrep ab.1 haR ab.2 hbR hne
    exact ⟨(p,q),hpq⟩
  let F (ab : Fin n × Fin n) :=
    if h : ab ∈ R.offDiag then Classical.choose (hex ab h) else ab
  have hF (ab : Fin n × Fin n) (hab : ab ∈ R.offDiag) :
      2 • (g ab.1-g ab.2)=g (F ab).1-g (F ab).2 := by
    simp only [F,dif_pos hab]
    exact Classical.choose_spec (hex ab hab)
  have hbound := single_repeat_fibre_coordinate_difference_edges_card_le
    g hg hd x R B hc ha hv R.offDiag (fun ab ↦ (F ab).1) (fun ab ↦ (F ab).2)
    (fun _ h ↦ Finset.mem_offDiag.mp h) hF
  rw [Finset.offDiag_card,← Nat.mul_sub_one] at hbound
  by_contra h
  have hm : n-R.card ≤ R.card-1 := by omega
  have hr' : R.card-1+1=R.card := by omega
  have hm' : n-R.card-1 ≤ n-R.card := Nat.sub_le _ _
  nlinarith

end MinModulus.Research
