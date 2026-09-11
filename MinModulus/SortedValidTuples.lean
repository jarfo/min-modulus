import MinModulus.CyclicUnitNormalization
import MinModulus.G1Triangle
import Mathlib.Data.Finset.Sort

namespace MinModulus
open Finset

theorem exists_sorted_valid_nat_tuple
    {n N : ℕ} [NeZero N] (g : Fin (n+1) → ZMod N) (hg : ValidTuple g) :
    ∃ v : Fin (n+1) → ℕ, StrictMono v ∧ v 0=0 ∧
      (∀ i, v i<N) ∧ ValidTuple (fun i ↦ (v i : ZMod N)) ∧
      (∀ i, ∃ j, v j=(g i-g 0).val) ∧
      (∀ j, ∃ i, v j=(g i-g 0).val) := by
  classical
  let w : Fin (n+1) → ZMod N := fun i ↦ g i-g 0
  have hw : ValidTuple w := validTuple_sub_const g hg (g 0)
  have hw0 : w 0=0 := by simp [w]
  have hinj : Function.Injective (fun i ↦ (w i).val) :=
    (ZMod.val_injective N).comp (validTuple_injective w hw)
  let S : Finset ℕ := univ.image fun i ↦ (w i).val
  have hcard : S.card=n+1 := by
    simpa [S] using card_image_of_injective (univ : Finset (Fin (n+1))) hinj
  let v : Fin (n+1) ↪o ℕ := S.orderEmbOfFin hcard
  have hpre (j : Fin (n+1)) : ∃ i, (w i).val=v j := by
    have hm : v j∈S := S.orderEmbOfFin_mem hcard j
    simpa only [S,mem_image,mem_univ,true_and] using hm
  choose e he using hpre
  have hei : Function.Injective e := by
    intro i j hij
    apply v.injective
    rw [← he i,← he j,hij]
  let emb : Fin (n+1) ↪ Fin (n+1) := ⟨e,hei⟩
  have hv : ValidTuple (fun i ↦ (v i : ZMod N)) := by
    have hh := validTuple_embedding emb w hw
    have heq : (fun i ↦ w (emb i))=(fun i ↦ (v i : ZMod N)) := by
      funext i
      rw [← he i]
      exact (ZMod.natCast_zmod_val (w (e i))).symm
    rwa [heq] at hh
  have hmem : 0∈S := by
    apply mem_image.mpr
    exact ⟨0,mem_univ _,by simp [hw0]⟩
  let z : S := ⟨0,hmem⟩
  let j : Fin (n+1) := (S.orderIsoOfFin hcard).symm z
  have hj : v j=0 := by
    change ((S.orderIsoOfFin hcard) ((S.orderIsoOfFin hcard).symm z)).val=0
    simp [z]
  have hv0 : v 0=0 := by
    have hle := v.monotone (show (0 : Fin (n+1))≤j from Fin.zero_le _)
    omega
  refine ⟨v,v.strictMono,hv0,?_,hv,?_,?_⟩
  · intro i
    rw [← he i]
    exact (w (e i)).val_lt
  · intro i
    have hm : (w i).val∈S := mem_image.mpr ⟨i,mem_univ _,rfl⟩
    refine ⟨(S.orderIsoOfFin hcard).symm ⟨(w i).val,hm⟩,?_⟩
    change ((S.orderIsoOfFin hcard) ((S.orderIsoOfFin hcard).symm
      ⟨(w i).val,hm⟩)).val=(w i).val
    simp
  · intro j
    exact ⟨e j,(he j).symm⟩

theorem not_validTuple_six_of_sorted_zero_exclusion
    {N : ℕ} [NeZero N]
    (hex : ∀ a b c d e : ℕ, 1≤a → a<b → b<c → c<d → d<e → e<N →
      ¬ ValidTuple (![0,(a : ZMod N),(b : ZMod N),(c : ZMod N),(d : ZMod N),(e : ZMod N)]))
    (g : Fin 6 → ZMod N) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨v,hv,h0,hlt,hw,_,_⟩ := exists_sorted_valid_nat_tuple (n := 5) g hg
  have h01 := hv (show (0 : Fin 6)<1 by decide)
  have h12 := hv (show (1 : Fin 6)<2 by decide)
  have h23 := hv (show (2 : Fin 6)<3 by decide)
  have h34 := hv (show (3 : Fin 6)<4 by decide)
  have h45 := hv (show (4 : Fin 6)<5 by decide)
  apply hex (v 1) (v 2) (v 3) (v 4) (v 5) (by omega) h12 h23 h34 h45 (hlt 5)
  have heq : (fun i ↦ (v i : ZMod N))=![0,(v 1 : ZMod N),(v 2 : ZMod N),
      (v 3 : ZMod N),(v 4 : ZMod N),(v 5 : ZMod N)] := by
    funext i
    fin_cases i <;> simp [h0]
  rwa [heq] at hw

theorem not_validTuple_six_normalized_of_sorted_exclusion
    {N : ℕ} [NeZero N] (hN : 1<N)
    (hex : ∀ a b c d : ℕ, 2≤a → a<b → b<c → c<d → d<N →
      ¬ ValidTuple (![0,1,(a : ZMod N),(b : ZMod N),(c : ZMod N),(d : ZMod N)]))
    (g : Fin 6 → ZMod N) (hg0 : g 0=0) (hg1 : g 1=1) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨v,hv,h0,hlt,hw,hpre,_⟩ := exists_sorted_valid_nat_tuple (n := 5) g hg
  obtain ⟨j,hj⟩ := hpre 1
  have hj1 : v j=1 := by
    simpa [hg0,hg1,ZMod.val_one'' (show N≠1 by omega)] using hj
  have hj0 : j≠0 := by intro h; rw [h,h0] at hj1; omega
  have hjle : (1 : Fin 6)≤j := by
    have : j.val≠0 := by simpa using hj0
    change 1≤j.val
    omega
  have hvle := hv.monotone hjle
  have hv01 := hv (show (0 : Fin 6)<1 by decide)
  have h1 : v 1=1 := by omega
  have h12 := hv (show (1 : Fin 6)<2 by decide)
  have h23 := hv (show (2 : Fin 6)<3 by decide)
  have h34 := hv (show (3 : Fin 6)<4 by decide)
  have h45 := hv (show (4 : Fin 6)<5 by decide)
  apply hex (v 2) (v 3) (v 4) (v 5) (by omega) h23 h34 h45 (hlt 5)
  have heq : (fun i ↦ (v i : ZMod N))=![0,1,(v 2 : ZMod N),
      (v 3 : ZMod N),(v 4 : ZMod N),(v 5 : ZMod N)] := by
    funext i
    fin_cases i <;> simp [h0,h1]
  rwa [heq] at hw

theorem not_validTuple_six_of_unit_and_nonunit_exclusions
    {N : ℕ} [NeZero N] [Nontrivial (ZMod N)] (hN : 1<N)
    (hunit : ∀ a b c d : ℕ, 2≤a → a<b → b<c → c<d → d<N →
      ¬ ValidTuple (![0,1,(a : ZMod N),(b : ZMod N),(c : ZMod N),(d : ZMod N)]))
    (hnonunit : ∀ a b c d e : ℕ, 1≤a → a<b → b<c → c<d → d<e → e<N →
      Nat.gcd a N≠1 → Nat.gcd b N≠1 → Nat.gcd c N≠1 →
      Nat.gcd d N≠1 → Nat.gcd e N≠1 →
      ¬ ValidTuple (![0,(a : ZMod N),(b : ZMod N),(c : ZMod N),(d : ZMod N),(e : ZMod N)]))
    (g : Fin 6 → ZMod N) : ¬ ValidTuple g := by
  classical
  intro hg
  by_cases hu : ∃ i, IsUnit (g i-g 0)
  · obtain ⟨i,hi⟩ := hu
    obtain ⟨w,hw,h0,h1⟩ := exists_normalized_valid_of_unit_difference g hg 0 i hi
    exact not_validTuple_six_normalized_of_sorted_exclusion hN hunit w h0 h1 hw
  · push Not at hu
    obtain ⟨v,hv,h0,hlt,hw,_,hback⟩ := exists_sorted_valid_nat_tuple (n := 5) g hg
    have hnu (j : Fin 6) : Nat.gcd (v j) N≠1 := by
      intro hc
      have hi : IsUnit (v j : ZMod N) := (ZMod.isUnit_iff_coprime _ _).mpr hc
      obtain ⟨i,heq⟩ := hback j
      rw [heq,ZMod.natCast_zmod_val] at hi
      exact hu i hi
    have h01 := hv (show (0 : Fin 6)<1 by decide)
    have h12 := hv (show (1 : Fin 6)<2 by decide)
    have h23 := hv (show (2 : Fin 6)<3 by decide)
    have h34 := hv (show (3 : Fin 6)<4 by decide)
    have h45 := hv (show (4 : Fin 6)<5 by decide)
    apply hnonunit (v 1) (v 2) (v 3) (v 4) (v 5) (by omega)
      h12 h23 h34 h45 (hlt 5) (hnu 1) (hnu 2) (hnu 3) (hnu 4) (hnu 5)
    have heq : (fun i ↦ (v i : ZMod N))=![0,(v 1 : ZMod N),(v 2 : ZMod N),
        (v 3 : ZMod N),(v 4 : ZMod N),(v 5 : ZMod N)] := by
      funext i
      fin_cases i <;> simp [h0]
    rwa [heq] at hw





end MinModulus
