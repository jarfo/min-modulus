import MinModulus.PrefixCertificateBasics

namespace MinModulus.PrefixCertificate

def verifyLinear (N : ℕ) : ℕ → List ℕ → ℕ → Certificate → Bool
  | _, p, _, .stop code => hits N p (decode code p.length)
  | 0, _, _, .branch _ => false
  | k + 1, p, next, .branch children =>
      decide (children.length = N - next) &&
        (children.zipIdx next).all fun (child, x) ↦
          verifyLinear N k (p ++ [x]) (x + 1) child

theorem verify_of_verifyLinear (N k : ℕ) (p : List ℕ) (next : ℕ)
    (cert : Certificate) (h : verifyLinear N k p next cert = true) :
    verify N k p next cert = true := by
  induction k generalizing p next cert with
  | zero => cases cert <;> simpa [verifyLinear, verify] using h
  | succ k ih =>
    cases cert with
    | stop code => exact h
    | branch children =>
      simp only [verifyLinear, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
      simp only [verify, List.all_eq_true]
      intro j hj
      have hjlt : j < children.length := by
        rw [h.1]
        exact List.mem_range.mp hj
      have hm : (children[j], next + j) ∈ children.zipIdx next := by
        apply List.mk_add_mem_zipIdx_iff_getElem?.mpr
        exact List.getElem?_eq_getElem hjlt
      have hh := h.2 _ hm
      have checked := ih (p ++ [next + j]) (next + j + 1) children[j] hh
      simpa [List.getD_eq_getElem, hjlt] using checked

theorem not_validTuple_of_verifyLinear {n N : ℕ} [NeZero N]
    (cert : Certificate) (hc : verifyLinear N n [0] 1 cert = true)
    (g : Fin (n + 1) → ZMod N) : ¬ ValidTuple g :=
  not_validTuple_of_verify cert (verify_of_verifyLinear N n [0] 1 cert hc) g

end MinModulus.PrefixCertificate
