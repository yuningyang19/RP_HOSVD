import RPHOSVD.TensorGeometry

namespace RPHOSVD.Tensor
open Matrix
noncomputable section
abbrev shapeOff {d : ℕ} (n : Fin d → ℕ) (j : Fin d) := (k : {k : Fin d // k ≠ j}) → Fin (n k.val)

/-- Original unfolding prior to the fixed finite column enumeration. -/
def rawOriginal {d : ℕ} {n : Fin d → ℕ} (a : ArrayR n) (j : Fin d) :
    Matrix (Fin (n j)) (shapeOff n j) ℝ :=
  fun row col ↦ a ((Equiv.piSplitAt j (fun k ↦ Fin (n k))).symm (row,col))

/-- Column factors in the previous modes; untouched modes use identity matrices. -/
def offFactor {d : ℕ} {n r : Fin d → ℕ} (U : Factors n r) (mode : Schedule) (j : Fin d)
    (k : {k : Fin d // k ≠ j}) :
    Matrix (Fin (n k.val)) (Fin (if compressBefore mode j k.val then r k.val else n k.val)) ℝ :=
  fun i c ↦ if h : compressBefore mode j k.val then U k.val i (Fin.cast (if_pos h) c)
    else if i = Fin.cast (if_neg h) c then 1 else 0

def offProduct {d : ℕ} {n r : Fin d → ℕ} (U : Factors n r) (mode : Schedule) (j : Fin d) :
    Matrix (shapeOff n j) (Cols n r mode j) ℝ := fun p c ↦ ∏ k, offFactor U mode j k (p k) (c k)

/-- Matrix identity D_j = A_j F, where F is the tensor product of the
previous mode factors and identities, with the fixed column enumeration. -/
theorem unfolding_factor {d : ℕ} {n r : Fin d → ℕ} (a : ArrayR n) (U : Factors n r)
    (mode : Schedule) (j : Fin d) (i : Fin (n j)) (c : Cols n r mode j) :
    unfolding a U mode j i (Fintype.equivFin _ c) = (rawOriginal a j * offProduct U mode j) i c := by
  classical
  let e := Equiv.piSplitAt j (fun k ↦ Fin (n k))
  let w (z : Fin (n j) × shapeOff n j) :=
    a (e.symm z) * (if z.1 = i then 1 else 0) * offProduct U mode j z.2 c
  have key : unfolding a U mode j i (Fintype.equivFin _ c) = ∑ z, w z := by
    unfold unfolding
    apply Fintype.sum_equiv e
    intro x
    have hx : (Equiv.piSplitAt j (fun k ↦ Fin (n k))).symm (x j, fun k ↦ x k.val) = x :=
      e.symm_apply_apply x
    simp [e,w,offProduct,offFactor,hx]
  rw [key, Fintype.sum_prod_type, Matrix.mul_apply]
  simp [w,e,rawOriginal, Finset.sum_ite_irrel, apply_ite, ite_mul]

theorem offFactor_orthonormal {d : ℕ} {n r : Fin d → ℕ} (U : Factors n r) (mode : Schedule)
    (j : Fin d) (k : {k : Fin d // k ≠ j}) (hu : (U k.val).transpose * U k.val = 1) :
    (offFactor U mode j k).transpose * offFactor U mode j k = 1 := by
  classical
  by_cases h : compressBefore mode j k.val
  · ext a b
    let a' := Fin.cast (if_pos h) a
    let b' := Fin.cast (if_pos h) b
    have hh := congrArg (fun M : Matrix (Fin (r k.val)) (Fin (r k.val)) ℝ ↦ M a' b') hu
    simpa [offFactor, h, Matrix.mul_apply, Matrix.one_apply, a',b'] using hh
  · ext a b
    simp [offFactor,h,Matrix.mul_apply, Matrix.one_apply, mul_ite, eq_comm]

theorem offProduct_orthonormal {d : ℕ} {n r : Fin d → ℕ} (U : Factors n r) (mode : Schedule)
    (j : Fin d) (hu : ∀ k, (U k).transpose * U k = 1) :
    (offProduct U mode j).transpose * offProduct U mode j = 1 := by
  classical
  ext a b
  simp only [Matrix.mul_apply, transpose_apply, offProduct, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k i ↦ offFactor U mode j k i (a k) * offFactor U mode j k i (b k))]
  have hs (k : {k : Fin d // k ≠ j}) : (∑ i, offFactor U mode j k i (a k) *
      offFactor U mode j k i (b k)) = (if a k = b k then 1 else 0 : ℝ) := by
    simpa only [Matrix.mul_apply, transpose_apply, Matrix.one_apply] using
      congrArg (fun Z ↦ Z (a k) (b k)) (offFactor_orthonormal U mode j k (hu _))
  simp_rw [hs]
  by_cases h : a = b
  · subst b; simp
  · obtain ⟨k,hk⟩ := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ k); simp [hk]

end
end RPHOSVD.Tensor
