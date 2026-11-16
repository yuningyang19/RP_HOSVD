import RPHOSVD.Tensor

/-! Entrywise bridges between the concrete Tucker reconstruction and orthogonal
projection geometry, in arbitrary finite order and nonuniform dimensions. -/
noncomputable section
namespace RPHOSVD.Tensor
open Matrix

/-- Tensor product of mode matrices in the fixed dependent index order. -/
def modeProduct {d : ℕ} {n r : Fin d → ℕ} (U : Factors n r) :
    Matrix (Index n) (Index r) ℝ := fun x p ↦ ∏ j, U j (x j) (p j)

theorem modeProduct_mul {d : ℕ} {n r s : Fin d → ℕ} (U : Factors n r) (V : Factors r s) :
    modeProduct U * modeProduct V = modeProduct (fun j ↦ U j * V j) := by
  ext x z
  simp only [Matrix.mul_apply, modeProduct, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j k ↦ U j (x j) k * V j k (z j))).symm

theorem modeProduct_transpose {d : ℕ} {n r : Fin d → ℕ} (U : Factors n r) :
    (modeProduct U).transpose = modeProduct (fun j ↦ (U j).transpose) := rfl

theorem modeProduct_one {d : ℕ} (n : Fin d → ℕ) :
    modeProduct (fun j ↦ (1 : Matrix (Fin (n j)) (Fin (n j)) ℝ)) = 1 := by
  classical
  ext x y
  by_cases h : x = y
  · subst y; simp [modeProduct]
  · obtain ⟨j,hj⟩ := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Matrix.one_apply_ne hj

theorem tensorFrame {d : ℕ} {n r : Fin d → ℕ} (U : Factors n r)
    (h : ∀ j, (U j).transpose * U j = 1) :
    (modeProduct U).transpose * modeProduct U = 1 := by
  rw [modeProduct_transpose, modeProduct_mul]
  simpa only [h] using modeProduct_one r

/-- The reconstruction in the public targets is the projection onto the
Kronecker product of the returned frames; no assumption of a best Tucker fit. -/
theorem reconstruction_eq {d : ℕ} {n r : Fin d → ℕ} (a : ArrayR n) (U : Factors n r) :
    reconstruction a U = (modeProduct U * (modeProduct U).transpose).mulVec a := by
  rw [modeProduct_transpose, modeProduct_mul]
  ext x
  simp [reconstruction, modeProduct, Matrix.mulVec, dotProduct, mul_comm]

theorem tuckerProjector_idempotent {d : ℕ} {n r : Fin d → ℕ} (U : Factors n r)
    (h : ∀ j, (U j).transpose * U j = 1) :
    let P := modeProduct U * (modeProduct U).transpose
    P * P = P := by
  dsimp only
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (modeProduct U).transpose, tensorFrame U h,
    Matrix.one_mul]

end RPHOSVD.Tensor
