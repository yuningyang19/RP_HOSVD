import RPHOSVD.TensorGeometry
import RPHOSVD.ExactProjection

/-! The STHOSVD tail on a compressed unfolding is compared to the tail on the
original unfolding by a column isometry. -/
noncomputable section
namespace RPHOSVD.Tensor
open Matrix RPHOSVD.Projection

private theorem frob_nonneg {m n : ℕ} (A : Mat m n) : 0 ≤ frobSq A := by
  rw [frobSq_cols]; exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Left compression by a frame transpose contracts Frobenius errors. -/
theorem frobCompress {m n k : ℕ} (A : Mat m n) (F : Mat m k) (h : Fᵀ * F = 1) :
    frobSq (Fᵀ * A) ≤ frobSq A := by
  let P := projector F
  have hs : Pᵀ = P := by simp [P,projector,transpose_mul]
  have hi : P*P = P := by
    simp [P,projector,Matrix.mul_assoc, ← Matrix.mul_assoc Fᵀ F,h]
  have tr {b c : ℕ} (Z : Mat b c) : frobSq Zᵀ = frobSq Z := by
    simp only [frobSq,transpose_transpose,trace_mul_comm Z Zᵀ]
  have hb := frobSplit Aᵀ P hs hi
  have he : frobSq (Fᵀ*A) = frobSq (Aᵀ*P) := by
    rw [← tr (Fᵀ*A),transpose_mul,transpose_transpose]
    simp only [P,projector,← Matrix.mul_assoc, rightFrameEnergy _ _ h]
  linarith [tr A,frob_nonneg (Aᵀ*(1-P))]

/-- The tail energy cannot increase under the orthogonal compressions in
preceding modes. Here H = A_jᵀ, so Fᵀ acts on the long dimension. -/
theorem tailCompress {m n k r : ℕ} (H : Mat m n) (F : Mat m k)
    (hF : Fᵀ * F = 1) (hr : r ≤ n) :
    Projection.tailEnergy (Fᵀ * H) r ≤ Projection.tailEnergy H r := by
  obtain ⟨W,hw⟩ := exists_rightBasis H
  let V := firstCols W hr
  let P := projector V
  have rk : (Fᵀ * H * P).rank ≤ r := by
    dsimp [P,projector]; rw [← Matrix.mul_assoc]
    exact (Matrix.rank_mul_le_right _ _).trans (by simpa using Matrix.rank_le_card_height Vᵀ)
  have h₁ := tailEnergy_le_error (Fᵀ*H) (Fᵀ*H*P) hr rk
  have id' : Fᵀ * H - Fᵀ * H * P = Fᵀ * (H * (1-P)) := by
    simp [Matrix.mul_sub, Matrix.mul_assoc]
  rw [id'] at h₁
  exact (h₁.trans (frobCompress _ _ hF)).trans_eq (basisResidualTail _ _ _ hw)

end RPHOSVD.Tensor
