import Mathlib

/-! Orthogonal projection identities underlying the two tensor schedules. The identification
of tensor mode multiplication with such orthogonal projections is a separate bridge. -/
namespace RPHOSVD.Tensor
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem orthogonalStep (P : E →ₗ[ℝ] E) (hs : P.IsSymmetric)
    (hi : ∀ x, P (P x) = P x) (x : E) : ‖x - P x‖^2 = ‖x‖^2 - ‖P x‖^2 := by
  have inner' : ⟪x, P x⟫ = ‖P x‖^2 := by
    rw [← real_inner_self_eq_norm_sq, hs x (P x), hi]
  rw [norm_sub_sq_real, inner']; ring

/-- Telescoping of energy for *current* residuals, with no commutation hypothesis. -/
theorem sequentialEnergy (P : ℕ → E →ₗ[ℝ] E) (x : ℕ → E)
    (hs : ∀ j, (P j).IsSymmetric) (hi : ∀ j y, P j (P j y) = P j y)
    (step : ∀ j, x (j+1) = P j (x j)) (d : ℕ) :
    ‖x 0‖^2 - ‖x d‖^2 = ∑ j ∈ Finset.range d, ‖x j - x (j+1)‖^2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ← ih, step d, orthogonalStep _ (hs d) (hi d)]
    ring

end RPHOSVD.Tensor
