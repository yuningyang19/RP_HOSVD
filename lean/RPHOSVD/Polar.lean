import RPHOSVD.Mixed
import RPHOSVD.KyFan

/-! Near-orthogonality of a rectangular factor and proximity to its polar frame. -/
namespace RPHOSVD.Mixed
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section
variable {m n t : ℕ}

private theorem frameContract {p q} (A : Mat p q) (hA : Aᵀ * A = 1) : ‖A‖ ≤ 1 := by
  have g := Matrix.l2_opNorm_conjTranspose_mul_self A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hA, ← Matrix.diagonal_one,
    Matrix.l2_opNorm_diagonal] at g
  have h : ‖(1 : Fin q → ℝ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun _ => by simp)
  change ‖(fun _ : Fin q => (1 : ℝ))‖ ≤ 1 at h
  rw [g] at h
  exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa [sq] using h)

private theorem contractBoth {p q d e} (U : Mat p q) (A : Mat q d) (W : Mat d e)
    (hU : ‖U‖ ≤ 1) (hW : ‖W‖ ≤ 1) : ‖U * A * W‖ ≤ ‖A‖ := by
  calc
    _ ≤ ‖U*A‖ * ‖W‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖U‖ * ‖A‖) * ‖W‖ := mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * ‖A‖) * 1 := mul_le_mul (mul_le_mul_of_nonneg_right hU (norm_nonneg _)) hW (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- A rectangular near-isometry has an orthonormal polar frame at distance at
most its Gram defect. This includes the zero-column case. -/
theorem polarProximity (X : Mat m t) (h : ‖Xᵀ * X - 1‖ < 1/2) :
    ∃ Q : Mat m t, Qᵀ * Q = 1 ∧ ‖X-Q‖ ≤ ‖Xᵀ * X-1‖ := by
  obtain ⟨W,hW⟩ := Projection.exists_rightBasis X
  let d := fun i : Fin t => sigma X i.val
  let defect := Xᵀ * X - 1
  have eig : Xᵀ * X * W = W * diagonal (fun i => d i ^ 2) := hW.2.2
  have hWn := frameContract W hW.1
  have hWt : ‖Wᵀ‖ ≤ 1 := by rwa [transpose_opNorm]
  have diag_defect : Wᵀ * defect * W = diagonal (fun i => d i ^ 2 - 1) := by
    rw [Matrix.mul_assoc, show defect * W = W * diagonal (fun i => d i ^ 2) - W by
      rw [show defect = Xᵀ * X - 1 from rfl, Matrix.sub_mul, eig, Matrix.one_mul]]
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hW.1, Matrix.one_mul, ← Matrix.diagonal_one, ← Matrix.diagonal_sub]
  have bound := contractBoth Wᵀ defect W hWt hWn
  rw [diag_defect, Matrix.l2_opNorm_diagonal] at bound
  have hd (i : Fin t) : |d i ^ 2 - 1| ≤ ‖defect‖ :=
    (norm_le_pi_norm (fun j => d j ^ 2 - 1) i).trans bound
  have hp (i : Fin t) : 0 < d i := by
    have hn := X.toEuclideanLin.singularValues_nonneg i.val
    change 0 ≤ d i at hn
    have hd' := neg_le_of_abs_le (hd i)
    change ‖defect‖ < 1/2 at h
    by_contra! hn'
    have eq := le_antisymm hn' hn
    rw [eq] at hd'
    linarith
  let D := diagonal d
  let J := diagonal (fun i => (d i)⁻¹)
  let U := X * W * J
  have hJD : J * D = 1 := by simp [J, D, diagonal_mul_diagonal, (hp _).ne']
  have hDJ : D * J = 1 := by simp [J, D, diagonal_mul_diagonal, (hp _).ne']
  have hw : Xᵀ * (X * W) = W * (D*D) := by
    simpa [← Matrix.mul_assoc Xᵀ, D, diagonal_mul_diagonal, sq] using eig
  have hXU : Xᵀ * U = W * D := by
    change Xᵀ * ((X * W) * J) = _
    rw [← Matrix.mul_assoc, hw, Matrix.mul_assoc, Matrix.mul_assoc D, hDJ, Matrix.mul_one]
  have hU : Uᵀ * U = 1 := by
    change (X * W * J)ᵀ * U = _
    rw [transpose_mul, transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, hXU,
      ← Matrix.mul_assoc Wᵀ, hW.1, Matrix.one_mul]
    simpa [J] using hJD
  have hUD : U * D = X * W := by simp [U, Matrix.mul_assoc, hJD]
  have hX : U * D * Wᵀ = X := by rw [hUD, Matrix.mul_assoc, hW.2.1, Matrix.mul_one]
  let Q := U * Wᵀ
  refine ⟨Q, ?_, ?_⟩
  · simp [Q, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hU, hW.2.1]
  · have factor : X-Q = U * diagonal (fun i => d i - 1) * Wᵀ := by
      rw [show diagonal (fun i => d i - 1) = D-1 by
        change diagonal (fun i => d i - 1) = diagonal d - 1
        rw [← Matrix.diagonal_one, Matrix.diagonal_sub]]
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hX]
    rw [factor]
    refine (contractBoth _ _ _ (frameContract U hU) hWt).trans ?_
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    change |d i - 1| ≤ ‖defect‖
    apply le_trans _ (hd i)
    have hd1 : 1 ≤ d i + 1 := by linarith [hp i]
    calc
      _ = |d i-1| * 1 := (mul_one _).symm
      _ ≤ |d i-1| * (d i+1) := mul_le_mul_of_nonneg_left hd1 (abs_nonneg _)
      _ = _ := by rw [← abs_of_nonneg (show 0 ≤ d i+1 by linarith) , ← abs_mul]; congr 1; ring

/-- A lower quadratic bound gives invertibility of the square factor and a
uniform operator-norm bound for its inverse. -/
theorem inverseFactorBound (R : Mat t t) (c : ℝ) (hc : 0 < c)
    (hl : ∀ z : EuclideanSpace ℝ (Fin t),
      c * ‖z‖^2 ≤ ‖R.toEuclideanLin z‖^2) :
    IsUnit R.det ∧ ‖R⁻¹‖ ≤ 1 / Real.sqrt c := by
  have hs := Real.sqrt_pos.mpr hc
  have lower (z : EuclideanSpace ℝ (Fin t)) :
      Real.sqrt c * ‖z‖ ≤ ‖R.toEuclideanLin z‖ := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    simpa only [mul_pow, Real.sq_sqrt hc.le] using hl z
  have hinj : Function.Injective R.mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    let v : EuclideanSpace ℝ (Fin t) := WithLp.toLp 2 z
    have h0 : R.toEuclideanLin v = 0 := WithLp.ofLp_injective 2 hz
    have hlow := lower v
    rw [h0, norm_zero] at hlow
    have hzero : ‖v‖ = 0 := le_antisymm (by by_contra! hn; exact (mul_pos hs hn).not_ge hlow) (norm_nonneg _)
    exact congrArg WithLp.ofLp (norm_eq_zero.mp hzero)
  have hu := R.isUnit_iff_isUnit_det.mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  refine ⟨hu, ?_⟩
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hh := lower (R⁻¹.toEuclideanLin x)
  have hid : R.toEuclideanLin (R⁻¹.toEuclideanLin x) = x := by
    change (R.toEuclideanLin ∘ₗ R⁻¹.toEuclideanLin) x = x
    rw [← Matrix.toLpLin_mul 2 2 2, R.mul_nonsing_inv hu]; simp
  rw [hid] at hh
  change ‖R⁻¹.toEuclideanLin x‖ ≤ _
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hs]
  rwa [mul_comm]

end
end RPHOSVD.Mixed
