import RPHOSVD.MixedTruncation
import RPHOSVD.MixedCoupling
import RPHOSVD.MixedRecovery
import RPHOSVD.Refined

/-! End-to-end finite-u mixed-precision projection theorem. -/
namespace RPHOSVD.Mixed
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section

private theorem mixed_frob_eq {a b : ℕ} (A : Mat a b) : frobSq A = Projection.frobSq A := by
  rw [Projection.frobSq_cols]
  exact Finset.sum_comm

private theorem ideal_split {m n r t : ℕ} (H : Mat m n) (V : Mat n t) (U : Mat t t)
    (hV : Vᵀ * V = 1) (hr : r ≤ t) (ht : t ≤ n) (hU : Projection.RightBasis (H*V) U) :
    frobSq (H * (1-V*Vᵀ)) + tailEnergy (H*(V*Vᵀ)) r =
    Projection.frobSq (H - (H*V)*Projection.projector (Projection.firstCols U hr)*Vᵀ) := by
  let A := H * V
  let P := V * Vᵀ
  let E := Projection.projector (Projection.firstCols U hr)
  let M := A * E * Vᵀ
  have hs : Pᵀ = P := by simp [P, transpose_mul]
  have hi : P * P = P := by simp [P, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V, hV]
  have hMP : M * P = M := by simp [M, P, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V, hV]
  have hHP : A * Vᵀ = H * P := by simp [A, P, Matrix.mul_assoc]
  have h := Projection.frobSplit (H - M) P hs hi
  have hcompl : (H - M) * (1 - P) = H * (1 - P) := by
    rw [Matrix.sub_mul, Matrix.mul_sub M, Matrix.mul_one, hMP, sub_self, sub_zero]
  have hret : (H - M) * P = (A - A * E) * Vᵀ := by rw [Matrix.sub_mul, hMP, Matrix.sub_mul, hHP]
  rw [hcompl, hret, Projection.rightFrameEnergy _ _ hV] at h
  have hw := Projection.basisResidualTail A U hr hU
  change Projection.frobSq (A * (1-E)) = _ at hw
  rw [Matrix.mul_sub, Matrix.mul_one] at hw
  rw [hw, ← Projection.tail_appendFrame A V hV hr ht, hHP] at h
  rw [mixed_frob_eq]
  exact h.symm

/-- Theorem 5.1, explicit finite-roundoff bound and positive definiteness of
the symmetrized computed Gram. -/
theorem mixedProjection : MixedProjectionBound := by
  intro m n s r t H S Y V X G η ε u h
  refine ⟨gram_posDef_of_run h, ?_⟩
  intro R Vr hout
  let ds := productBudget u S H
  let θ := theta η (productBudget u H (V * inverseScales Y t)) (productBudget u Xᵀ X)
  let b := η * ((ε+ds) / Real.sqrt (1-η)) + 3 * Real.sqrt (1+η) * ds
  have hr := mixed_target_le_retained h
  have hrpos : 0 < r := h.rank_pos
  have hinj := noisy_retained_injective h
  obtain ⟨D,hD,hVD,hcomp,hYD⟩ := noisy_complement h
  obtain ⟨Q,hQ,hQR⟩ := Projection.exists_rangeFrame _ hinj
  obtain ⟨U,hU⟩ := Projection.exists_rightBasis (H*V)
  have hds : 0 ≤ ds := (norm_nonneg _).trans (rounded_product_opNorm S H Y u h.roundoff_pos.le h.long_product h.sketch)
  have hp : 0 < 1+η := by linarith [h.distortion_nonneg]
  have hm : 0 < 1-η := sub_pos.mpr h.distortion_lt
  have hs := noisy_retained_sv h hrpos hr
  have hpos : 0 ≤ (sigma Y (r-1) - ds) / Real.sqrt (1+η) := by
    apply div_nonneg _ (Real.sqrt_nonneg _)
    dsimp [ds]
    linarith [h.target_retained,h.sketch_small,h.threshold_pos]
  have hsq := pow_le_pow_left₀ hpos hs 2
  rw [div_pow, Real.sq_sqrt hp.le] at hsq
  have hd := pow_le_pow_left₀ (norm_nonneg _) (mixedDiscardNorm h D hD hYD) 2
  rw [div_pow, Real.sq_sqrt hm.le] at hd
  have hsep := hd.trans h.separated
  have hgap : Projection.opNorm (H * D)^2 ≤ Projection.sigma (H * V) (r-1)^2 / 2 := by
    change ‖H * D‖^2 ≤ sigma (H*V) (r-1)^2 / 2
    rw [mul_comm 2 (1+η), ← div_div] at hsep
    exact hsep.trans (div_le_div_of_nonneg_right hsq (by norm_num))
  have hi := Projection.retainedSubspace H V D Q U hr h.rank_pos h.retained_basis.1 h.retained_basis.2.1 hD hVD
    hcomp hinj hQ hQR hU hgap
  have hcouple := noisyCoupling h D Q hD hVD hQ hQR hYD
  have hc := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcouple 2)
    (by positivity : 0 ≤ 2*(r:ℝ))
  change 2*(r:ℝ)*Projection.opNorm (Qᵀ*H*D)^2 ≤ 2*(r:ℝ)*b^2 at hc
  have hi' := hi.trans (add_le_add (le_refl (Projection.tailEnergy H r)) hc)
  rw [← ideal_split H V U h.retained_basis.2.1 hr h.retained_basis.1 hU] at hi'
  have he := error_reduction_of_run h hout
  change _ ≤ frobSq (H*(1-V*Vᵀ)) + tailEnergy (H*(V*Vᵀ)) r + (2*θ/(1-θ))*tailEnergy H r at he
  change _ ≤ tailEnergy H r + 2*(r:ℝ)*b^2 at hi'
  change _ ≤ (1+θ)/(1-θ)*tailEnergy H r + 2*(r:ℝ)*b^2
  have hdθ : 0 < 1-θ := sub_pos.mpr h.gram_small
  have hratio : (1+θ)/(1-θ) = 1 + 2*θ/(1-θ) := by field_simp; ring
  rw [hratio, add_mul, one_mul]
  linarith only [he,hi']

end
end RPHOSVD.Mixed
