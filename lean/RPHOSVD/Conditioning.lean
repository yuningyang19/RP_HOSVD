import Mathlib

/-! Conditioning of the retained sketch-whitened matrix in RP-HOSVD. -/

namespace RPHOSVD

open Matrix
open scoped MatrixOrder RealInnerProductSpace

namespace Conditioning

/-- The spectral condition number for full-column-rank rectangular matrices with
a nonempty column index: largest singular value divided by the smallest. -/
noncomputable def conditionNumber₂ {m t : ℕ} (X : Matrix (Fin m) (Fin t) ℝ) : ℝ :=
  (Matrix.toLpLin 2 2 X).singularValues 0 /
    (Matrix.toLpLin 2 2 X).singularValues (t - 1)

/-- Coordinates obtained by retaining the columns of V indexed by e and dividing
them by the corresponding singular values. -/
noncomputable def whitening {n q t : ℕ} (V : Matrix (Fin n) (Fin q) ℝ)
    (σ : Fin q → ℝ) (e : Fin t ↪ Fin q) : Matrix (Fin n) (Fin t) ℝ :=
  V.submatrix id e * diagonal (fun i ↦ (σ (e i))⁻¹)

private theorem gram_form {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin n → ℝ) :
    y ⬝ᵥ ((Aᵀ * A) *ᵥ y) = (A *ᵥ y) ⬝ᵥ (A *ᵥ y) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

private theorem euclidean_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp x) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [sq, dotProduct]

private theorem spectral_bounds {m t : ℕ} (X : Matrix (Fin m) (Fin t) ℝ)
    {a b : ℝ}
    (hb : ∀ y, a * (y ⬝ᵥ y) ≤ (X *ᵥ y) ⬝ᵥ (X *ᵥ y) ∧
      (X *ᵥ y) ⬝ᵥ (X *ᵥ y) ≤ b * (y ⬝ᵥ y)) (i : Fin t) :
    a ≤ (Matrix.toLpLin 2 2 X).singularValues i ^ 2 ∧
    (Matrix.toLpLin 2 2 X).singularValues i ^ 2 ≤ b := by
  let L := Matrix.toLpLin 2 2 X
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin t)) = t := by simp
  let v := L.isSymmetric_adjoint_comp_self.eigenvectorBasis hd i
  have hv : ‖v‖ = 1 := (L.isSymmetric_adjoint_comp_self.eigenvectorBasis hd).orthonormal.1 i
  have hev : (LinearMap.adjoint L ∘ₗ L) v = (L.singularValues i ^ 2) • v := by
    rw [L.sq_singularValues_fin hd]
    exact L.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hd i
  have hnorm : ‖L v‖ ^ 2 = L.singularValues i ^ 2 := by
    calc
      _ = ⟪L v, L v⟫ := (real_inner_self_eq_norm_sq _).symm
      _ = ⟪(LinearMap.adjoint L ∘ₗ L) v, v⟫ := (L.adjoint_inner_left v (L v)).symm
      _ = _ := by rw [hev, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]; ring
  have h := hb (WithLp.ofLp v)
  change a * (WithLp.ofLp v ⬝ᵥ WithLp.ofLp v) ≤
      WithLp.ofLp (L v) ⬝ᵥ WithLp.ofLp (L v) ∧ _ at h
  change _ ∧ WithLp.ofLp (L v) ⬝ᵥ WithLp.ofLp (L v) ≤ _ at h
  rw [← euclidean_sq, ← euclidean_sq, hv, hnorm] at h
  simpa [L] using h

/-- Manuscript Lemma on conditioning. The equality specifying the range of e
selects exactly the singular directions above ε. The factorization and the two
orthogonality identities are the compact SVD data, and the final hypothesis is
the realized embedding on the column space of H. -/
theorem conditioning {m n s q t : ℕ}
    (H : Matrix (Fin m) (Fin n) ℝ) (S : Matrix (Fin s) (Fin m) ℝ)
    (U : Matrix (Fin s) (Fin q) ℝ) (V : Matrix (Fin n) (Fin q) ℝ)
    (σ : Fin q → ℝ) (e : Fin t ↪ Fin q) (ε η : ℝ)
    (ht : 0 < t) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hη' : η < 1)
    (hsel : Set.range e = {i | ε < σ i})
    (hsvd : S * H = U * diagonal σ * Vᵀ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hose : ∀ z, (1 - η) * ((H *ᵥ z) ⬝ᵥ (H *ᵥ z)) ≤
        (S *ᵥ (H *ᵥ z)) ⬝ᵥ (S *ᵥ (H *ᵥ z)) ∧
      (S *ᵥ (H *ᵥ z)) ⬝ᵥ (S *ᵥ (H *ᵥ z)) ≤
        (1 + η) * ((H *ᵥ z) ⬝ᵥ (H *ᵥ z))) :
    let X := H * whitening V σ e
    X.rank = t ∧
      (1 / (1 + η) : ℝ) • (1 : Matrix (Fin t) (Fin t) ℝ) ≤ Xᵀ * X ∧
      Xᵀ * X ≤ (1 / (1 - η) : ℝ) • (1 : Matrix (Fin t) (Fin t) ℝ) ∧
      conditionNumber₂ X ≤ Real.sqrt ((1 + η) / (1 - η)) := by
  classical
  let X := H * whitening V σ e
  let W := U.submatrix id e
  have hpos (j : Fin t) : σ (e j) ≠ 0 := by
    have hm : e j ∈ Set.range e := ⟨j, rfl⟩
    rw [hsel] at hm
    exact (lt_of_le_of_lt hε hm).ne'
  have hsv : (S * H) * V = U * diagonal σ := by
    rw [hsvd, Matrix.mul_assoc, hV, Matrix.mul_one]
  have hSX : S * X = W := by
    change S * (H * (V.submatrix id e * diagonal _)) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    have hr : (S * H) * V.submatrix id e = ((S * H) * V).submatrix id e := rfl
    rw [hr, hsv]
    ext i j
    simp [W, mul_diagonal, hpos, submatrix_apply]
  have hW : Wᵀ * W = 1 := by
    have hr : Wᵀ * W = (Uᵀ * U).submatrix e e := rfl
    rw [hr, hU, submatrix_one _ e.injective]
  have hunit (y : Fin t → ℝ) : (W *ᵥ y) ⬝ᵥ (W *ᵥ y) = y ⬝ᵥ y := by
    rw [← gram_form, hW, one_mulVec]
  have hbound (y : Fin t → ℝ) :
      1 / (1 + η) * (y ⬝ᵥ y) ≤ (X *ᵥ y) ⬝ᵥ (X *ᵥ y) ∧
      (X *ᵥ y) ⬝ᵥ (X *ᵥ y) ≤ 1 / (1 - η) * (y ⬝ᵥ y) := by
    have h := hose (whitening V σ e *ᵥ y)
    rw [mulVec_mulVec, mulVec_mulVec] at h
    change (1 - η) * _ ≤ ((S * X) *ᵥ y) ⬝ᵥ ((S * X) *ᵥ y) ∧ _ at h
    change _ ∧ ((S * X) *ᵥ y) ⬝ᵥ ((S * X) *ᵥ y) ≤ (1 + η) * _ at h
    rw [hSX, hunit] at h
    constructor
    · rw [one_div_mul_eq_div, div_le_iff₀ (by linarith : 0 < 1 + η)]
      simpa only [mul_comm (1 + η)] using h.2
    · rw [one_div_mul_eq_div, le_div_iff₀ (by linarith : 0 < 1 - η)]
      simpa only [mul_comm (1 - η)] using h.1
  have hHerm : (Xᵀ * X).IsHermitian := by
    simpa using Matrix.isHermitian_conjTranspose_mul_self X
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hinj : Function.Injective X.mulVecLin := by
      apply (LinearMap.ker_eq_bot).mp
      rw [LinearMap.ker_eq_bot']
      intro y hy
      change X *ᵥ y = 0 at hy
      have hz := (hbound y).1
      rw [hy, zero_dotProduct] at hz
      have hp : 0 < 1 / (1 + η) := by positivity
      have hy' : 0 ≤ y ⬝ᵥ y := Finset.sum_nonneg (fun j _ ↦ mul_self_nonneg (y j))
      exact dotProduct_self_eq_zero.mp (by nlinarith)
    change Module.finrank ℝ (LinearMap.range X.mulVecLin) = t
    rw [LinearMap.finrank_range_of_inj hinj]
    simp
  · apply Matrix.le_iff.mpr
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (hHerm.sub (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])))
    intro y
    simpa [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, gram_form] using
      sub_nonneg.mpr (hbound y).1
  · apply Matrix.le_iff.mpr
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])).sub hHerm)
    intro y
    simpa [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, gram_form] using
      sub_nonneg.mpr (hbound y).2
  · let L := Matrix.toLpLin 2 2 X
    have hsmall := (spectral_bounds X hbound ⟨t-1, by omega⟩).1
    have hbig := (spectral_bounds X hbound ⟨0, ht⟩).2
    change 1 / (1 + η) ≤ L.singularValues (t - 1) ^ 2 at hsmall
    change L.singularValues 0 ^ 2 ≤ 1 / (1 - η) at hbig
    have hp : 0 < L.singularValues (t - 1) := by
      have : 0 < 1 / (1 + η) := by positivity
      nlinarith [L.singularValues_nonneg (t - 1)]
    change L.singularValues 0 / L.singularValues (t - 1) ≤ _
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos hp)]
    calc
      _ ≤ 1 / (1 - η) := hbig
      _ = ((1 + η) / (1 - η)) * (1 / (1 + η)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (by positivity)

end Conditioning
end RPHOSVD
