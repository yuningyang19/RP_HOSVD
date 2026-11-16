import RPHOSVD.Mixed

/-! Transfer of retained/discarded orthogonality from the rounded sketch. -/
namespace RPHOSVD.Mixed
open Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
noncomputable section
variable {m n s r t k : ℕ} {H : Mat m n} {S : Mat s m} {Y : Mat s n}
  {V : Mat n t} {X : Mat m t} {G : Mat t t} {η ε u : ℝ}

private abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

private theorem frameNorm {a b} (A : Mat a b) (h : Aᵀ * A = 1) (v : Euc b) :
    ‖A.toEuclideanLin v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change ∑ i, ((A *ᵥ v.ofLp) i)^2 = ∑ i, (v.ofLp i)^2
  simp only [sq]
  change (A *ᵥ v.ofLp) ⬝ᵥ (A *ᵥ v.ofLp) = v.ofLp ⬝ᵥ v.ofLp
  calc
    _ = v.ofLp ⬝ᵥ ((Aᵀ * A) *ᵥ v.ofLp) := by symm; rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    _ = _ := by rw [h, one_mulVec]

private theorem applyMul {a b c} (A : Mat a b) (B : Mat b c) (z : Euc c) :
    (A * B).toEuclideanLin z = A.toEuclideanLin (B.toEuclideanLin z) := by
  rw [Matrix.toLpLin_mul 2 2 2]; rfl

private theorem applyBound {a b} (A : Mat a b) (x : Euc b) :
    ‖A.toEuclideanLin x‖ ≤ ‖A‖ * ‖x‖ := Matrix.l2_opNorm_mulVec A x

private theorem embedNorm (h : MixedRun H S Y V X G η ε u r) (x : Euc n) :
    Real.sqrt (1-η) * ‖H.toEuclideanLin x‖ ≤ ‖S.toEuclideanLin (H.toEuclideanLin x)‖ ∧
    ‖S.toEuclideanLin (H.toEuclideanLin x)‖ ≤ Real.sqrt (1+η) * ‖H.toEuclideanLin x‖ := by
  have he := h.embedding x
  dsimp only at he
  constructor
  · apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    simpa only [mul_pow, Real.sq_sqrt (sub_nonneg.mpr h.distortion_lt.le)] using he.1
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    simpa only [mul_pow, Real.sq_sqrt (by linarith [h.distortion_nonneg] : 0 ≤ 1+η)] using he.2

private theorem errorBound (h : MixedRun H S Y V X G η ε u r) (v : Euc n) :
    ‖(Y - S * H).toEuclideanLin v‖ ≤ productBudget u S H * ‖v‖ :=
  (applyBound _ _).trans (mul_le_mul_of_nonneg_right
    (rounded_product_opNorm S H Y u h.roundoff_pos.le h.long_product h.sketch) (norm_nonneg _))

/-- The original discarded block has norm at most the noisy cutoff divided by
the lower embedding scale. -/
theorem mixedDiscardNorm (h : MixedRun H S Y V X G η ε u r) (D : Mat n k)
    (hD : Dᵀ * D = 1) (hYD : ‖Y * D‖ ≤ ε) :
    ‖H * D‖ ≤ (ε + productBudget u S H) / Real.sqrt (1-η) := by
  have hds := (norm_nonneg _).trans (rounded_product_opNorm S H Y u h.roundoff_pos.le h.long_product h.sketch)
  have hε := h.threshold_pos
  have hs := Real.sqrt_pos.mpr (sub_pos.mpr h.distortion_lt)
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  let d := D.toEuclideanLin z
  have he := (embedNorm h d).1
  have herr := errorBound h d
  have hdn : ‖d‖ = ‖z‖ := frameNorm D hD z
  have hyd := (applyBound (Y*D) z).trans (mul_le_mul_of_nonneg_right hYD (norm_nonneg _))
  rw [applyMul] at hyd
  have hsbound := norm_sub_le (Y.toEuclideanLin d) ((Y-S*H).toEuclideanLin d)
  rw [map_sub, LinearMap.sub_apply, sub_sub_cancel, applyMul] at hsbound
  change ‖(H * D).toEuclideanLin z‖ ≤ _
  rw [applyMul, div_mul_eq_mul_div, le_div_iff₀ hs]
  rw [hdn, map_sub, LinearMap.sub_apply, applyMul] at herr
  change ‖H.toEuclideanLin d‖ * _ ≤ _
  linarith only [he, hsbound, herr, hyd, show ‖Y.toEuclideanLin d‖ ≤ ε * ‖z‖ from hyd,
    show (ε + productBudget u S H) * ‖z‖ = ε * ‖z‖ + productBudget u S H * ‖z‖ by ring]

private theorem embedInner (h : MixedRun H S Y V X G η ε u r) (x y : Euc n) :
    |⟪H.toEuclideanLin x, H.toEuclideanLin y⟫ -
      ⟪S.toEuclideanLin (H.toEuclideanLin x), S.toEuclideanLin (H.toEuclideanLin y)⟫| ≤
      η * ‖H.toEuclideanLin x‖ * ‖H.toEuclideanLin y‖ := by
  let A := H.toEuclideanLin x
  let B := H.toEuclideanLin y
  change |⟪A,B⟫ - ⟪S.toEuclideanLin A,S.toEuclideanLin B⟫| ≤ η * ‖A‖ * ‖B‖
  by_cases hx : A = 0
  · simp [hx]
  by_cases hy : B = 0
  · simp [hy]
  have nx := norm_pos_iff.mpr hx
  have ny := norm_pos_iff.mpr hy
  let a := ‖A‖⁻¹ • x
  let b := ‖B‖⁻¹ • y
  have hu : ‖H.toEuclideanLin a‖ = 1 := by
    simp [a, norm_smul, A, hx]
  have hv : ‖H.toEuclideanLin b‖ = 1 := by
    simp [b, norm_smul, B, hy]
  have plus := h.embedding (a+b)
  have minus := h.embedding (a-b)
  simp only [map_add, map_sub, norm_add_sq_real, norm_sub_sq_real, hu, hv] at plus minus
  have normalized :
      |⟪H.toEuclideanLin a,H.toEuclideanLin b⟫ -
        ⟪S.toEuclideanLin (H.toEuclideanLin a),S.toEuclideanLin (H.toEuclideanLin b)⟫| ≤ η :=
    abs_le.mpr ⟨by linarith [plus.2, minus.1], by linarith [plus.1, minus.2]⟩
  simp only [a,b,map_smul,real_inner_smul_left,real_inner_smul_right, ← mul_sub] at normalized
  rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr nx), abs_of_pos (inv_pos.mpr ny)] at normalized
  change ‖B‖⁻¹ * (‖A‖⁻¹ * |⟪A,B⟫ - ⟪S.toEuclideanLin A,S.toEuclideanLin B⟫|) ≤ η at normalized
  calc
    _ = (‖B‖⁻¹ * (‖A‖⁻¹ * |⟪A,B⟫ - ⟪S.toEuclideanLin A,S.toEuclideanLin B⟫|)) * ‖A‖ * ‖B‖ := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right normalized nx.le) ny.le

private theorem retainedLower (h : MixedRun H S Y V X G η ε u r) (c : Euc t) :
    ε * ‖c‖ ≤ ‖(Y*V).toEuclideanLin c‖ := by
  have hgram : (Y*V)ᵀ * (Y*V) = diagonal (fun j : Fin t => sigma Y j.val ^ 2) := by
    rw [transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc Vᵀ Yᵀ Y, Matrix.mul_assoc,
      h.retained_basis.2.2, ← Matrix.mul_assoc, h.retained_basis.2.1, one_mul]
  apply (sq_le_sq₀ (mul_nonneg h.threshold_pos.le (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  change _ ≤ ∑ i, (((Y*V) *ᵥ c.ofLp) i)^2
  simp only [sq]
  change _ ≤ ((Y*V) *ᵥ c.ofLp) ⬝ᵥ ((Y*V) *ᵥ c.ofLp)
  have energy (A : Mat s t) :
      (A *ᵥ c.ofLp) ⬝ᵥ (A *ᵥ c.ofLp) = c.ofLp ⬝ᵥ ((Aᵀ * A) *ᵥ c.ofLp) := by
    symm
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  rw [energy, hgram]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_le_sum
  intro j _
  have hj := (retained_gt Y ε h.retained_basis.1 h.retained_count j).le
  have hh := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ h.threshold_pos.le hj 2) (sq_nonneg (c j))
  simpa [sq, mul_comm, mul_left_comm, mul_assoc] using hh

private theorem sketchOrthogonal (h : MixedRun H S Y V X G η ε u r) (D : Mat n k)
    (hVD : Vᵀ * D = 0) (c : Euc t) (z : Euc k) :
    ⟪(Y*V).toEuclideanLin c,(Y*D).toEuclideanLin z⟫ = 0 := by
  have htranspose := congrArg Matrix.transpose h.retained_basis.2.2
  simp only [transpose_mul, transpose_transpose, diagonal_transpose] at htranspose
  have cross : (Y*V)ᵀ * (Y*D) = 0 := by
    rw [transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc Vᵀ Yᵀ Y, htranspose,
      Matrix.mul_assoc, hVD, Matrix.mul_zero]
  rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial, ← applyMul, cross]
  simp

/-- Noisy coupling estimate for an arbitrary orthonormal coordinate frame on
the retained original range. The rounded sketch error enters with coefficient
three under the half-threshold condition. -/
theorem noisyCoupling (h : MixedRun H S Y V X G η ε u r) (D : Mat n k) (Q : Mat m t)
    (hD : Dᵀ * D = 1) (hVD : Vᵀ * D = 0) (hQ : Qᵀ * Q = 1)
    (hrange : LinearMap.range Q.mulVecLin = LinearMap.range (H * V).mulVecLin)
    (hYD : ‖Y * D‖ ≤ ε) :
    ‖Qᵀ * H * D‖ ≤ η * ((ε + productBudget u S H) / Real.sqrt (1-η)) +
      3 * Real.sqrt (1+η) * productBudget u S H := by
  let ds := productBudget u S H
  let a := Real.sqrt (1+η)
  let b := (ε + ds) / Real.sqrt (1-η)
  have hds : 0 ≤ ds := (norm_nonneg _).trans (rounded_product_opNorm S H Y u h.roundoff_pos.le h.long_product h.sketch)
  have hε := h.threshold_pos
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := div_nonneg (add_nonneg hε.le hds) (Real.sqrt_nonneg _)
  have hη := h.distortion_nonneg
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (show 0 ≤ η * b + 3 * a * ds by positivity)
  intro z
  let d := D.toEuclideanLin z
  let y := H.toEuclideanLin d
  let w := Qᵀ.toEuclideanLin y
  change ‖(Qᵀ * H * D).toEuclideanLin z‖ ≤ _
  rw [applyMul, applyMul]
  change ‖w‖ ≤ (η * b + 3*a*ds) * ‖z‖
  by_cases hw : w = 0
  · rw [hw, norm_zero]; positivity
  have hwpos := norm_pos_iff.mpr hw
  have hmem : Q.mulVecLin w.ofLp ∈ LinearMap.range (H * V).mulVecLin := hrange ▸ ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ := hmem
  let c : Euc t := WithLp.toLp 2 c₀
  let x := V.toEuclideanLin c
  let v := H.toEuclideanLin x
  have hv : v = Q.toEuclideanLin w := by
    apply WithLp.ofLp_injective 2
    change H *ᵥ (V *ᵥ c₀) = Q *ᵥ w.ofLp
    rwa [mulVec_mulVec]
  have hvn : ‖v‖ = ‖w‖ := hv ▸ frameNorm Q hQ w
  have hxn : ‖x‖ = ‖c‖ := frameNorm V h.retained_basis.2.1 c
  have hdn : ‖d‖ = ‖z‖ := frameNorm D hD z
  let E := Y-S*H
  have decomp (f : Euc n) : S.toEuclideanLin (H.toEuclideanLin f) =
      Y.toEuclideanLin f - E.toEuclideanLin f := by
    simp [E]
  have eX := errorBound h x
  change ‖E.toEuclideanLin x‖ ≤ ds * ‖x‖ at eX
  rw [hxn] at eX
  have eD := errorBound h d
  change ‖E.toEuclideanLin d‖ ≤ ds * ‖d‖ at eD
  rw [hdn] at eD
  have sv := (embedNorm h x).2
  change ‖S.toEuclideanLin v‖ ≤ a * ‖v‖ at sv
  rw [hvn] at sv
  have yc := retainedLower h c
  rw [applyMul] at yc
  change ε * ‖c‖ ≤ ‖Y.toEuclideanLin x‖ at yc
  have hyc : Y.toEuclideanLin x = S.toEuclideanLin v + E.toEuclideanLin x := by
    change _ = S.toEuclideanLin (H.toEuclideanLin x) + _
    rw [decomp]; abel
  have hc : ε * ‖c‖ ≤ 2 * a * ‖w‖ := by
    rw [hyc] at yc
    have hsmall := mul_le_mul_of_nonneg_right h.sketch_small (norm_nonneg c)
    change ds * ‖c‖ ≤ ε / 2 * ‖c‖ at hsmall
    linarith only [yc.trans (norm_add_le _ _), sv, eX, hsmall]
  have yd := (applyBound (Y*D) z).trans (mul_le_mul_of_nonneg_right hYD (norm_nonneg _))
  rw [applyMul] at yd
  have orth := sketchOrthogonal h D hVD c z
  rw [applyMul, applyMul] at orth
  change ⟪Y.toEuclideanLin x,Y.toEuclideanLin d⟫ = 0 at orth
  have innerEq :
      ⟪S.toEuclideanLin v,S.toEuclideanLin y⟫ =
        -⟪E.toEuclideanLin x,Y.toEuclideanLin d⟫ - ⟪S.toEuclideanLin v,E.toEuclideanLin d⟫ := by
    change ⟪_, S.toEuclideanLin (H.toEuclideanLin d)⟫ = _
    rw [decomp d, inner_sub_right]
    congr 1
    change ⟪S.toEuclideanLin (H.toEuclideanLin x),_⟫ = _
    rw [decomp x, inner_sub_left, orth, zero_sub]
  have hsk : |⟪S.toEuclideanLin v,S.toEuclideanLin y⟫| ≤ 3*a*ds*‖w‖*‖z‖ := by
    rw [innerEq]
    rw [sub_eq_add_neg]
    apply (abs_add_le _ _).trans
    simp only [abs_neg]
    have h₁ := (abs_real_inner_le_norm (E.toEuclideanLin x) (Y.toEuclideanLin d)).trans
      (mul_le_mul eX yd (norm_nonneg _) (mul_nonneg hds (norm_nonneg _)))
    have h₂ := (abs_real_inner_le_norm (S.toEuclideanLin v) (E.toEuclideanLin d)).trans
      (mul_le_mul sv eD (norm_nonneg _) (mul_nonneg ha (norm_nonneg _)))
    have h₃ := mul_le_mul_of_nonneg_right hc (mul_nonneg hds (norm_nonneg z))
    linarith only [h₁, h₂, h₃]
  have hd := (applyBound (H*D) z).trans (mul_le_mul_of_nonneg_right (mixedDiscardNorm h D hD hYD) (norm_nonneg _))
  rw [applyMul] at hd
  have hh := embedInner h x d
  change |⟪v,y⟫ - ⟪S.toEuclideanLin v,S.toEuclideanLin y⟫| ≤ η * ‖v‖ * ‖y‖ at hh
  rw [hvn] at hh
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hd (mul_nonneg hη (norm_nonneg w)))
  have hself : ⟪v,y⟫ = ‖w‖^2 := by
    rw [hv, ← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    exact real_inner_self_eq_norm_sq w
  rw [hself] at hh'
  apply le_of_mul_le_mul_left (a := ‖w‖) _ hwpos
  linarith only [le_of_abs_le hh', le_of_abs_le hsk]

end
end RPHOSVD.Mixed
