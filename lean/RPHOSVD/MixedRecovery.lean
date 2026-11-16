import RPHOSVD.Mixed
import RPHOSVD.ExactProjection

/-! Relative Gram comparison and transfer of residuals to the recovered matrix. -/
namespace RPHOSVD.Mixed

open Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace MatrixOrder
noncomputable section

private lemma gram_form {m t : ℕ} (X : Mat m t) (z : Fin t → ℝ) :
    z ⬝ᵥ ((Xᵀ * X) *ᵥ z) = ∑ i, ((X *ᵥ z) i)^2 := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, sq]

private lemma abs_form_le {t : ℕ} (F : Mat t t) (z : Fin t → ℝ) :
    |z ⬝ᵥ (F *ᵥ z)| ≤ ‖F‖ * ‖WithLp.toLp 2 z‖^2 := by
  let w : EuclideanSpace ℝ (Fin t) := WithLp.toLp 2 z
  have hinner := abs_real_inner_le_norm w (Matrix.toEuclideanCLM (n := Fin t) (𝕜 := ℝ) F w)
  rw [Matrix.inner_toEuclideanCLM] at hinner
  refine hinner.trans ?_
  have hFw := Matrix.l2_opNorm_mulVec F w
  change ‖Matrix.toEuclideanCLM (n := Fin t) (𝕜 := ℝ) F w‖ ≤ ‖F‖ * ‖w‖ at hFw
  simpa [sq, mul_left_comm] using mul_le_mul_of_nonneg_left hFw (norm_nonneg w)

variable {m n s r t : ℕ} {H : Mat m n} {S : Mat s m} {Y : Mat s n}
    {V : Mat n t} {X : Mat m t} {G : Mat t t} {η ε u : ℝ}

/-- Relative comparison of the two Gram quadratic forms, for every vector in the
retained coordinates, derived from the three actual rounded products. -/
theorem relative_gram_forms (h : MixedRun H S Y V X G η ε u r) (z : Fin t → ℝ) :
    let T := V * inverseScales Y t
    let X₀ := H * T
    let θ := theta η (productBudget u H T) (productBudget u Xᵀ X)
    let q := z ⬝ᵥ ((X₀ᵀ * X₀) *ᵥ z)
    (1 - θ) * q ≤ z ⬝ᵥ (G *ᵥ z) ∧ z ⬝ᵥ (G *ᵥ z) ≤ (1 + θ) * q := by
  let T := V * inverseScales Y t
  let X₀ := H * T
  let F := G - X₀ᵀ * X₀
  let dx := productBudget u H T
  let dg := productBudget u Xᵀ X
  let b := 3 * dx / Real.sqrt (1 - η) + dx^2 + dg
  let w : EuclideanSpace ℝ (Fin t) := WithLp.toLp 2 z
  let q := z ⬝ᵥ ((X₀ᵀ * X₀) *ᵥ z)
  have hbudget : ‖F‖ ≤ b := gram_budget_of_run h
  have hb : 0 ≤ b := (norm_nonneg _).trans hbudget
  have hp : 0 < 1 + η := by linarith [h.distortion_nonneg]
  have hcond := (conditioning_of_run h w).1
  change ‖w‖ / (2 * Real.sqrt (1 + η)) ≤ ‖Matrix.toEuclideanLin X₀ w‖ at hcond
  have low : ‖w‖^2 ≤ 4 * (1 + η) * q := by
    have hc := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hcond
    norm_num [div_pow, mul_pow, Real.sq_sqrt hp.le, EuclideanSpace.real_norm_sq_eq] at hc
    dsimp [q]
    rw [gram_form]
    simpa [EuclideanSpace.real_norm_sq_eq, mul_comm] using (div_le_iff₀ (by positivity)).mp hc
  have bound : |z ⬝ᵥ (F *ᵥ z)| ≤ theta η dx dg * q := by
    calc
      _ ≤ ‖F‖ * ‖w‖^2 := abs_form_le _ _
      _ ≤ b * (4 * (1 + η) * q) := mul_le_mul hbudget low (sq_nonneg _) hb
      _ = _ := by dsimp [theta, b]; ring
  have hd : z ⬝ᵥ (F *ᵥ z) = z ⬝ᵥ (G *ᵥ z) - q := by
    simp [F, q, Matrix.sub_mulVec, dotProduct_sub]
  rw [hd, abs_le] at bound
  change (1 - theta η dx dg) * q ≤ _ ∧ _ ≤ (1 + theta η dx dg) * q
  constructor <;> linarith [bound.1, bound.2]

/-- The Loewner order statement before congruence by the retained scale factors. -/
theorem relative_gram_order (h : MixedRun H S Y V X G η ε u r) :
    let T := V * inverseScales Y t
    let A := (H*T)ᵀ * (H*T)
    let θ := theta η (productBudget u H T) (productBudget u Xᵀ X)
    (1-θ) • A ≤ G ∧ G ≤ (1+θ) • A := by
  let T := V * inverseScales Y t
  let A := (H*T)ᵀ * (H*T)
  let θ := theta η (productBudget u H T) (productBudget u Xᵀ X)
  have ha : A.IsHermitian := by
    simpa only [A, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self (H*T)
  have hg : G.IsHermitian := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using h.symmetric
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hg.sub (ha.smul (by rfl)))
    intro z
    have k := (relative_gram_forms h z).1
    change (1-θ) * (z ⬝ᵥ (A *ᵥ z)) ≤ _ at k
    simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul] using sub_nonneg.mpr k
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ((ha.smul (by rfl)).sub hg)
    intro z
    have k := (relative_gram_forms h z).2
    change _ ≤ (1+θ) * (z ⬝ᵥ (A *ᵥ z)) at k
    simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul] using sub_nonneg.mpr k

private theorem cancel_scales (h : MixedRun H S Y V X G η ε u r) :
    inverseScales Y t * scales Y t = 1 := by
  unfold inverseScales scales
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  have hs := retained_gt Y ε h.retained_basis.1 h.retained_count j
  simp [(h.threshold_pos.trans hs).ne']

private lemma energy_by_cols {a b : ℕ} (A : Mat a b) :
    frobSq A = ∑ j, ∑ i, (A i j)^2 := Finset.sum_comm

/-- Congruence and summing the column quadratic forms transfers the recovery
bound to every right multiplier Z, including both competing residual projectors. -/
theorem recovered_frob_comparison (h : MixedRun H S Y V X G η ε u r) {R : Mat t t}
    (hR : Rᵀ * R = G) {k : ℕ} (Z : Mat n k) :
    let θ := theta η (productBudget u H (V * inverseScales Y t)) (productBudget u Xᵀ X)
    let B := R * scales Y t * Vᵀ
    let A := H * (V * Vᵀ)
    (1-θ) * frobSq (A*Z) ≤ frobSq (B*Z) ∧ frobSq (B*Z) ≤ (1+θ) * frobSq (A*Z) := by
  let X₀ := H * (V * inverseScales Y t)
  let C := scales Y t * Vᵀ
  let θ := theta η (productBudget u H (V * inverseScales Y t)) (productBudget u Xᵀ X)
  have hA : H * (V * Vᵀ) * Z = X₀ * (C * Z) := by
    simp only [X₀, C, Matrix.mul_assoc, ← Matrix.mul_assoc (inverseScales Y t) (scales Y t),
      cancel_scales h, Matrix.one_mul]
  have hB : R * scales Y t * Vᵀ * Z = R * (C * Z) := by simp [C, Matrix.mul_assoc]
  dsimp only
  rw [hA, hB, energy_by_cols, energy_by_cols, Finset.mul_sum, Finset.mul_sum]
  have column (j : Fin k) := relative_gram_forms h ((C * Z).col j)
  simp only [← hR, gram_form] at column
  exact ⟨Finset.sum_le_sum (fun j _ => (column j).1), Finset.sum_le_sum (fun j _ => (column j).2)⟩

private theorem energy_eq_projection {a b : ℕ} (A : Mat a b) :
    frobSq A = Projection.frobSq A := by
  rw [energy_by_cols, Projection.frobSq_cols]
  rfl

private theorem residual_orthogonal_frame {a b k : ℕ} (B : Mat a b) (Z : Mat b k)
    (hZ : Zᵀ * Z = 1) :
    frobSq (B * (1 - Z * Zᵀ)) = frobSq B - frobSq (B * Z) := by
  have split := Projection.frobSplit B (Z * Zᵀ)
    (by simp [transpose_mul]) (by simp [Matrix.mul_assoc, ← Matrix.mul_assoc Zᵀ Z, hZ])
  rw [← Matrix.mul_assoc B Z, Projection.rightFrameEnergy (B*Z) Z hZ] at split
  simp only [energy_eq_projection]
  linarith

/-- Any leading right singular frame minimizes the squared Frobenius residual
among rank-r orthogonal projectors. The proof also covers ties. -/
theorem leading_optimal {a b k : ℕ} (B : Mat a b) {W : Mat b k}
    (hw : LeadingRight B W) (Z : Mat b k) (hz : Zᵀ * Z = 1) :
    frobSq (B * (1-W*Wᵀ)) ≤ frobSq (B * (1-Z*Zᵀ)) := by
  have hW : Projection.frobSq (B * W) = ∑ i : Fin k, sigma B i.val ^ 2 := by
    rw [Projection.frobSq, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Bᵀ B,
      hw.2.2, ← Matrix.mul_assoc, hw.2.1, Matrix.one_mul]
    simp [Matrix.trace]
  have hZ := Projection.frameEnergy_le_head B Z hw.1 hz
  rw [residual_orthogonal_frame _ _ hw.2.1, residual_orthogonal_frame _ _ hz,
    energy_eq_projection (B*W), hW, energy_eq_projection (B*Z)]
  exact sub_le_sub_left hZ _

/-- Quasioptimal recovery within the retained subspace for every competing
rank-r projector. Its constant is exactly (1+θ)/(1-θ). -/
theorem retained_projection_residual (h : MixedRun H S Y V X G η ε u r)
    {R : Mat t t} {Vr : Mat n r} (hout : Output Y V G R Vr) (W : Mat n r)
    (hw : Wᵀ * W = 1) :
    let θ := theta η (productBudget u H (V * inverseScales Y t)) (productBudget u Xᵀ X)
    let A := H * (V * Vᵀ)
    frobSq (A * (1 - Vr * Vrᵀ)) ≤
      ((1+θ)/(1-θ)) * frobSq (A * (1-W*Wᵀ)) := by
  let θ := theta η (productBudget u H (V * inverseScales Y t)) (productBudget u Xᵀ X)
  have chain := (recovered_frob_comparison h hout.1 (1-Vr*Vrᵀ)).1.trans <|
    (leading_optimal _ hout.2 W hw).trans <| (recovered_frob_comparison h hout.1 (1-W*Wᵀ)).2
  have hp : 0 < 1-θ := sub_pos.mpr h.gram_small
  dsimp only
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hp).mpr (by simpa [mul_comm] using chain)

/-- Every output direction with positive singular value lies in the retained
right frame. Rank follows from positive definiteness of the rounded Gram and
the strict threshold, including rank-deficient input H. -/
theorem output_nested (h : MixedRun H S Y V X G η ε u r)
    {R : Mat t t} {Vr : Mat n r} (hout : Output Y V G R Vr) :
    (Vr * Vrᵀ) * (V * Vᵀ) = Vr * Vrᵀ := by
  let B := R * scales Y t * Vᵀ
  let P := V * Vᵀ
  have hR : R.rank = t := by
    rw [← Matrix.rank_transpose_mul_self R, hout.1]
    simpa using Matrix.rank_of_isUnit _ (gram_posDef_of_run h).isUnit
  have hrec : B * V * inverseScales Y t = R := by
    have hc : scales Y t * inverseScales Y t = 1 := by
      simpa [scales, inverseScales, mul_comm] using cancel_scales h
    rw [ show B * V = R * scales Y t by simp [B, Matrix.mul_assoc, h.retained_basis.2.1], Matrix.mul_assoc, hc, Matrix.mul_one]
  have hrank : B.rank = t := le_antisymm B.rank_le_height (by
    calc
      t = R.rank := hR.symm
      _ = (B * V * inverseScales Y t).rank := congrArg Matrix.rank hrec.symm
      _ ≤ B.rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _))
  have htarget : r ≤ t := by
    let i : Fin n := ⟨r-1, by have hr := h.rank_le; have hr' := h.rank_pos; omega⟩
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j : Fin n => ε < sigma Y j.val) := by
      intro j hj
      have hji : j ≤ i := Finset.mem_Iic.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le h.target_retained
        ((Matrix.toEuclideanLin Y).singularValues_antitone hji)⟩
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic, ← h.retained_count] at hc
    change r - 1 + 1 ≤ t at hc
    have hr := h.rank_pos
    omega
  have hpos (i : Fin r) : 0 < sigma B i.val := by
    have hr : B.rank = Module.finrank ℝ (LinearMap.range B.toEuclideanLin) :=
      B.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin t) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    exact (B.toEuclideanLin.singularValues_pos_iff_lt_finrank_range).mpr
      (by rw [← hr, hrank]; exact lt_of_lt_of_le i.isLt htarget)
  have hP : Pᵀ = P := by simp [P, transpose_mul]
  have hBP : B * P = B := by
    simp [B, P, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V, h.retained_basis.2.1]
  have hPB : P * Bᵀ = Bᵀ := by simpa [transpose_mul, hP] using congrArg Matrix.transpose hBP
  let D := diagonal (fun i : Fin r => sigma B i.val ^ 2)
  have he : (Bᵀ * B) * Vr = Vr * D := hout.2.2.2
  have hp : (P * Vr) * D = Vr * D := by
    rw [Matrix.mul_assoc, ← he, ← Matrix.mul_assoc P, ← Matrix.mul_assoc P, hPB]
  have hpVr : P * Vr = Vr := by
    ext i j
    have hh := congrArg (fun A : Mat n r => A i j) hp
    simp only [D, mul_diagonal] at hh
    exact mul_right_cancel₀ (pow_ne_zero 2 (hpos j).ne') hh
  have hpVr' : Vrᵀ * P = Vrᵀ := by simpa [transpose_mul, hP] using congrArg Matrix.transpose hpVr
  change _ * P = _
  rw [Matrix.mul_assoc, hpVr']

/-- The mixed proof is reduced to the ideal truncation error, with the
multiplicative correction measured against the original tail energy. -/
theorem error_reduction_of_run (h : MixedRun H S Y V X G η ε u r)
    {R : Mat t t} {Vr : Mat n r} (hout : Output Y V G R Vr) :
    let θ := theta η (productBudget u H (V * inverseScales Y t)) (productBudget u Xᵀ X)
    let P := V * Vᵀ
    frobSq (H - H * (Vr * Vrᵀ)) ≤
      frobSq (H * (1-P)) + tailEnergy (H*P) r + (2*θ/(1-θ)) * tailEnergy H r := by
  let P := V * Vᵀ
  let θ := theta η (productBudget u H (V * inverseScales Y t)) (productBudget u Xᵀ X)
  obtain ⟨W,hW⟩ := Projection.exists_rightBasis (H*P)
  let Z := Projection.firstCols W h.rank_le
  have hZ : Zᵀ * Z = 1 := Projection.firstCols_orthonormal _ _ hW.1
  have htail : frobSq ((H*P) * (1-Z*Zᵀ)) = tailEnergy (H*P) r := by
    rw [energy_eq_projection]
    exact Projection.basisResidualTail _ _ h.rank_le hW
  have hh := retained_projection_residual h hout Z hZ
  change frobSq (_ * (1-Vr*Vrᵀ)) ≤ ((1+θ)/(1-θ)) * frobSq ((H*P)*(1-Z*Zᵀ)) at hh
  rw [htail] at hh
  have hp : Pᵀ = P := by simp [P, transpose_mul]
  have hi : P*P = P := by simp [P, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V, h.retained_basis.2.1]
  have hN := output_nested h hout
  have hn' : P * (Vr*Vrᵀ) = Vr*Vrᵀ := by
    simpa [transpose_mul, hp, P] using congrArg Matrix.transpose hN
  have hsplit := Projection.nestedProjectionSplit H P (Vr*Vrᵀ) hp hi hN
  rw [← energy_eq_projection, ← energy_eq_projection, ← energy_eq_projection] at hsplit
  have hres : H*P - H*(Vr*Vrᵀ) = (H*P)*(1-Vr*Vrᵀ) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hn']
  rw [hres] at hsplit
  have ht : tailEnergy (H*P) r ≤ tailEnergy H r :=
    Projection.tailEnergy_projector_le H V h.rank_le h.retained_basis.2.1
  have hθ : 0 ≤ θ := by
    have hb := gram_budget_of_run h
    have hb' := (norm_nonneg _).trans hb
    dsimp [θ, theta]
    exact mul_nonneg (by linarith [h.distortion_nonneg]) hb'
  have hden : 0 < 1-θ := sub_pos.mpr h.gram_small
  have ratio : (1+θ)/(1-θ) = 1 + 2*θ/(1-θ) := by field_simp; ring
  rw [ratio, add_mul, one_mul] at hh
  change _ ≤ frobSq (H*(1-P)) + tailEnergy (H*P) r + (2*θ/(1-θ)) * tailEnergy H r
  linarith [mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2*θ/(1-θ))]

end
end RPHOSVD.Mixed
