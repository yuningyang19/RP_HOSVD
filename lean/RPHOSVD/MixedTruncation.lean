import RPHOSVD.Mixed
import RPHOSVD.Retained

/-! Min–max bounds for singular values under a noisy retained sketch. -/
namespace RPHOSVD.Mixed
open Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
noncomputable section
variable {m n s r t k : ℕ}

private theorem frame_norm (V : Mat m n) (hV : Vᵀ * V = 1) (x : EuclideanSpace ℝ (Fin n)) :
    ‖V.toEuclideanLin x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change ∑ i, ((V *ᵥ x.ofLp) i) ^ 2 = ∑ i, (x.ofLp i) ^ 2
  simp only [sq]
  change (V *ᵥ x.ofLp) ⬝ᵥ (V *ᵥ x.ofLp) = x.ofLp ⬝ᵥ x.ofLp
  calc
    _ = x.ofLp ⬝ᵥ ((Vᵀ * V) *ᵥ x.ofLp) := by symm; rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    _ = _ := by rw [hV, one_mulVec]

private theorem norm_weighted (A : Mat m n) (V : Mat n k) (b : Fin k → ℝ)
    (hg : (A * V)ᵀ * (A * V) = diagonal b) (x : EuclideanSpace ℝ (Fin k)) :
    ‖(A * V).toEuclideanLin x‖ ^ 2 = ∑ i, b i * (x i)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change ∑ i, (((A*V) *ᵥ x.ofLp) i)^2 = _
  simp only [sq]
  change ((A*V) *ᵥ x.ofLp) ⬝ᵥ ((A*V) *ᵥ x.ofLp) = _
  calc
    _ = x.ofLp ⬝ᵥ (((A*V)ᵀ * (A*V)) *ᵥ x.ofLp) := by symm; rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    _ = _ := by rw [hg]; simp [dotProduct, Matrix.mulVec_diagonal, mul_left_comm]

private theorem gram_leading (A : Mat m n) (V : Mat n k) (h : LeadingRight A V) :
    (A * V)ᵀ * (A * V) = diagonal (fun i : Fin k => sigma A i.val^2) := by
  rw [transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc Vᵀ Aᵀ A, Matrix.mul_assoc, h.2.2,
    ← Matrix.mul_assoc, h.2.1, Matrix.one_mul]

/-- Lower bound version of the variational characterization of the kth singular
value, for an arbitrary isometric test frame. -/
theorem sigma_lower_of_frame (A : Mat m n) (F : Mat n k) (hF : Fᵀ * F = 1)
    (hk : 0 < k) (hkn : k ≤ n) (c : ℝ)
    (h : ∀ z : EuclideanSpace ℝ (Fin k), c * ‖z‖ ≤ ‖(A * F).toEuclideanLin z‖) :
    c ≤ sigma A (k-1) := by
  obtain ⟨W,hW⟩ := Projection.exists_rightBasis A
  let T := Wᵀ * F
  let g := Fin.castLE (show k-1 ≤ n by omega)
  let M : Mat (k-1) k := T.submatrix g id
  have hn : ¬ Function.Injective M.mulVecLin := by
    intro hi
    have he := LinearMap.finrank_le_finrank_of_injective hi
    simp only [Module.finrank_pi, Fintype.card_fin] at he
    omega
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot'] at hn
  push Not at hn
  obtain ⟨z,hMz,hz⟩ := hn
  let x : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 z
  let w := T.toEuclideanLin x
  have hWnorm : ‖w‖ = ‖x‖ := by
    have hT : Tᵀ * T = 1 := by
      simp [T, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc W Wᵀ, hW.2.1, hF]
    exact frame_norm T hT x
  have hAeq : (A * F).toEuclideanLin x = (A * W).toEuclideanLin w := by
    have ha : (A * W) * T = A * F := by
      simp [T, Matrix.mul_assoc, ← Matrix.mul_assoc W Wᵀ, hW.2.1]
    rw [← ha, Matrix.toLpLin_mul 2 2 2]; rfl
  have hsmall (i : Fin n) (hi : i.val < k-1) : w i = 0 := by
    have hh := congrFun hMz (⟨i.val, hi⟩ : Fin (k-1))
    exact hh
  have en := norm_weighted A W _ (gram_leading A W ⟨le_rfl,hW.1,hW.2.2⟩) w
  have hupper : ‖(A*W).toEuclideanLin w‖^2 ≤ sigma A (k-1)^2 * ‖w‖^2 := by
    rw [en, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i.val < k-1
    · simp [hsmall i hi]
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ (A.toEuclideanLin.singularValues_nonneg _)
        (A.toEuclideanLin.singularValues_antitone (le_of_not_gt hi)) 2
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr (fun hx => hz (congrArg WithLp.ofLp hx))
  rw [hWnorm, ← hAeq, ← mul_pow] at hupper
  have ht := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (A.toEuclideanLin.singularValues_nonneg _) hpos.le)).mp hupper
  exact (le_of_mul_le_mul_right ((h x).trans ht) hpos)

variable {H : Mat m n} {S : Mat s m} {Y : Mat s n} {V : Mat n t} {X : Mat m t}
    {G : Mat t t} {η ε u : ℝ}

theorem discarded_sv (h : MixedRun H S Y V X G η ε u r) (i : Fin n) (hi : t ≤ i.val) :
    sigma Y i.val ≤ ε := by
  by_contra! hd
  have hs : Finset.Iic i ⊆ Finset.univ.filter (fun j : Fin n => ε < sigma Y j.val) := by
    intro j hj
    have hji : j ≤ i := Finset.mem_Iic.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd.trans_le (Y.toEuclideanLin.singularValues_antitone hji)⟩
  have hc := Finset.card_le_card hs
  rw [Fin.card_Iic, ← h.retained_count] at hc
  omega

theorem mixed_target_le_retained (h : MixedRun H S Y V X G η ε u r) : r ≤ t := by
  by_contra! he
  have hr := h.rank_pos
  have hnr := h.rank_le
  exact (discarded_sv h ⟨r-1, by omega⟩ (by dsimp; omega)).not_gt h.target_retained

/-- The finite-noise version of the retained-original singular-value lower bound,
for every prefix of the retained SVD (including the smallest retained value). -/
theorem noisy_retained_sv (h : MixedRun H S Y V X G η ε u r) (hk : 0 < k) (hkt : k ≤ t) :
    (sigma Y (k-1) - productBudget u S H) / Real.sqrt (1+η) ≤ sigma (H * V) (k-1) := by
  let ds := productBudget u S H
  let F := Projection.firstCols (1 : Mat t t) hkt
  have hf : Fᵀ * F = 1 := Projection.firstCols_orthonormal _ _ (by simp)
  apply sigma_lower_of_frame _ F hf hk hkt
  intro z
  let v := (V * F).toEuclideanLin z
  have hv : ‖v‖ = ‖z‖ := by
    apply frame_norm
    simp [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V, h.retained_basis.2.1, hf]
  have hsel : (Yᵀ * Y) * (V * F) = (V * F) * diagonal (fun i : Fin k => sigma Y i.val^2) := by
    rw [← Matrix.mul_assoc, h.retained_basis.2.2, Matrix.mul_assoc, Matrix.mul_assoc]
    congr 1
    ext i j
    simp only [F, Projection.firstCols, Matrix.diagonal_mul, Matrix.mul_diagonal, submatrix_apply, id_eq, Matrix.one_apply]
    split_ifs with e
    · subst i; simp
    · simp
  have hG := gram_leading Y (V*F) ⟨hkt.trans h.retained_basis.1, by
    simp [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V, h.retained_basis.2.1, hf], hsel⟩
  have hlow : sigma Y (k-1) * ‖z‖ ≤ ‖Y.toEuclideanLin v‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Y.toEuclideanLin.singularValues_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
    change _ ≤ ‖(Y.toEuclideanLin ∘ₗ (V*F).toEuclideanLin) z‖^2
    rw [← Matrix.toLpLin_mul 2 2 2, norm_weighted Y (V*F) _ hG, mul_pow, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (Y.toEuclideanLin.singularValues_nonneg _) (Y.toEuclideanLin.singularValues_antitone (by omega)) 2
  have hd : ‖Y - S * H‖ ≤ ds := rounded_product_opNorm S H Y u h.roundoff_pos.le h.long_product h.sketch
  have err := ((Y-S*H).toEuclideanLin.toContinuousLinearMap.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
  have decomp : Y.toEuclideanLin v = (Y-S*H).toEuclideanLin v + S.toEuclideanLin (H.toEuclideanLin v) := by
    simp only [map_sub, LinearMap.sub_apply, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    abel
  have hse : ‖S.toEuclideanLin (H.toEuclideanLin v)‖ ≤ Real.sqrt (1+η) * ‖H.toEuclideanLin v‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt (by linarith [h.distortion_nonneg])]
    exact (h.embedding v).2
  have tr := (norm_add_le ((Y-S*H).toEuclideanLin v) (S.toEuclideanLin (H.toEuclideanLin v)))
  rw [← decomp] at tr
  change ‖(Y-S*H).toEuclideanLin v‖ ≤ ds * ‖v‖ at err
  rw [hv] at err
  have heq : ((H * V) * F).toEuclideanLin z = H.toEuclideanLin v := by
    simp [v, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
  rw [heq, div_mul_eq_mul_div, div_le_iff₀ (Real.sqrt_pos.mpr (by linarith [h.distortion_nonneg]))]
  change (sigma Y (k-1) - ds) * ‖z‖ ≤ _
  linarith only [hlow, tr, err, hse]

/-- Orthogonal complements chosen in the discarded ordered eigenspaces of the
observed sketch. The retained frame may use arbitrary orthonormal bases at ties. -/
theorem noisy_complement (h : MixedRun H S Y V X G η ε u r) :
    ∃ D : Mat n (n-t), Dᵀ * D = 1 ∧ Vᵀ * D = 0 ∧
      Projection.projector V + Projection.projector D = 1 ∧ ‖Y * D‖ ≤ ε := by
  obtain ⟨W, hW⟩ := Projection.exists_rightBasis Y
  let f (j : Fin (n-t)) : Fin n := ⟨t+j.val, by have ht := h.retained_basis.1; omega⟩
  let D := W.submatrix id f
  have hf : Function.Injective f := fun _ _ he => Fin.ext (Nat.add_left_cancel (congrArg Fin.val he))
  have hD : Dᵀ * D = 1 := by
    change (Wᵀ * W).submatrix f f = _
    rw [hW.1, Matrix.submatrix_one _ hf]
  let M := Yᵀ * Y
  let a := fun i : Fin t => sigma Y i.val^2
  let b := fun j : Fin (n-t) => sigma Y (f j).val^2
  have heV : M * V = V * diagonal a := h.retained_basis.2.2
  have heD : M * D = D * diagonal b := by
    ext i j
    have hj := congrArg (fun A : Mat n n => A i (f j)) hW.2.2
    rw [Matrix.mul_diagonal] at hj ⊢
    exact hj
  have heV' : Vᵀ * M = diagonal a * Vᵀ := by
    simpa only [M, transpose_mul, transpose_transpose, diagonal_transpose] using congrArg Matrix.transpose heV
  have hdcomm : diagonal a * (Vᵀ * D) = (Vᵀ * D) * diagonal b := by
    rw [← Matrix.mul_assoc, ← heV', Matrix.mul_assoc, heD, ← Matrix.mul_assoc]
  have hVD : Vᵀ * D = 0 := by
    ext i j
    have hpair := congrArg (fun U : Mat t (n-t) => U i j) hdcomm
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hpair
    have hv := retained_gt Y ε h.retained_basis.1 h.retained_count i
    have hd := discarded_sv h (f j) (by dsimp [f]; omega)
    have hdiff : b j < a i := (sq_lt_sq₀ (Y.toEuclideanLin.singularValues_nonneg _) (Y.toEuclideanLin.singularValues_nonneg _)).mpr (hd.trans_lt hv)
    change _ = (0 : ℝ)
    rcases mul_eq_zero.mp (show (a i - b j) * (Vᵀ * D) i j = 0 by linarith only [hpair]) with hz | hz
    · linarith
    · exact hz
  have hDV : Dᵀ * V = 0 := by simpa [transpose_mul] using congrArg Matrix.transpose hVD
  let C : Matrix (Fin n) (Fin t ⊕ Fin (n-t)) ℝ := Matrix.of fun i j => Sum.elim (V i) (D i) j
  have hC : Cᵀ * C = 1 := by
    ext i j
    rcases i with i|i <;> rcases j with j|j
    · simpa [C, Matrix.mul_apply, Matrix.one_apply] using congrArg (fun U : Mat t t => U i j) h.retained_basis.2.1
    · simpa [C, Matrix.mul_apply, Matrix.one_apply] using congrArg (fun U : Mat t (n-t) => U i j) hVD
    · simpa [C, Matrix.mul_apply, Matrix.one_apply] using congrArg (fun U : Mat (n-t) t => U i j) hDV
    · simpa [C, Matrix.mul_apply, Matrix.one_apply] using congrArg (fun U : Mat (n-t) (n-t) => U i j) hD
  have hcard : Fintype.card (Fin t ⊕ Fin (n-t)) = Fintype.card (Fin n) := by
    simp only [Fintype.card_sum, Fintype.card_fin]; have ht := h.retained_basis.1; omega
  have hC' := (Matrix.mul_eq_one_comm_of_equiv ((Fintype.card_eq.mp hcard).some)).mp hC
  have hcomplete : Projection.projector V + Projection.projector D = 1 := by
    ext i j
    have he := congrArg (fun U : Mat n n => U i j) hC'
    simpa only [Projection.projector, Matrix.add_apply, Matrix.mul_apply, transpose_apply, Fintype.sum_sum_type, C,
      Matrix.of_apply, Sum.elim_inl, Sum.elim_inr] using he
  refine ⟨D,hD,hVD,hcomplete,?_⟩
  have hgram : (Y*D)ᵀ * (Y*D) = diagonal b := by
    rw [transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc Dᵀ Yᵀ Y, Matrix.mul_assoc, heD,
      ← Matrix.mul_assoc, hD, Matrix.one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ h.threshold_pos.le
  intro z
  change ‖(Y*D).toEuclideanLin z‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg h.threshold_pos.le (norm_nonneg _))).mp
  rw [norm_weighted Y D b hgram, mul_pow, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Y.toEuclideanLin.singularValues_nonneg _)
    (discarded_sv h (f i) (by dsimp [f]; omega)) 2) (sq_nonneg _)

theorem noisy_retained_injective (h : MixedRun H S Y V X G η ε u r) :
    Function.Injective (H * V).mulVecLin := by
  have ht := mixed_target_le_retained h
  have hr := h.rank_pos
  have htpos : 0 < t := by omega
  let i : Fin t := ⟨t-1, by omega⟩
  have hsig := noisy_retained_sv h htpos (le_refl t)
  have hsmall := h.sketch_small
  have hgt := retained_gt Y ε h.retained_basis.1 h.retained_count i
  change ε < sigma Y (t-1) at hgt
  have hpos : 0 < sigma (H*V) (t-1) := lt_of_lt_of_le (div_pos (by linarith [h.threshold_pos]) (Real.sqrt_pos.mpr (by linarith [h.distortion_nonneg]))) hsig
  have hl := (H*V).toEuclideanLin.singularValues_pos_iff_lt_finrank_range.mp hpos
  have he := (H*V).rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin t) ℝ).toBasis
  change (H*V).rank = Module.finrank ℝ (H*V).toEuclideanLin.range at he
  rw [← he] at hl
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  have hb := (H*V).mulVecLin.finrank_range_add_finrank_ker
  change t-1 < Module.finrank ℝ (LinearMap.range (H*V).mulVecLin) at hl
  simp only [Module.finrank_pi, Fintype.card_fin] at hb
  omega

end
end RPHOSVD.Mixed
