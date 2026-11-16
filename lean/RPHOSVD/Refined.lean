import RPHOSVD.ExactProjection
import RPHOSVD.Retained

/-! Retained and discarded coordinates for the sharp ordinary RP error bound. -/
namespace RPHOSVD.Projection
open Matrix
open scoped RealInnerProductSpace
noncomputable section
variable {m n s r t : ℕ}

/-- The columns of the sketch basis discarded by the threshold, in their original order. -/
def Run.D (a : Run m n s r t) : Mat n (n - t) :=
  a.sketchBasis.submatrix id (fun i => ⟨t + i.val, by have ht := a.retained_le_n; omega⟩)

theorem Run.complementProperties (a : Run m n s r t) :
    a.Dᵀ * a.D = 1 ∧ a.Vᵀ * a.D = 0 ∧ projector a.V + projector a.D = 1 := by
  let f := fun i : Fin (n - t) => (⟨t + i.val, by have ht := a.retained_le_n; omega⟩ : Fin n)
  have hf : Function.Injective f := fun i j hij => Fin.ext (Nat.add_left_cancel (congrArg (Fin.val (n := n)) hij))
  have hGram (p q : ℕ) (u : Fin p → Fin n) (v : Fin q → Fin n) :
      (a.sketchBasis.submatrix id u)ᵀ * a.sketchBasis.submatrix id v = (1 : Mat n n).submatrix u v := by
    change (a.sketchBasisᵀ * a.sketchBasis).submatrix u v = _
    rw [a.sketchBasis_spec.1]
  refine ⟨(hGram _ _ f f).trans (Matrix.submatrix_one f hf), ?_, ?_⟩
  · rw [show a.Vᵀ * a.D = (1 : Mat n n).submatrix (Fin.castLE a.retained_le_n) f from hGram ..]
    ext i j
    have h : Fin.castLE a.retained_le_n i ≠ f j := by
      intro eq
      have := congrArg Fin.val eq
      change i.val = t + j.val at this
      omega
    simp [submatrix_apply, h]
  · obtain ⟨d, hn⟩ := Nat.exists_eq_add_of_le a.retained_le_n
    subst n
    ext i j
    have h := congrArg (fun T : Mat (t + d) (t + d) => T i j) a.sketchBasis_spec.2.1
    simp only [Matrix.mul_apply, transpose_apply, Fin.sum_univ_add] at h
    let ee : Fin (t + d - t) ≃ Fin d := finCongr (Nat.add_sub_cancel_left t d)
    simp only [Run.D, Run.V, firstCols, projector, Matrix.add_apply, Matrix.mul_apply,
      transpose_apply, submatrix_apply, id_eq]
    convert h using 1
    congr 1
    apply Fintype.sum_equiv ee
    intro x
    have he : (ee x).val = x.val := by simp [ee]
    simp [Fin.natAdd, he]

/-- Polarization of the realized embedding when the two sketch images are perpendicular. -/
theorem embeddingAngle (H : Mat m n) (S : Mat s m) (η : ℝ) (hη : EmbedsRange H S η)
    (x y : Fin n → ℝ) (hx : vecSq (H *ᵥ x) = 1) (hy : vecSq (H *ᵥ y) = 1)
    (hxy : (S *ᵥ (H *ᵥ x)) ⬝ᵥ (S *ᵥ (H *ᵥ y)) = 0) :
    |(H *ᵥ x) ⬝ᵥ (H *ᵥ y)| ≤ η := by
  have sq {k} (z : Fin k → ℝ) : vecSq z = z ⬝ᵥ z := by simp [vecSq, dotProduct, pow_two]
  have plus := hη.2.2 (x + y)
  have minus := hη.2.2 (x - y)
  rw [sq] at hx hy
  simp only [mulVec_add, mulVec_sub, sq, add_dotProduct, dotProduct_add, sub_dotProduct,
    dotProduct_sub, hx, hy, hxy, dotProduct_comm (H *ᵥ y) (H *ᵥ x),
    dotProduct_comm (S *ᵥ (H *ᵥ y)) (S *ᵥ (H *ᵥ x))] at plus minus
  exact abs_le.mpr ⟨by linarith [plus.2, minus.1], by linarith [plus.1, minus.2]⟩

private theorem eucl_vecSq {p} (v : EuclideanSpace ℝ (Fin p)) : vecSq v.ofLp = ‖v‖ ^ 2 := by
  simp [vecSq, EuclideanSpace.real_norm_sq_eq]

private theorem sqApply {p q} (A : Mat p q) (x : Fin q → ℝ) :
    vecSq (A *ᵥ x) = x ⬝ᵥ ((Aᵀ * A) *ᵥ x) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp [vecSq, dotProduct, pow_two]

private theorem sketchDiscardGram (a : Run m n s r t) :
    (a.S * a.H * a.D)ᵀ * (a.S * a.H * a.D) = diagonal
    (fun i : Fin (n - t) => sigma (a.S * a.H) (t + i.val) ^ 2) := by
  let W := a.sketchBasis
  let Y := a.S * a.H
  let f := fun i : Fin (n - t) => (⟨t + i.val, by have ht := a.retained_le_n; omega⟩ : Fin n)
  have hf : Function.Injective f := fun i j hij => Fin.ext (Nat.add_left_cancel (congrArg (Fin.val (n := n)) hij))
  have hg : (Y * W)ᵀ * (Y * W) = diagonal (fun i : Fin n => sigma Y i.val ^ 2) := by
    rw [Matrix.transpose_mul Y W, ← Matrix.mul_assoc, Matrix.mul_assoc Wᵀ Yᵀ Y,
      Matrix.mul_assoc, a.sketchBasis_spec.2.2, ← Matrix.mul_assoc, a.sketchBasis_spec.1, one_mul]
  change ((Y * W)ᵀ * (Y * W)).submatrix f f = _
  rw [hg, Matrix.submatrix_diagonal _ f hf]
  rfl

/-- Spectral error on discarded columns with its precise threshold and embedding constant. -/
theorem discardedOpNormBound (a : Run m n s r t) (η : ℝ) (hη : EmbedsRange a.H a.S η) :
    opNorm (a.H * a.D)^2 ≤ a.ε^2 / (1 - η) := by
  let c := a.ε^2 / (1 - η)
  have hc : 0 ≤ c := div_nonneg (sq_nonneg _) (sub_nonneg.mpr hη.2.1.le)
  have hpoint (z : Fin (n - t) → ℝ) : vecSq ((a.H * a.D) *ᵥ z) ≤ c * vecSq z := by
    have h := (hη.2.2 (a.D *ᵥ z)).1
    simp only [mulVec_mulVec] at h
    have hsk : vecSq ((a.S * a.H * a.D) *ᵥ z) ≤ a.ε^2 * vecSq z := by
      rw [sqApply, sketchDiscardGram]
      simp only [Matrix.mulVec_diagonal, dotProduct, vecSq, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hi : t + i.val < n := by have hh := a.retained_le_n; omega
      have hv : sigma (a.S * a.H) (t + i.val) ≤ a.ε :=
        le_of_not_gt fun hh => (Nat.le_add_right t i.val).not_gt ((a.threshold ⟨_, hi⟩).mpr hh)
      have hn := (a.S * a.H).toEuclideanLin.singularValues_nonneg (t + i.val)
      have hv2 : sigma (a.S * a.H) (t + i.val) ^ 2 ≤ a.ε^2 := pow_le_pow_left₀ hn hv 2
      nlinarith only [mul_le_mul_of_nonneg_right hv2 (sq_nonneg (z i))]
    rw [Matrix.mul_assoc a.S a.H a.D] at hsk
    have hg := h.trans hsk
    change _ ≤ a.ε^2 / (1 - η) * _
    rw [div_mul_eq_mul_div, le_div_iff₀ (sub_pos.mpr hη.2.1)]
    simpa only [mul_comm (1 - η)] using hg
  have hop : opNorm (a.H * a.D) ≤ Real.sqrt c := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro z
    have h := hpoint z.ofLp
    change vecSq ((a.H * a.D).toEuclideanLin z).ofLp ≤ _ at h
    rw [eucl_vecSq, eucl_vecSq] at h
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa [mul_pow, Real.sq_sqrt hc] using h
  exact (pow_le_pow_left₀ (norm_nonneg _) hop 2).trans_eq (Real.sq_sqrt hc)

/-- In the sketch, retained and discarded right singular coordinates are orthogonal. -/
theorem Run.sketchCross (a : Run m n s r t) :
    (a.S * a.H * a.V)ᵀ * (a.S * a.H * a.D) = 0 := by
  let Y := a.S * a.H
  let W := a.sketchBasis
  let f := fun i : Fin (n - t) => (⟨t + i.val, by have ht := a.retained_le_n; omega⟩ : Fin n)
  have hg : (Y * W)ᵀ * (Y * W) = diagonal (fun i : Fin n => sigma Y i.val ^ 2) := by
    rw [Matrix.transpose_mul Y W, ← Matrix.mul_assoc, Matrix.mul_assoc Wᵀ Yᵀ Y,
      Matrix.mul_assoc, a.sketchBasis_spec.2.2, ← Matrix.mul_assoc, a.sketchBasis_spec.1, one_mul]
  change ((Y * W)ᵀ * (Y * W)).submatrix (Fin.castLE a.retained_le_n) f = _
  rw [hg]
  ext i j
  simp only [submatrix_apply, Matrix.zero_apply]
  apply Matrix.diagonal_apply_ne
  intro hh
  have hh' := congrArg Fin.val hh
  change i.val = t + j.val at hh'
  omega

private theorem embeddingInnerBound (H : Mat m n) (S : Mat s m) (η : ℝ)
    (hη : EmbedsRange H S η) (x y : EuclideanSpace ℝ (Fin n))
    (horth : ⟪S.toEuclideanLin (H.toEuclideanLin x), S.toEuclideanLin (H.toEuclideanLin y)⟫ = 0) :
    |⟪H.toEuclideanLin x, H.toEuclideanLin y⟫| ≤ η * ‖H.toEuclideanLin x‖ * ‖H.toEuclideanLin y‖ := by
  let X := H.toEuclideanLin x
  let Y := H.toEuclideanLin y
  change |⟪X, Y⟫| ≤ η * ‖X‖ * ‖Y‖
  by_cases hx : X = 0
  · simp [hx]
  by_cases hy : Y = 0
  · simp [hy]
  have nx := norm_pos_iff.mpr hx
  have ny := norm_pos_iff.mpr hy
  let u := ‖X‖⁻¹ • x
  let v := ‖Y‖⁻¹ • y
  have hu : vecSq (H *ᵥ u.ofLp) = 1 := by
    change vecSq (H.toEuclideanLin u).ofLp = _
    rw [eucl_vecSq]
    change ‖H.toEuclideanLin (‖X‖⁻¹ • x)‖^2 = 1
    rw [map_smul, norm_smul]
    change (|‖X‖⁻¹| * ‖X‖)^2 = 1
    simp [abs_of_nonneg (inv_nonneg.mpr nx.le), nx.ne']
  have hv : vecSq (H *ᵥ v.ofLp) = 1 := by
    change vecSq (H.toEuclideanLin v).ofLp = _
    rw [eucl_vecSq]
    change ‖H.toEuclideanLin (‖Y‖⁻¹ • y)‖^2 = 1
    rw [map_smul, norm_smul]
    change (|‖Y‖⁻¹| * ‖Y‖)^2 = 1
    simp [abs_of_nonneg (inv_nonneg.mpr ny.le), ny.ne']
  have dot {k} (u v : EuclideanSpace ℝ (Fin k)) : u.ofLp ⬝ᵥ v.ofLp = ⟪u, v⟫ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  have hh : ⟪S.toEuclideanLin (H.toEuclideanLin u), S.toEuclideanLin (H.toEuclideanLin v)⟫ = 0 := by
    simp [u, v, real_inner_smul_left, real_inner_smul_right, horth]
  have ho := embeddingAngle H S η hη u.ofLp v.ofLp hu hv
  rw [← dot] at hh
  have res := ho hh
  change |(H.toEuclideanLin u).ofLp ⬝ᵥ (H.toEuclideanLin v).ofLp| ≤ η at res
  rw [dot] at res
  simp only [u, v, map_smul, real_inner_smul_left, real_inner_smul_right, abs_mul,
    abs_inv, abs_of_pos nx, abs_of_pos ny] at res
  change ‖Y‖⁻¹ * (‖X‖⁻¹ * |⟪X,Y⟫|) ≤ η at res
  calc
    _ = (‖Y‖⁻¹ * (‖X‖⁻¹ * |⟪X,Y⟫|)) * ‖X‖ * ‖Y‖ := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right res nx.le) ny.le

/-- For any orthonormal coordinates on the retained original column space, the
operator norm of the retained/discarded cross term is at most η times the discarded norm. -/
theorem discardedCoupling (a : Run m n s r t) (η : ℝ) (he : EmbedsRange a.H a.S η)
    (Q : Mat m t) (hq : Qᵀ * Q = 1)
    (hqr : LinearMap.range Q.mulVecLin = LinearMap.range (a.H * a.V).mulVecLin) :
    opNorm (Qᵀ * a.H * a.D) ≤ η * opNorm (a.H * a.D) := by
  let F := a.H * a.D
  have hη : 0 ≤ η := he.1.le
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hη (norm_nonneg _))
  intro z
  let y := F.toEuclideanLin z
  let w := Qᵀ.toEuclideanLin y
  have hmap : (Qᵀ * a.H * a.D).toEuclideanLin z = w := by
    rw [Matrix.mul_assoc, show (Qᵀ * (a.H * a.D)).toEuclideanLin = Qᵀ.toEuclideanLin ∘ₗ F.toEuclideanLin from Matrix.toLpLin_mul 2 2 2 _ _]; rfl
  change ‖(Qᵀ * a.H * a.D).toEuclideanLin z‖ ≤ _
  rw [hmap]
  by_cases hw : w = 0
  · simp only [hw, norm_zero]
    positivity
  have hwpos := norm_pos_iff.mpr hw
  have hmem : Q.mulVecLin w.ofLp ∈ LinearMap.range (a.H * a.V).mulVecLin := hqr ▸ ⟨_, rfl⟩
  obtain ⟨c, hC⟩ := hmem
  let x := a.V.toEuclideanLin (WithLp.toLp 2 c)
  let d := a.D.toEuclideanLin z
  have hHx : a.H.toEuclideanLin x = Q.toEuclideanLin w := by
    apply WithLp.ofLp_injective 2
    change (a.H * a.V) *ᵥ c = Q *ᵥ w.ofLp at hC
    change a.H *ᵥ (a.V *ᵥ c) = Q *ᵥ w.ofLp
    rwa [mulVec_mulVec]
  have hHd : a.H.toEuclideanLin d = y := by
    change _ = (a.H * a.D).toEuclideanLin z
    rw [show (a.H * a.D).toEuclideanLin = a.H.toEuclideanLin ∘ₗ a.D.toEuclideanLin from Matrix.toLpLin_mul 2 2 2 _ _]; rfl
  have horth : ⟪a.S.toEuclideanLin (a.H.toEuclideanLin x), a.S.toEuclideanLin (a.H.toEuclideanLin d)⟫ = 0 := by
    let A := a.S * a.H * a.V
    let B := a.S * a.H * a.D
    have hA : a.S.toEuclideanLin (a.H.toEuclideanLin x) = A.toEuclideanLin (WithLp.toLp 2 c) := by
      simp only [x, A, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    have hB : a.S.toEuclideanLin (a.H.toEuclideanLin d) = B.toEuclideanLin z := by
      simp only [d, B, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
    rw [hA, hB]
    rw [← LinearMap.adjoint_inner_right, ← A.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    have hz : Aᵀ.toEuclideanLin (B.toEuclideanLin z) = 0 := by
      change (Aᵀ.toEuclideanLin ∘ₗ B.toEuclideanLin) z = 0
      rw [← Matrix.toLpLin_mul 2 2 2, a.sketchCross]; simp
    simp [hz]
  have ha := embeddingInnerBound a.H a.S η he x d horth
  rw [hHx, hHd, ← LinearMap.adjoint_inner_right, ← Q.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial] at ha
  change |⟪w,w⟫| ≤ η * ‖Q.toEuclideanLin w‖ * ‖y‖ at ha
  have hqnorm : ‖Q.toEuclideanLin w‖ = ‖w‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← eucl_vecSq, ← eucl_vecSq]
    change vecSq (Q *ᵥ w.ofLp) = vecSq w.ofLp
    rw [sqApply, hq, one_mulVec]
    simp [vecSq, dotProduct, pow_two]
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _), hqnorm] at ha
  have hwbound : ‖w‖ ≤ η * ‖y‖ := by nlinarith
  have hybound : ‖y‖ ≤ opNorm F * ‖z‖ := F.toEuclideanLin.toContinuousLinearMap.le_opNorm z
  change ‖w‖ ≤ (η * opNorm F) * ‖z‖
  exact hwbound.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hybound hη)

/-- Appending coordinates by an isometric inclusion preserves every SVD tail. -/
theorem tail_appendFrame {k q} (A : Mat m k) (V : Mat n k) (hV : Vᵀ * V = 1)
    (hq : q ≤ k) (hk : k ≤ n) : tailEnergy (A * Vᵀ) q = tailEnergy A q := by
  let L := A * Vᵀ
  have hLV : L * V = A := by simp [L, Matrix.mul_assoc, hV]
  obtain ⟨W, hW⟩ := exists_rightBasis A
  obtain ⟨U, hU⟩ := exists_rightBasis L
  let V₁ := firstCols W hq
  let V₂ := firstCols U (hq.trans hk)
  have rankproj {d e} (M : Mat m d) (C : Mat d q) (N : Mat d e) :
      (M * projector C * N).rank ≤ q := by
    exact (Matrix.rank_mul_le_left _ _).trans <| (Matrix.rank_mul_le_right _ _).trans <|
      (Matrix.rank_mul_le_left C Cᵀ).trans C.rank_le_width
  have hAW : frobSq (A - A * projector V₁) = tailEnergy A q := by
    simpa only [Matrix.mul_sub, Matrix.mul_one] using basisResidualTail A W hq hW
  have hLU : frobSq (L - L * projector V₂) = tailEnergy L q := by
    simpa only [Matrix.mul_sub, Matrix.mul_one] using basisResidualTail L U (hq.trans hk) hU
  apply le_antisymm
  · have h := tailEnergy_le_error L (A * projector V₁ * Vᵀ) (hq.trans hk) (rankproj ..)
    change tailEnergy L q ≤ _
    rw [show L - A * projector V₁ * Vᵀ = (A - A * projector V₁) * Vᵀ by rw [Matrix.sub_mul],
      rightFrameEnergy _ _ hV, hAW] at h
    exact h
  · have h := tailEnergy_le_error A (L * projector V₂ * V) hq (rankproj ..)
    let E := L - L * projector V₂
    have hs : (projector V)ᵀ = projector V := by simp [projector, transpose_mul]
    have hi : projector V * projector V = projector V := by
      simp [projector, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V, hV]
    have hsplit := frobSplit E (projector V) hs hi
    have he : frobSq (E * projector V) = frobSq (E * V) := by
      rw [projector, ← Matrix.mul_assoc, rightFrameEnergy _ _ hV]
    have hnon : 0 ≤ frobSq (E * (1 - projector V)) := by
      rw [frobSq_cols]; exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    rw [← hLV] at h
    rw [← Matrix.sub_mul] at h
    change tailEnergy (L * V) q ≤ frobSq (E * V) at h
    rw [hLV] at h
    change frobSq E = _ at hLU
    linarith only [h, hsplit, hLU, he, hnon]

private theorem tail_succ {p d} (A : Mat m d) (hp : p < d) :
    tailEnergy A p = (sigma A p)^2 + tailEnergy A (p+1) := by
  let i : Fin d := ⟨p, hp⟩
  have hh (j : Fin d) : (if p ≤ j.val then sigma A j.val ^ 2 else 0) =
      (if j = i then sigma A p ^ 2 else 0) + (if p+1 ≤ j.val then sigma A j.val ^ 2 else 0) := by
    by_cases hj : j.val = p
    · have : j = i := Fin.ext hj
      simp [this, i]
    · have hiff : p ≤ j.val ↔ p+1 ≤ j.val := by omega
      have hne : j ≠ i := fun eq => hj (congrArg Fin.val eq)
      simp [hiff, hne]
  simp only [tailEnergy, hh, Finset.sum_add_distrib]
  simp

/-- The r-th squared singular value for the retained tall factor agrees with the recovered B. -/
theorem Run.retainedScale (a : Run m n s r t) :
    sigma a.B (r-1) ^ 2 = sigma (a.H * a.V) (r-1) ^ 2 := by
  have hHP : (a.H * a.V) * a.Vᵀ = a.H * a.P := by simp [Run.P, projector, Matrix.mul_assoc]
  have htail (q : ℕ) (hq : q ≤ t) : tailEnergy (a.H * a.P) q = tailEnergy (a.H * a.V) q := by
    rw [← hHP]; exact tail_appendFrame _ _ a.V_orthonormal hq a.retained_le_n
  have hpri : r-1 < t := by have h := a.rank_pos; have h' := a.rank_le_retained; omega
  have hpn : r-1 < n := hpri.trans_le a.retained_le_n
  have hsucc : r-1+1 ≤ t := by omega
  have h₁ := tail_succ (a.H * a.V) hpri
  have h₂ := tail_succ (a.H * a.P) hpn
  rw [htail _ hpri.le, htail _ hsucc] at h₂
  rw [sigma_eq_of_gram_eq _ _ (gramRecovery a)]
  linarith

/-- The two candidate residuals coincide even when a target singular value is repeated. -/
theorem Run.sameRetainedResidual (a : Run m n s r t) (W : Mat t t) (hW : RightBasis (a.H * a.V) W) :
    frobSq (a.H - (a.H * a.V) * projector (firstCols W a.rank_le_retained) * a.Vᵀ) =
    frobSq (a.H - a.H * a.Pout) := by
  let A := a.H * a.V
  let E := projector (firstCols W a.rank_le_retained)
  let M := A * E * a.Vᵀ
  have hV := a.V_orthonormal
  have hs : a.Pᵀ = a.P := by simp [Run.P, projector, transpose_mul]
  have hi : a.P * a.P = a.P := by simp [Run.P, projector, Matrix.mul_assoc, ← Matrix.mul_assoc a.Vᵀ a.V, hV]
  have hMP : M * a.P = M := by simp [M, Run.P, projector, Matrix.mul_assoc, ← Matrix.mul_assoc a.Vᵀ a.V, hV]
  have hHP : A * a.Vᵀ = a.H * a.P := by simp [A, Run.P, projector, Matrix.mul_assoc]
  have h := frobSplit (a.H - M) a.P hs hi
  have hcompl : (a.H - M) * (1 - a.P) = a.H * (1 - a.P) := by
    rw [Matrix.sub_mul, Matrix.mul_sub M, Matrix.mul_one, hMP, sub_self, sub_zero]
  have hret : (a.H - M) * a.P = (A - A * E) * a.Vᵀ := by rw [Matrix.sub_mul, hMP, Matrix.sub_mul, hHP]
  rw [hcompl, hret, rightFrameEnergy _ _ hV] at h
  have hw := basisResidualTail A W a.rank_le_retained hW
  change frobSq (A * (1 - E)) = _ at hw
  rw [Matrix.mul_sub, Matrix.mul_one] at hw
  rw [hw, ← tail_appendFrame A a.V hV a.rank_le_retained a.retained_le_n, hHP] at h
  exact h.trans (exactProjectionIdentity a).symm

/-- The retained tall factor is injective even when the original matrix is rank deficient. -/
theorem Run.retainedInjective (a : Run m n s r t) : Function.Injective (a.H * a.V).mulVecLin := by
  have hb : a.B.rank = (a.H * a.P).rank := by
    rw [← Matrix.rank_transpose_mul_self a.B, gramRecovery, Matrix.rank_transpose_mul_self]
  have hHP : a.H * a.V * a.Vᵀ = a.H * a.P := by simp [Run.P, projector, Matrix.mul_assoc]
  have ht : t ≤ (a.H * a.V).rank := by
    calc
      t = a.B.rank := a.rank_B.symm
      _ = (a.H * a.V * a.Vᵀ).rank := by rw [hHP, hb]
      _ ≤ (a.H * a.V).rank := Matrix.rank_mul_le_left _ _
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  have hh := (a.H * a.V).mulVecLin.finrank_range_add_finrank_ker
  change t ≤ Module.finrank ℝ (LinearMap.range (a.H * a.V).mulVecLin) at ht
  simp only [Module.finrank_pi, Fintype.card_fin] at hh
  omega

/-- Theorem `thm:rp-refined`, including the strict minimum-threshold clause. -/
theorem refinedProjection : refinedProjectionClaim := by
  intro m n s r t a η he hgap
  obtain ⟨Q, hQ, hrange⟩ := exists_rangeFrame _ a.retainedInjective
  obtain ⟨W, hW⟩ := exists_rightBasis (a.H * a.V)
  obtain ⟨hd, hcross, hcomplete⟩ := a.complementProperties
  have hpos := sub_pos.mpr he.2.1
  have hdiscard := discardedOpNormBound a η he
  have hscale : opNorm (a.H * a.D)^2 ≤ sigma (a.H * a.V) (r-1)^2 / 2 := by
    apply hdiscard.trans
    rw [div_le_iff₀ hpos, ← a.retainedScale]
    linarith only [hgap]
  have h := retainedSubspace a.H a.V a.D Q W a.rank_le_retained a.rank_pos a.retained_le_n
    a.V_orthonormal hd hcross hcomplete a.retainedInjective hQ hrange hW hscale
  rw [a.sameRetainedResidual W hW] at h
  have hc := pow_le_pow_left₀ (norm_nonneg _) (discardedCoupling a η he Q hQ hrange) 2
  rw [mul_pow] at hc
  have hcb := hc.trans (mul_le_mul_of_nonneg_left hdiscard (sq_nonneg η))
  refine ⟨h.trans ?_, fun hmin => (fullRetentionExact a (a.full_of_min hmin)).le⟩
  apply add_le_add_right
  calc
    2 * (r : ℝ) * opNorm (Qᵀ * a.H * a.D)^2 ≤ 2 * r * (η^2 * (a.ε^2 / (1-η))) :=
      mul_le_mul_of_nonneg_left hcb (by positivity)
    _ = _ := by ring

end
end RPHOSVD.Projection
