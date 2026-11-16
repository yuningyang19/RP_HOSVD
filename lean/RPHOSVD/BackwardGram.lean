import RPHOSVD.MixedAsymptotic

/-! Explicit error constants for the computed Gram matrix and a successful
componentwise-backward-stable Cholesky factor. -/
namespace RPHOSVD.Mixed
open Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace
noncomputable section

/-- A dimension-only majorant that works simultaneously for the m-by-t
computed preconditioner and the t-by-t triangular factor, for every t ≤ n. -/
def gramScale (m n : ℕ) : ℝ := 2 * (m+n+2 : ℝ)^5

private theorem gramScale_nonneg (m n : ℕ) : 0 ≤ gramScale m n := by unfold gramScale; positivity

private theorem gram_contract_bound {a t : ℕ} (A : Mat a t) (N : Mat t t) (k : ℕ)
    (u : ℝ) (hu : 0 ≤ u) (hku : (k:ℝ)*u ≤ 1/2)
    (h : ∀ i j, |N i j| ≤ gamma k u * (magnitude Aᵀ * magnitude A) i j) :
    ‖N‖ ≤ (2 * (k:ℝ) * ((a+1:ℝ)*(t+1))^2) * u * ‖A‖^2 := by
  have hg := gamma_upper k u hu hku
  have e := entrywise_opNorm_bound N (magnitude Aᵀ * magnitude A) _ hg.1 h
  have eA := magnitude_bound A ‖A‖ (norm_nonneg _) (entry_le_norm A)
  have eAt := magnitude_bound Aᵀ ‖Aᵀ‖ (norm_nonneg _) (entry_le_norm Aᵀ)
  rw [transpose_opNorm] at eAt
  have eprod := (Matrix.l2_opNorm_mul (magnitude Aᵀ) (magnitude A)).trans
    (mul_le_mul eAt eA (norm_nonneg _) (by positivity))
  calc
    _ ≤ _ := e
    _ ≤ ((2*(k:ℝ))*u) * ((‖A‖ * ((t+1:ℝ)*(a+1))) * (‖A‖ * ((a+1:ℝ)*(t+1)))) :=
      mul_le_mul hg.2 eprod (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem scalarMajor {a t k : ℕ} (d : ℝ) (ha : (a:ℝ)+1 ≤ d) (ht : (t:ℝ)+1 ≤ d)
    (hk : (k:ℝ) ≤ d) : 2 * (k:ℝ) * ((a+1:ℝ)*(t+1))^2 ≤ 2*d^5 := by
  have hd0 : 0 ≤ d := (Nat.cast_nonneg k).trans hk
  calc
    _ ≤ 2*d*(d*d)^2 := by gcongr
    _ = _ := by ring

/-- Gram error and size of R derived from the two componentwise contracts.
The coefficient is uniform in the retained dimension t. -/
theorem backwardGram_budget {m n t : ℕ} (X : Mat m t) (G R : Mat t t) (u b : ℝ)
    (ht : t ≤ n) (hu : 0 ≤ u) (hb : ‖X‖ ≤ b)
    (hsmall : gramScale m n * u ≤ 1/2)
    (hG : StoredProduct u Xᵀ X G)
    (hR : ∀ i j, |(Rᵀ * R - G) i j| ≤ gamma (t+1) u * (magnitude Rᵀ * magnitude R) i j) :
    ‖R‖ ≤ 2*b ∧ ‖Rᵀ * R - Xᵀ * X‖ ≤ (5 * gramScale m n * b^2) * u := by
  let d : ℝ := m+n+2
  let e := gramScale m n * u
  have hn : 0 ≤ e := mul_nonneg (gramScale_nonneg _ _) hu
  have ht' : (t:ℝ) ≤ n := by exact_mod_cast ht
  have hd : 2 ≤ d := by dsimp [d]; linarith [Nat.cast_nonneg (α:=ℝ) n,Nat.cast_nonneg (α:=ℝ) m]
  have hscale : d ≤ gramScale m n := by
    change d ≤ 2*d^5
    have hp : d ≤ d^5 := by simpa using (pow_le_pow_right₀ (by linarith : 1≤d) (by decide : 1 ≤ 5))
    linarith
  have hku (k : ℕ) (hk : (k:ℝ) ≤ d) : (k:ℝ)*u ≤ 1/2 :=
    (mul_le_mul_of_nonneg_right (hk.trans hscale) hu).trans hsmall
  have sm : (m:ℝ)+1 ≤ d := by dsimp [d]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have st : (t:ℝ)+1 ≤ d := by dsimp [d]; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have eg := gram_contract_bound X (G-Xᵀ*X) m u hu (hku m (by linarith)) hG
  have ec := gram_contract_bound R (Rᵀ*R-G) (t+1) u hu (hku _ (by push_cast; linarith)) hR
  have eg' : ‖G-Xᵀ*X‖ ≤ e * ‖X‖^2 := by
    apply eg.trans
    gcongr
    exact mul_le_mul_of_nonneg_right (scalarMajor (k:=m) d sm st (by linarith)) hu
  have ec' : ‖Rᵀ*R-G‖ ≤ e * ‖R‖^2 := by
    apply ec.trans
    gcongr
    exact mul_le_mul_of_nonneg_right (scalarMajor (k:=t+1) d st st (by push_cast; linarith)) hu
  have ngram {p q : ℕ} (A : Mat p q) : ‖Aᵀ*A‖ = ‖A‖^2 := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, sq] using Matrix.l2_opNorm_conjTranspose_mul_self A
  have gr := norm_add_le (G-Xᵀ*X) (Xᵀ*X)
  have rr := norm_add_le (Rᵀ*R-G) G
  rw [sub_add_cancel, ngram] at gr rr
  have eb : e ≤ 1/2 := hsmall
  have hsq : ‖R‖^2 ≤ 3*‖X‖^2 := by
    linarith only [gr,rr,ec',eg',mul_le_mul_of_nonneg_right eb (sq_nonneg ‖X‖),mul_le_mul_of_nonneg_right eb (sq_nonneg ‖R‖)]
  have hb0 := (norm_nonneg X).trans hb
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hR2 : ‖R‖^2 ≤ (2*b)^2 := by nlinarith only [hsq,hb2,sq_nonneg b]
  refine ⟨(sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hR2, ?_⟩
  have hsum := norm_add_le (Rᵀ*R-G) (G-Xᵀ*X)
  rw [sub_add_sub_cancel] at hsum
  have hfinal : ‖Rᵀ*R-Xᵀ*X‖ ≤ e*(4*b^2) + e*b^2 := hsum.trans
    (add_le_add (ec'.trans (mul_le_mul_of_nonneg_left (by nlinarith only [hR2]) hn))
      (eg'.trans (mul_le_mul_of_nonneg_left hb2 hn)))
  calc
    _ ≤ _ := hfinal
    _ = _ := by dsimp [e]; ring

private theorem quad_gram {m t : ℕ} (A : Mat m t) (z : EuclideanSpace ℝ (Fin t)) :
    z.ofLp ⬝ᵥ ((Aᵀ * A) *ᵥ z.ofLp) = ‖A.toEuclideanLin z‖^2 := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct,sq]
  rfl

private theorem quad_abs {t : ℕ} (F : Mat t t) (z : EuclideanSpace ℝ (Fin t)) :
    |z.ofLp ⬝ᵥ (F *ᵥ z.ofLp)| ≤ ‖F‖ * ‖z‖^2 := by
  have hi := abs_real_inner_le_norm z (Matrix.toEuclideanCLM (n := Fin t) (𝕜 := ℝ) F z)
  rw [Matrix.inner_toEuclideanCLM] at hi
  refine hi.trans ?_
  have hb := Matrix.l2_opNorm_mulVec F z
  change ‖Matrix.toEuclideanCLM (n := Fin t) (𝕜 := ℝ) F z‖ ≤ ‖F‖ * ‖z‖ at hb
  simpa [sq,mul_left_comm] using mul_le_mul_of_nonneg_left hb (norm_nonneg z)

/-- Stability of the inverse triangular factor and of the normalized computed
preconditioner. The proof also covers matrices with zero retained columns. -/
theorem backwardGram_normalized {m t : ℕ} (X : Mat m t) (R : Mat t t) (a e : ℝ)
    (ha : 0 < a) (hx : ∀ z : EuclideanSpace ℝ (Fin t), a * ‖z‖ ≤ ‖X.toEuclideanLin z‖)
    (hR : ∀ i j, j < i → R i j = 0) (hp : ∀ i, 0 < R i i)
    (he : ‖Rᵀ*R - Xᵀ*X‖ ≤ e) (hs : e ≤ a^2 / 2) :
    IsUnit R.det ∧ ‖R⁻¹‖ ≤ 2/a ∧
      ‖(X*R⁻¹)ᵀ*(X*R⁻¹) - 1‖ ≤ (2/a)^2 * e := by
  have htri : R.IsUpperTriangular := fun {i j} hij => hR i j hij
  have hdet : IsUnit R.det := by
    rw [Matrix.det_of_isUpperTriangular htri, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne')
  have hRlow (z : EuclideanSpace ℝ (Fin t)) : (a/2)*‖z‖ ≤ ‖R.toEuclideanLin z‖ := by
    let F := Rᵀ*R - Xᵀ*X
    have hq := quad_abs F z
    change |z.ofLp ⬝ᵥ (F *ᵥ z.ofLp)| ≤ ‖F‖ * ‖z‖^2 at hq
    have hid : z.ofLp ⬝ᵥ (F *ᵥ z.ofLp) = ‖R.toEuclideanLin z‖^2 - ‖X.toEuclideanLin z‖^2 := by
      dsimp [F]
      rw [Matrix.sub_mulVec, dotProduct_sub, quad_gram, quad_gram]
    rw [hid] at hq
    have hg := neg_le_of_abs_le (hq.trans (mul_le_mul_of_nonneg_right (he.trans hs) (sq_nonneg _)))
    have hl := pow_le_pow_left₀ (mul_nonneg ha.le (norm_nonneg _)) (hx z) 2
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    rw [mul_pow] at hl ⊢
    nlinarith only [hl,hg,mul_nonneg (sq_nonneg a) (sq_nonneg ‖z‖)]
  have hInv : ‖R⁻¹‖ ≤ 2/a := by
    apply norm_le_of_pointwise _ _ (by positivity)
    intro z
    have hh := hRlow (R⁻¹.toEuclideanLin z)
    change (a/2)*‖R⁻¹.toEuclideanLin z‖ ≤ ‖(R.toEuclideanLin ∘ₗ R⁻¹.toEuclideanLin) z‖ at hh
    rw [← Matrix.toLpLin_mul 2 2 2, R.mul_nonsing_inv hdet, Matrix.toLpLin_one] at hh
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]
    change (a/2)*‖R⁻¹.toEuclideanLin z‖ ≤ ‖z‖ at hh
    linarith
  refine ⟨hdet,hInv,?_⟩
  let F := Xᵀ*X - Rᵀ*R
  have hFn : ‖F‖ ≤ e := by simpa only [F,norm_sub_rev] using he
  have hID : (X*R⁻¹)ᵀ * (X*R⁻¹) - 1 = R⁻¹ᵀ * F * R⁻¹ := by
    have rr : R⁻¹ᵀ * (Rᵀ*R) * R⁻¹ = 1 := by
      rw [← Matrix.mul_assoc, ← transpose_mul, R.mul_nonsing_inv hdet, transpose_one,
        Matrix.one_mul, R.mul_nonsing_inv hdet]
    dsimp only [F]
    rw [Matrix.mul_sub, Matrix.sub_mul, rr, transpose_mul]
    simp [Matrix.mul_assoc]
  rw [hID]
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  calc
    _ ≤ (‖R⁻¹ᵀ‖ * ‖F‖) * ‖R⁻¹‖ := (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (2/a * e) * (2/a) := by rw [transpose_opNorm]; gcongr
    _ = _ := by ring

end
end RPHOSVD.Mixed
