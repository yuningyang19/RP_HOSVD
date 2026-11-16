import RPHOSVD.KyFan
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Variational proof of the retained-subspace estimate. -/
namespace RPHOSVD.Projection
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section
variable {m n k r t : ℕ}

private theorem frob_transpose (A : Mat m n) : frobSq Aᵀ = frobSq A := by
  simp only [frobSq, transpose_transpose, trace_mul_comm A Aᵀ]

private theorem frob_frame_left (U : Mat m k) (A : Mat k n) (h : Uᵀ * U = 1) :
    frobSq (U * A) = frobSq A := by
  simp [frobSq, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, h]

private theorem op_frob (A : Mat m n) (C : Mat n k) :
    frobSq (A * C) ≤ opNorm A ^ 2 * frobSq C := by
  have h (i : Fin k) : vecSq ((A * C).col i) ≤ opNorm A ^ 2 * vecSq (C.col i) := by
    let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (C.col i)
    have e := A.toEuclideanLin.toContinuousLinearMap.le_opNorm x
    have e' := pow_le_pow_left₀ (norm_nonneg _) e 2
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at e'
    exact e'
  simpa only [frobSq_cols, Finset.mul_sum] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)

private theorem op_transpose (A : Mat m n) : opNorm Aᵀ = opNorm A := by
  change ‖Aᵀ‖ = ‖A‖
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial]
    using Matrix.l2_opNorm_conjTranspose A

private theorem frob_add_le_two (A B : Mat m n) :
    frobSq (A + B) ≤ 2 * frobSq A + 2 * frobSq B := by
  simp only [frobSq_cols, vecSq, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro i _
  change (A i j + B i j)^2 ≤ 2 * A i j ^ 2 + 2 * B i j ^ 2
  nlinarith [sq_nonneg (A i j - B i j)]

private theorem diag_restrict (A : Mat m n) (W : Mat n n) (hW : RightBasis A W) (hk : k ≤ n) :
    (Aᵀ * A) * firstCols W hk = firstCols W hk * diagonal (fun i : Fin k => sigma A i.val ^ 2) := by
  ext i j
  have h := congrArg (fun M : Mat n n => M i (Fin.castLE hk j)) hW.2.2
  rw [Matrix.mul_diagonal] at h ⊢
  exact h

private theorem normalize_left (A : Mat m n) (W : Mat n n) (hW : RightBasis A W)
    (hk : k ≤ n) (hp : ∀ i : Fin k, 0 < sigma A i.val) :
    ∃ L : Mat m k, Lᵀ * L = 1 ∧
      L * diagonal (fun i : Fin k => sigma A i.val) = A * firstCols W hk ∧
      Aᵀ * L = firstCols W hk * diagonal (fun i : Fin k => sigma A i.val) := by
  let C := firstCols W hk
  let S := diagonal (fun i : Fin k => sigma A i.val)
  let J := diagonal (fun i : Fin k => (sigma A i.val)⁻¹)
  have hC : Cᵀ * C = 1 := firstCols_orthonormal _ _ hW.1
  have hJS : J * S = 1 := by simp [J, S, diagonal_mul_diagonal, (hp _).ne']
  have he : Aᵀ * (A * C) = C * (S * S) := by
    simpa [← Matrix.mul_assoc Aᵀ, S, diagonal_mul_diagonal, pow_two] using diag_restrict A W hW hk
  have hL : Aᵀ * (A * C * J) = C * S := by
    rw [← Matrix.mul_assoc Aᵀ, he, Matrix.mul_assoc, Matrix.mul_assoc S]
    have hSJ : S * J = 1 := by simp [J, S, diagonal_mul_diagonal, (hp _).ne']
    rw [hSJ, Matrix.mul_one]
  refine ⟨A * C * J, ?_, ?_, hL⟩
  · rw [transpose_mul, transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, hL,
      ← Matrix.mul_assoc Cᵀ, hC, Matrix.one_mul]
    simpa [J] using hJS
  · rw [Matrix.mul_assoc, hJS, Matrix.mul_one]

private theorem frob_diag (s : Fin k → ℝ) : frobSq (diagonal s) = ∑ i, s i ^ 2 := by
  simp [frobSq, diagonal_mul_diagonal, pow_two]

/-- Left-frame attainment, obtained by normalizing the nonzero top right singular
vectors. No independent left SVD witness is required. -/
theorem exists_leftFrame_head (A : Mat m n) (hk : k ≤ A.rank) :
    ∃ X : Mat m k, Xᵀ * X = 1 ∧ frobSq (Aᵀ * X) = ∑ i : Fin k, sigma A i.val ^ 2 := by
  obtain ⟨W, hW⟩ := exists_rightBasis A
  have hkn : k ≤ n := hk.trans (by simpa using A.rank_le_card_width)
  have eqRank := A.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hp (i : Fin k) : 0 < sigma A i.val := A.toEuclideanLin.singularValues_pos_iff_lt_finrank_range.mpr
    (i.isLt.trans_le (hk.trans_eq eqRank))
  obtain ⟨X,hX,_,h⟩ := normalize_left A W hW hkn hp
  refine ⟨X,hX,?_⟩
  rw [h, frob_frame_left _ _ (firstCols_orthonormal _ _ hW.1), frob_diag]

private theorem weighted_deficit (a : ℕ → ℝ) (w : Fin t → ℝ) (hr : r ≤ t)
    (ha : Antitone a) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) :
    (∑ i, a i.val * w i) + a (r-1) * (r - ∑ i, w i) ≤ ∑ i : Fin r, a i.val := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  let p := a (r-1)
  have h₁ (i : Fin r) : a i.val * w (Fin.castAdd d i) ≤
      a i.val + p * (w (Fin.castAdd d i) - 1) := by
    have he : i.val ≤ r-1 := by omega
    have h := mul_nonneg (sub_nonneg.mpr (ha he)) (sub_nonneg.mpr (hw (Fin.castAdd d i)).2)
    dsimp [p]
    nlinarith only [h]
  have h₂ (i : Fin d) : a (r + i.val) * w (Fin.natAdd r i) ≤ p * w (Fin.natAdd r i) :=
    mul_le_mul_of_nonneg_right (ha (by omega)) (hw _).1
  have e₁ := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h₁ i)
  have e₂ := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h₂ i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at e₁ e₂
  simp only [Fin.sum_univ_add, Fin.val_castAdd, Fin.val_natAdd, p] at *
  linarith only [e₁, e₂]

private theorem ortho_properties (Q : Mat m t) (hQ : Qᵀ * Q = 1) :
    (projector Q)ᵀ = projector Q ∧ projector Q * projector Q = projector Q := by
  constructor <;> simp [projector, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ Q, hQ]

private theorem frame_energy (X : Mat m r) (hX : Xᵀ * X = 1) : frobSq X = r := by
  simp [frobSq, hX]

private theorem project_frame_split (X : Mat m r) (L : Mat m t) (hL : Lᵀ * L = 1) :
    frobSq X = frobSq ((1 - projector L) * X) + frobSq (Lᵀ * X) := by
  obtain ⟨hs, hi⟩ := ortho_properties _ hL
  have h := frobSplit Xᵀ (projector L) hs hi
  have hls : frobSq (projector L * X) = frobSq (Lᵀ * X) := by
    rw [projector, Matrix.mul_assoc, frob_frame_left _ _ hL]
  rw [← hls, ← frob_transpose ((1 - projector L) * X), ← frob_transpose (projector L * X)]
  simpa only [frob_transpose, transpose_mul, transpose_sub, transpose_one, hs] using h

private theorem project_fixes_range (L : Mat m t) (hL : Lᵀ * L = 1) {B : Mat m k}
    (hb : LinearMap.range B.mulVecLin ≤ LinearMap.range L.mulVecLin) : projector L * B = B := by
  ext i j
  have hj : B.col j ∈ LinearMap.range B.mulVecLin := ⟨Pi.single j 1, Matrix.mulVec_single_one B j⟩
  obtain ⟨x, hx⟩ := hb hj
  change L *ᵥ x = B.col j at hx
  have hy : (projector L) *ᵥ B.col j = B.col j := by
    rw [← hx, mulVec_mulVec, projector, Matrix.mul_assoc, hL, Matrix.mul_one]
  exact congrFun hy i

private theorem frame_range_factor (A : Mat m t) (U : Mat t t) (hU : RightBasis A U)
    (hp : ∀ i : Fin t, 0 < sigma A i.val) :
    ∃ L : Mat m t, Lᵀ * L = 1 ∧ LinearMap.range L.mulVecLin = LinearMap.range A.mulVecLin ∧
      A = L * diagonal (fun i : Fin t => sigma A i.val) * Uᵀ := by
  obtain ⟨L, hL,he,_⟩ := normalize_left A U hU (le_refl t) hp
  change L * diagonal (fun i : Fin t => sigma A i.val) = A * U at he
  let S := diagonal (fun i : Fin t => sigma A i.val)
  let J := diagonal (fun i : Fin t => (sigma A i.val)⁻¹)
  have he' : L * S = A * U := he
  have hSJ : S * J = 1 := by simp [S, J, diagonal_mul_diagonal, (hp _).ne']
  have hA : A = L * S * Uᵀ := by rw [he', Matrix.mul_assoc, hU.2.1, Matrix.mul_one]
  have hL' : L = A * (U * J) := by rw [← Matrix.mul_assoc, ← he', Matrix.mul_assoc, hSJ, Matrix.mul_one]
  refine ⟨L, hL, le_antisymm ?_ ?_, hA⟩
  · rw [hL', Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · rw [hA, Matrix.mul_assoc, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _

private theorem retained_deficit (A : Mat m t) (U : Mat t t) (L : Mat m t) (X : Mat m r)
    (hU : RightBasis A U) (hL : Lᵀ * L = 1) (hX : Xᵀ * X = 1)
    (hA : A = L * diagonal (fun i : Fin t => sigma A i.val) * Uᵀ) (hr : r ≤ t) :
    frobSq (Aᵀ * X) + sigma A (r-1)^2 * frobSq ((1 - projector L) * X) ≤
      ∑ i : Fin r, sigma A i.val ^ 2 := by
  let T := Lᵀ * X
  let w := fun i : Fin t => vecSq (Tᵀ.col i)
  have hw (i : Fin t) : 0 ≤ w i ∧ w i ≤ 1 := by
    refine ⟨Finset.sum_nonneg (fun j _ => sq_nonneg _), ?_⟩
    let E : Mat m 1 := Matrix.of fun j _ => L j i
    have hE : frobSq E = 1 := by
      have hii := congrArg (fun M : Mat t t => M i i) hL
      simp [frobSq_cols, E, vecSq, Matrix.col, pow_two, Matrix.mul_apply] at hii ⊢
      exact hii
    have hs := project_frame_split E X hX
    have hn : 0 ≤ frobSq ((1 - projector X) * E) := by
      rw [frobSq_cols]
      exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have he : frobSq (Xᵀ * E) = w i := by
      simp [frobSq_cols, vecSq, w, T, E, Matrix.col, Matrix.mul_apply, mul_comm]
    linarith
  have hsum : ∑ i, w i = frobSq T := by rw [← frob_transpose T, frobSq_cols]
  have hweighted : frobSq (Aᵀ * X) = ∑ i : Fin t, sigma A i.val ^ 2 * w i := by
    have he : Aᵀ * X = U * (diagonal (fun i : Fin t => sigma A i.val) * T) := by
      conv_lhs => rw [hA, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose]
      simp [T, Matrix.mul_assoc]
    rw [he, frob_frame_left _ _ hU.1, ← frob_transpose (diagonal _ * T), frobSq_cols]
    simp only [transpose_mul, diagonal_transpose, vecSq, Matrix.col, transpose_transpose, Matrix.diagonal_mul,
      mul_pow, w, Finset.mul_sum]
  have hd := weighted_deficit (fun i => sigma A i ^ 2) w hr
    (fun i j hij => pow_le_pow_left₀ (A.toEuclideanLin.singularValues_nonneg _) (A.toEuclideanLin.singularValues_antitone hij) 2) hw
  rw [← hweighted, hsum] at hd
  have hs := project_frame_split X L hL
  rw [frame_energy _ hX] at hs
  have he : (r : ℝ) - frobSq T = frobSq ((1-projector L)*X) := by dsimp [T]; linarith only [hs]
  rwa [he] at hd

private theorem full_column_rank (A : Mat m t) (hA : Function.Injective A.mulVecLin) : A.rank = t := by
  rw [Matrix.rank, LinearMap.finrank_range_of_inj hA]
  simp

private theorem full_sigma_pos (A : Mat m t) (hA : Function.Injective A.mulVecLin) (i : Fin t) :
    0 < sigma A i.val := by
  have hr := A.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin t) ℝ).toBasis
  rw [full_column_rank A hA] at hr
  exact A.toEuclideanLin.singularValues_pos_iff_lt_finrank_range.mpr (i.isLt.trans_eq hr)

/-- Every full-column-rank matrix has an orthonormal frame spanning its range. -/
theorem exists_rangeFrame (A : Mat m t) (hA : Function.Injective A.mulVecLin) :
    ∃ Q : Mat m t, Qᵀ * Q = 1 ∧ LinearMap.range Q.mulVecLin = LinearMap.range A.mulVecLin := by
  obtain ⟨U,hU⟩ := exists_rightBasis A
  obtain ⟨Q,hQ,hR,_⟩ := frame_range_factor A U hU (full_sigma_pos A hA)
  exact ⟨Q,hQ,hR⟩

private theorem residual_head (H : Mat m n) (V : Mat n t) (U : Mat t t)
    (hV : Vᵀ * V = 1) (hU : RightBasis (H * V) U) (hr : r ≤ t) :
    frobSq (H - H * V * projector (firstCols U hr) * Vᵀ) =
      frobSq H - ∑ i : Fin r, sigma (H * V) i.val ^ 2 := by
  let C := firstCols U hr
  let B := V * C
  have hc : Cᵀ * C = 1 := firstCols_orthonormal _ _ hU.1
  have hb : Bᵀ * B = 1 := by
    simp [B, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V, hV, hc]
  obtain ⟨hs, hi⟩ := ortho_properties B hb
  have he := frobSplit H (projector B) hs hi
  have hcap : frobSq (H * projector B) = ∑ i : Fin r, sigma (H * V) i.val ^ 2 := by
    rw [projector, ← Matrix.mul_assoc, rightFrameEnergy _ _ hb, show H * B = H * V * C by
      simp only [B, Matrix.mul_assoc], frobSq_cols]
    exact Finset.sum_congr rfl (fun i _ => basisColumnEnergy hU (Fin.castLE hr i))
  have hres : H - H * V * projector C * Vᵀ = H * (1 - projector B) := by
    simp [B, projector, Matrix.mul_assoc, Matrix.mul_sub, transpose_mul]
  rw [hres]
  linarith only [hcap, he]

private theorem energies_split (C : Mat n r) (V : Mat n t) (D : Mat n k)
    (h : projector V + projector D = 1) :
    frobSq C = frobSq (Vᵀ * C) + frobSq (Dᵀ * C) := by
  simp only [frobSq, transpose_mul, transpose_transpose]
  rw [← trace_add, Matrix.mul_assoc Cᵀ V, Matrix.mul_assoc Cᵀ D, ← Matrix.mul_add,
      ← Matrix.mul_assoc V, ← Matrix.mul_assoc D]
  change _ = (Cᵀ * ((V * Vᵀ) * C + (D * Dᵀ) * C)).trace
  rw [← Matrix.add_mul]
  change _ = (Cᵀ * ((projector V + projector D) * C)).trace
  rw [h, Matrix.one_mul]

/-- Lemma 4.4. The energy paid outside the retained left range is cancelled by
the loss in captured retained energy under the manuscript's separation inequality. -/
theorem retainedSubspace : retainedSubspaceClaim := by
  intro m n r t H V D Q U hr _ htn hV _ _ hVD hA hQ hQR hU hgap
  let A := H * V
  let E := H * D
  obtain ⟨L,hL,hLR,hfact⟩ := frame_range_factor A U hU (full_sigma_pos A hA)
  have hrH : r ≤ H.rank := hr.trans ((full_column_rank A hA).ge.trans (Matrix.rank_mul_le_left H V))
  obtain ⟨X, hX, hmax⟩ := exists_leftFrame_head H hrH
  let N := (1 - projector L) * X
  have hspan : LinearMap.range L.mulVecLin ≤ LinearMap.range Q.mulVecLin := by rw [hLR, hQR]
  have hQL := project_fixes_range Q hQ hspan
  have hR : projector L * X = Q * (Qᵀ * (projector L * X)) := by
    have he : projector Q * projector L = projector L := by
      change projector Q * (L * Lᵀ) = L * Lᵀ
      rw [← Matrix.mul_assoc, hQL]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← projector, he]
  have hsplit : Eᵀ * X = (Qᵀ * E)ᵀ * (Qᵀ * (projector L * X)) + Eᵀ * N := by
    rw [transpose_mul Qᵀ E, transpose_transpose, Matrix.mul_assoc Eᵀ Q, ← hR, ← Matrix.mul_add]
    congr 1
    simp [N, Matrix.sub_mul]
  have hnon {a b : ℕ} (M : Mat a b) : 0 ≤ frobSq M := by
    rw [frobSq_cols]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hLenergy : frobSq (projector L * X) ≤ r := by
    rw [projector, Matrix.mul_assoc, frob_frame_left _ _ hL]
    have h := project_frame_split X L hL
    rw [frame_energy X hX] at h
    linarith [hnon N]
  have hQenergy : frobSq (Qᵀ * (projector L * X)) ≤ r := by
    have h := project_frame_split (projector L * X) Q hQ
    linarith [hnon ((1 - projector Q) * (projector L * X))]
  have hdiscard : frobSq (Eᵀ * X) ≤ 2 * (r : ℝ) * opNorm (Qᵀ * E) ^ 2 +
      sigma A (r-1)^2 * frobSq N := by
    rw [hsplit]
    have h1 := op_frob (Qᵀ * E)ᵀ (Qᵀ * (projector L * X))
    have h2 := op_frob Eᵀ N
    rw [op_transpose] at h1 h2
    have h3 := mul_le_mul_of_nonneg_left hQenergy (sq_nonneg (opNorm (Qᵀ * E)))
    have h4 := mul_le_mul_of_nonneg_right hgap (hnon N)
    change opNorm E ^ 2 * frobSq N ≤ (sigma A (r-1)^2 / 2) * frobSq N at h4
    linarith only [frob_add_le_two ((Qᵀ * E)ᵀ * (Qᵀ * (projector L * X))) (Eᵀ * N), h1,h2,h3,h4]
  have hdef := retained_deficit A U L X hU hL hX hfact hr
  change frobSq (Aᵀ * X) + sigma A (r-1)^2 * frobSq N ≤ _ at hdef
  have hpart := energies_split (Hᵀ * X) V D hVD
  change frobSq (Hᵀ * X) = frobSq (Vᵀ * (Hᵀ * X)) + frobSq (Dᵀ * (Hᵀ * X)) at hpart
  rw [← Matrix.mul_assoc, ← transpose_mul, ← Matrix.mul_assoc, ← transpose_mul] at hpart
  change frobSq (Hᵀ * X) = frobSq (Aᵀ * X) + frobSq (Eᵀ * X) at hpart
  have htail : frobSq H = tailEnergy H r + ∑ i : Fin r, sigma H i.val ^ 2 := by
    obtain ⟨W,hW⟩ := exists_rightBasis H
    rw [fullBasisEnergy hW]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (hr.trans htn)
    simp [tailEnergy, Fin.sum_univ_add, Fin.castAdd, add_comm, fun i : Fin r => i.isLt.not_ge]
  rw [residual_head H V U hV hU hr]
  change frobSq H - (∑ i : Fin r, sigma A i.val ^ 2) ≤ tailEnergy H r + 2 * (r : ℝ) * opNorm (Qᵀ * H * D)^2
  rw [Matrix.mul_assoc Qᵀ H D]
  change _ ≤ tailEnergy H r + 2 * (r : ℝ) * opNorm (Qᵀ * E)^2
  linarith only [hmax,htail,hpart,hdiscard,hdef]

end
end RPHOSVD.Projection
