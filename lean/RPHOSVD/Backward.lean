import RPHOSVD.MixedAsymptotic

/-! Same-precision division followed by multiplication: scaling back the columns
removes the inverse retained singular values from the forward-error bound. -/
namespace RPHOSVD.Mixed
open Matrix
noncomputable section

private theorem gamma_accumulate (n : ℕ) (u : ℝ) (hu : 0 ≤ u) (hn : ((n+1:ℕ):ℝ)*u < 1) :
    0 ≤ gamma n u ∧ gamma n u * (1+u) + u ≤ gamma (n+1) u := by
  have hdim : (n:ℝ)*u < 1 := by push_cast at hn; nlinarith
  have hd := sub_pos.mpr hdim
  have hd' := sub_pos.mpr hn
  unfold gamma
  refine ⟨div_nonneg (by positivity) hd.le, ?_⟩
  calc
    _ = (((n+1:ℕ):ℝ)*u) / (1-(n:ℝ)*u) := by push_cast; field_simp; ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by positivity) hd'
      push_cast
      linarith

/-- The components contributing to the appendix's scaled bound. Division
roundings can differ by column and row. A nonzero diagonal is necessary only
to identify the represented singular directions. -/
theorem scaled_roundoff_entries {m n t : ℕ} (H : Mat m n) (V T : Mat n t)
    (X : Mat m t) (d : Fin t → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hn : ((n+1:ℕ):ℝ)*u < 1) (hd : ∀ j, 0 < d j)
    (hdiv : ∀ i j, ∃ δ : ℝ, |δ| ≤ u ∧ T i j = (V i j / d j)*(1+δ))
    (hx : StoredProduct u H T X) (i : Fin m) (j : Fin t) :
    |(X * diagonal d - H * V) i j| ≤ gamma (n+1) u * (magnitude H * magnitude V) i j := by
  have hδ k : |T k j * d j - V k j| ≤ |V k j| * u := by
    obtain ⟨δ, he, eq⟩ := hdiv k j
    have e : T k j * d j - V k j = V k j * δ := by rw [eq]; field_simp [(hd j).ne']; ring
    rw [e, abs_mul]
    exact mul_le_mul_of_nonneg_left he (abs_nonneg _)
  have hs k : |T k j| * d j ≤ |V k j| * (1+u) := by
    have h₁ := abs_add_le (T k j * d j - V k j) (V k j)
    rw [sub_add_cancel, abs_mul, abs_of_pos (hd j)] at h₁
    linarith [hδ k]
  let F := X - H*T
  let A := (magnitude H * magnitude V) i j
  have hA : 0 ≤ A := by
    change 0 ≤ ∑ k, |H i k| * |V k j|
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have prod : (magnitude H * magnitude T) i j * d j ≤ A*(1+u) := by
    dsimp only [A]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    simpa [magnitude, mul_assoc] using mul_le_mul_of_nonneg_left (hs k) (abs_nonneg (H i k))
  have hx' : |F i j| * d j ≤ gamma n u * (A*(1+u)) := by
    calc
      _ ≤ (gamma n u * (magnitude H * magnitude T) i j) * d j :=
        mul_le_mul_of_nonneg_right (hx i j) (hd j).le
      _ = gamma n u * ((magnitude H * magnitude T) i j * d j) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left prod (gamma_accumulate n u hu hn).1
  have hlinear : |∑ k, H i k * (T k j * d j - V k j)| ≤ A*u := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    change _ ≤ (∑ k, |H i k| * |V k j|) * u
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hδ k) (abs_nonneg _)
  have hid : (X * diagonal d - H * V) i j =
      F i j * d j + ∑ k, H i k * (T k j * d j - V k j) := by
    rw [Matrix.sub_apply, Matrix.mul_diagonal]
    simp only [F, Matrix.sub_apply, Matrix.mul_apply,
      sub_mul, Finset.sum_mul, mul_sub, Finset.sum_sub_distrib, mul_assoc]
    ring
  rw [hid]
  have h := abs_add_le (F i j*d j) (∑ k, H i k*(T k j*d j-V k j))
  rw [abs_mul, abs_of_pos (hd j)] at h
  calc
    _ ≤ gamma n u * (A*(1+u)) + A*u := h.trans (add_le_add hx' hlinear)
    _ = (gamma n u*(1+u)+u) * A := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (gamma_accumulate n u hu hn).2 hA

open scoped Matrix.Norms.Frobenius in
/-- Frobenius norm of a real matrix from the sum of squares. -/
private theorem frobenius_as_sqrt {m n : ℕ} (A : Mat m n) : ‖A‖ = Real.sqrt (frobSq A) := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp [frobSq, Real.norm_eq_abs]

/-- The division and multiplication errors contribute at most
γ_(n+1) √t ‖H‖_F to the scaled error irrespective of the conditioning of H. -/
theorem scaled_roundoff_frob {m n t : ℕ} (H : Mat m n) (V T : Mat n t)
    (X : Mat m t) (d : Fin t → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hn : ((n+1:ℕ):ℝ)*u < 1) (hd : ∀ j, 0 < d j) (hV : Vᵀ * V = 1)
    (hdiv : ∀ i j, ∃ δ : ℝ, |δ| ≤ u ∧ T i j = (V i j / d j)*(1+δ))
    (hx : StoredProduct u H T X) :
    Real.sqrt (frobSq (X * diagonal d - H * V)) ≤
      gamma (n+1) u * Real.sqrt t * Real.sqrt (frobSq H) := by
  let E := X * diagonal d - H * V
  let A := magnitude H * magnitude V
  have hγ : 0 ≤ gamma (n+1) u := div_nonneg (by positivity) (sub_pos.mpr hn).le
  have he : frobSq E ≤ gamma (n+1) u ^ 2 * frobSq A := by
    unfold frobSq
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    simpa only [sq_abs, mul_pow] using
      pow_le_pow_left₀ (abs_nonneg _) (scaled_roundoff_entries H V T X d u hu hn hd hdiv hx i j) 2
  have hmag {a b : ℕ} (Q : Mat a b) : frobSq (magnitude Q) = frobSq Q := by simp [frobSq, magnitude]
  have hV2 : frobSq V = t := by
    unfold frobSq
    rw [Finset.sum_comm]
    have hcol (j : Fin t) : ∑ i, V i j ^ 2 = 1 := by
      simpa [Matrix.mul_apply, sq] using congrArg (fun A : Mat t t => A j j) hV
    simp [hcol]
  have hA := Matrix.frobenius_norm_mul (magnitude H) (magnitude V)
  rw [frobenius_as_sqrt, frobenius_as_sqrt, frobenius_as_sqrt, hmag, hmag, hV2] at hA
  have hq := Real.sqrt_le_sqrt he
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hγ] at hq
  exact hq.trans (by simpa [mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_left hA hγ)

open scoped Matrix.Norms.L2Operator

theorem opNorm_le_frob {m n : ℕ} (A : Mat m n) : ‖A‖ ≤ Real.sqrt (frobSq A) := by
  apply norm_le_of_pointwise _ _ (Real.sqrt_nonneg _)
  intro z
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (frobSq_nonneg _), EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  unfold frobSq
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  change (∑ j, A i j * z j)^2 ≤ _
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) (fun j => z j)

private theorem retained_sketch_coordinates {s n t : ℕ} (Y : Mat s n) (V : Mat n t)
    (ε : ℝ) (hε : 0 < ε) (hV : LeadingRight Y V) (hs : ∀ j : Fin t, ε < sigma Y j.val) :
    let D := inverseScales Y t
    let T := V * D
    let U := Y * T
    Uᵀ * U = 1 ∧ ‖V‖ ≤ 1 ∧ ‖D‖ ≤ 1/ε := by
  let D := inverseScales Y t
  let T := V * D
  let U := Y * T
  have hσ (j : Fin t) : sigma Y j.val ≠ 0 := (hε.trans (hs j)).ne'
  have hU : Uᵀ * U = 1 := by
    change (Y * (V * D))ᵀ * (Y * (V * D)) = 1
    rw [transpose_mul, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Yᵀ Y,
      ← Matrix.mul_assoc (Yᵀ * Y) V, hV.2.2]
    change (diagonal _ )ᵀ * Vᵀ * (V * diagonal _ * diagonal _) = 1
    rw [diagonal_transpose, Matrix.mul_assoc, Matrix.mul_assoc V, ← Matrix.mul_assoc Vᵀ V,
      hV.2.1, Matrix.one_mul, diagonal_mul_diagonal, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext j
    simp [sq, hσ j]
  have hVn : ‖V‖ ≤ 1 := norm_le_of_pointwise V 1 zero_le_one fun x => by
    simp [norm_of_orthonormal_columns V hV.2.1]
  have hDn : ‖D‖ ≤ 1 / ε := by
    change ‖diagonal _‖ ≤ 1 / ε
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 1 / ε)).mpr
    intro j
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hε.trans (hs j))), one_div]
    exact inv_anti₀ hε (hs j).le

  exact ⟨hU,hVn,hDn⟩

/-- Same-precision computed X is well conditioned once the sketch error is
below half the threshold and the scaled multiplication error is below the
displayed fraction of that threshold. The input errors are in Frobenius norm. -/
theorem computed_conditioning {m n s t : ℕ} (H : Mat m n) (S : Mat s m) (Y : Mat s n)
    (V : Mat n t) (X : Mat m t) (η ε : ℝ) (hη : 0 ≤ η) (hη' : η < 1) (hε : 0 < ε)
    (hemb : EmbedsRange η S H) (hV : LeadingRight Y V) (hs : ∀ j : Fin t, ε < sigma Y j.val)
    (hsketch : Real.sqrt (frobSq (Y-S*H)) ≤ ε/2)
    (hscaled : Real.sqrt (frobSq (X*scales Y t-H*V)) ≤ ε/(4*Real.sqrt (1+η))) :
    (∀ z : EuclideanSpace ℝ (Fin t),
      (1/(4*Real.sqrt (1+η))) * ‖z‖ ≤ ‖Matrix.toEuclideanLin X z‖) ∧
      ‖X‖ ≤ 3/(2*Real.sqrt (1-η)) + 1 := by
  let D := inverseScales Y t
  let T := V * D
  let X₀ := H*T
  let U := Y*T
  let N := (Y-S*H)*T
  have hp : 0 < 1+η := by linarith
  have hp' : 0 < Real.sqrt (1+η) := Real.sqrt_pos.mpr hp
  have hm' : 0 < Real.sqrt (1-η) := Real.sqrt_pos.mpr (sub_pos.mpr hη')
  obtain ⟨hU,hVn,hDn⟩ := retained_sketch_coordinates Y V ε hε hV hs
  have hN : ‖N‖ ≤ 1/2 := by
    calc
      _ ≤ ‖Y-S*H‖ * ‖V*D‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (ε/2) * (1 * (1/ε)) := mul_le_mul ((opNorm_le_frob _).trans hsketch)
        ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hVn hDn (norm_nonneg _) zero_le_one))
        (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hc (z : EuclideanSpace ℝ (Fin t)) :
      ‖z‖ / (2*Real.sqrt (1+η)) ≤ ‖Matrix.toEuclideanLin X₀ z‖ ∧
      ‖Matrix.toEuclideanLin X₀ z‖ ≤ 3*‖z‖/(2*Real.sqrt (1-η)) := by
    apply noisy_conditioning S X₀ U N η hη hη' _ (norm_of_orthonormal_columns _ hU) hN z
    · have he := hemb (Matrix.toEuclideanLin T z)
      have comp {a b c : ℕ} (A : Mat a b) (B : Mat b c) (w : EuclideanSpace ℝ (Fin c)) :
          A.toEuclideanLin (B.toEuclideanLin w) = (A*B).toEuclideanLin w := by
        apply WithLp.ofLp_injective
        exact mulVec_mulVec w.ofLp A B
      dsimp only at he
      rw [comp,comp] at he
      constructor
      · apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
        simpa [X₀,mul_pow,Real.sq_sqrt (sub_nonneg.mpr hη'.le)] using he.1
      · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
        simpa [X₀,mul_pow,Real.sq_sqrt hp.le] using he.2
    · simp [X₀,U,N,Matrix.sub_mul,Matrix.mul_assoc]
  have hσ (j : Fin t) : sigma Y j.val ≠ 0 := (hε.trans (hs j)).ne'
  have hcancel : scales Y t * D = 1 := by
    simp [scales,D,inverseScales,diagonal_mul_diagonal,hσ]
  have hE : ‖X-X₀‖ ≤ 1/(4*Real.sqrt (1+η)) := by
    have hid : (X*scales Y t-H*V)*D = X-X₀ := by simp [X₀,T,Matrix.sub_mul,Matrix.mul_assoc,hcancel]
    rw [← hid]
    calc
      _ ≤ ‖X*scales Y t-H*V‖ * ‖D‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (ε/(4*Real.sqrt (1+η))) * (1/ε) := mul_le_mul ((opNorm_le_frob _).trans hscaled)
        hDn (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  have ed : (1/(4*Real.sqrt (1+η))) ≤ 1 := by
    have hr : 1 ≤ Real.sqrt (1+η) := by
      apply (sq_le_sq₀ zero_le_one hp'.le).mp
      rw [Real.sq_sqrt hp.le]
      linarith
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  constructor
  · intro z
    have hb := Matrix.l2_opNorm_mulVec (X-X₀) z
    change ‖Matrix.toEuclideanLin (X-X₀) z‖ ≤ _ at hb
    rw [map_sub,LinearMap.sub_apply] at hb
    have hh := norm_sub_norm_le (Matrix.toEuclideanLin X₀ z) (Matrix.toEuclideanLin X z)
    rw [norm_sub_rev] at hh
    have scale : ‖z‖ / (2*Real.sqrt (1+η)) = 2 * ((1/(4*Real.sqrt (1+η))) * ‖z‖) := by ring
    have hmin := (hc z).1
    rw [scale] at hmin
    linarith [mul_le_mul_of_nonneg_right hE (norm_nonneg z)]
  · have hx : ‖X₀‖ ≤ 3/(2*Real.sqrt (1-η)) := by
      apply norm_le_of_pointwise _ _ (by positivity)
      intro z
      convert (hc z).2 using 1
      ring
    have hn := norm_add_le (X-X₀) X₀
    rw [sub_add_cancel] at hn
    linarith

/-- A global, dimension-only upper bound for the coefficient of u in the
scaled error and a concrete threshold constant for the computed conditioning. -/
theorem backward_conditioning_threshold {m n s t : ℕ}
    (H : Mat m n) (S : Mat s m) (Y E : Mat s n) (V T : Mat n t) (X : Mat m t)
    (η u c α a : ℝ) (hη : 0 ≤ η) (hη' : η < 1) (hu : 0 < u) (hα : 0 < α)
    (hH : 0 < Real.sqrt (frobSq H))
    (hsz : α * Real.sqrt (frobSq H) ≤ ‖Y‖)
    (hes : Real.sqrt (frobSq (Y+E - S*H)) ≤ a*u*Real.sqrt (frobSq H))
    (hn : ((n+1:ℕ):ℝ) * u ≤ 1/2)
    (cpos : 0 < c) (ca : 2*a ≤ c*α)
    (cb : 4*Real.sqrt (1+η) * (2*((n+1:ℕ):ℝ)*(n+1:ℝ)) ≤ c*α)
    (hemb : EmbedsRange η S H) (hV : LeadingRight (Y+E) V)
    (hcount : t = (Finset.univ.filter (fun j : Fin n => c*u*‖Y‖ < sigma (Y+E) j.val)).card)
    (hdiv : ∀ i j, ∃ δ : ℝ, |δ| ≤ u ∧ T i j = (V i j / sigma (Y+E) j.val)*(1+δ))
    (hX : StoredProduct u H T X) :
    (∀ z : EuclideanSpace ℝ (Fin t), (1/(4*Real.sqrt (1+η))) * ‖z‖ ≤ ‖X.toEuclideanLin z‖) ∧
    ‖X‖ ≤ 3/(2*Real.sqrt (1-η)) + 1 ∧
    Real.sqrt (frobSq (X*scales (Y+E) t-H*V)) ≤
      (2*((n+1:ℕ):ℝ)*(n+1:ℝ))*u*Real.sqrt (frobSq H) := by
  let f := Real.sqrt (frobSq H)
  let ε := c*u*‖Y‖
  have hY : 0 < ‖Y‖ := (mul_pos hα hH).trans_le hsz
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hs j := retained_gt (Y+E) ε hV.1 hcount j
  have hp : 0 < Real.sqrt (1+η) := Real.sqrt_pos.mpr (by linarith)
  have hT : Real.sqrt t ≤ n+1 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg _)]
    have ht : (t:ℝ) ≤ n := by exact_mod_cast hV.1
    nlinarith [sq_nonneg (n:ℝ), Nat.cast_nonneg (α:=ℝ) n]
  have hscale := scaled_roundoff_frob H V T X (fun j : Fin t => sigma (Y+E) j.val) u hu.le
    (by linarith) (fun j => hε.trans (hs j)) hV.2.1 hdiv hX
  have hg := (gamma_upper (n+1) u hu.le hn).2
  have hb : Real.sqrt (frobSq (X*scales (Y+E) t-H*V)) ≤
      (2*((n+1:ℕ):ℝ)*(n+1:ℝ))*u*f := by
    apply hscale.trans
    calc
      _ ≤ ((2*((n+1:ℕ):ℝ))*u) * (n+1:ℝ) * f := by gcongr
      _ = _ := by ring
  have hth : c*α*(u*f) ≤ ε := by
    change _ ≤ c*u*‖Y‖
    have h := mul_le_mul_of_nonneg_left hsz (mul_pos cpos hu).le
    linarith only [h]
  have h1 : Real.sqrt (frobSq (Y+E-S*H)) ≤ ε/2 := by
    have hca := mul_le_mul_of_nonneg_right ca (mul_nonneg hu.le hH.le)
    change _ ≤ a*u*f at hes
    nlinarith only [hes,hth,hca]
  have h2 : Real.sqrt (frobSq (X*scales (Y+E) t-H*V)) ≤ ε/(4*Real.sqrt (1+η)) := by
    apply hb.trans
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ = (4*Real.sqrt (1+η)*(2*((n+1:ℕ):ℝ)*(n+1:ℝ))) * (u*f) := by ring
      _ ≤ c*α*(u*f) := mul_le_mul_of_nonneg_right cb (mul_nonneg hu.le hH.le)
      _ ≤ ε := hth
  obtain ⟨lo,hi⟩ := computed_conditioning H S (Y+E) V X η ε hη hη' hε hemb hV hs h1 h2
  exact ⟨lo,hi,hb⟩

end
end RPHOSVD.Mixed
