import Mathlib

/-! Mixed precision, in the model with exact small factorizations.
The main inequality is a proposition to be proved. The lemmas below are
individual algebraic and norm estimates used in the manuscript's proofs. -/

namespace RPHOSVD.Mixed

open Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

noncomputable def sigma {m n : ℕ} (A : Mat m n) (j : ℕ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues j

/-- Sum of squared discarded singular values, with zero-based indexing. -/
noncomputable def tailEnergy {m n : ℕ} (A : Mat m n) (r : ℕ) : ℝ :=
  ∑ j : Fin n, if r ≤ j.val then (sigma A j.val) ^ 2 else 0

noncomputable def frobSq {m n : ℕ} (A : Mat m n) : ℝ :=
  ∑ i, ∑ j, (A i j)^2

noncomputable def gamma (k : ℕ) (u : ℝ) : ℝ := (k : ℝ) * u / (1 - (k : ℝ) * u)

noncomputable def magnitude {m n : ℕ} (A : Mat m n) : Mat m n := A.map abs

/-- Componentwise model for a product, including the two input conversions. -/
def RoundedProduct {m k n : ℕ} (u : ℝ) (A : Mat m k) (B : Mat k n) (C : Mat m n) : Prop :=
  ∀ i j, |(C - A * B) i j| ≤ gamma (k + 2) u * (magnitude A * magnitude B) i j

noncomputable def productBudget {m k n : ℕ} (u : ℝ) (A : Mat m k) (B : Mat k n) : ℝ :=
  gamma (k + 2) u * ‖magnitude A * magnitude B‖

def EmbedsRange {s m n : ℕ} (η : ℝ) (S : Mat s m) (H : Mat m n) : Prop :=
  ∀ z : EuclideanSpace ℝ (Fin n),
    let x := Matrix.toEuclideanLin H z
    (1 - η) * ‖x‖^2 ≤ ‖Matrix.toEuclideanLin S x‖^2 ∧
      ‖Matrix.toEuclideanLin S x‖^2 ≤ (1 + η) * ‖x‖^2

/-- The columns are orthonormal right singular vectors for the leading
singular values of A, allowing any orthonormal choice at ties. -/
def LeadingRight {m n k : ℕ} (A : Mat m n) (V : Mat n k) : Prop :=
  k ≤ n ∧ Vᵀ * V = 1 ∧
    (Aᵀ * A) * V = V * Matrix.diagonal (fun j : Fin k => sigma A j.val ^ 2)

noncomputable def scales {s n : ℕ} (Y : Mat s n) (t : ℕ) : Mat t t :=
  Matrix.diagonal (fun j : Fin t => sigma Y j.val)

noncomputable def inverseScales {s n : ℕ} (Y : Mat s n) (t : ℕ) : Mat t t :=
  Matrix.diagonal (fun j : Fin t => (sigma Y j.val)⁻¹)

noncomputable def theta (η dx dg : ℝ) : ℝ :=
  4 * (1 + η) * (3 * dx / Real.sqrt (1 - η) + dx ^ 2 + dg)

/-- The three measured products and the local assumptions of the finite-u
theorem, before computing a Cholesky factor. -/
structure MixedRun {m n s t : ℕ} (H : Mat m n) (S : Mat s m) (Y : Mat s n)
    (V : Mat n t) (X : Mat m t) (G : Mat t t) (η ε u : ℝ) (r : ℕ) : Prop where
  rank_pos : 1 ≤ r
  rank_le : r ≤ n
  distortion_nonneg : 0 ≤ η
  distortion_lt : η < 1
  threshold_pos : 0 < ε
  roundoff_pos : 0 < u
  long_product : ((m + 2 : ℕ) : ℝ) * u < 1
  short_product : ((n + 2 : ℕ) : ℝ) * u < 1
  embedding : EmbedsRange η S H
  sketch : RoundedProduct u S H Y
  target_retained : ε < sigma Y (r - 1)
  retained_count : t = (Finset.univ.filter (fun j : Fin n => ε < sigma Y j.val)).card
  retained_basis : LeadingRight Y V
  precondition : RoundedProduct u H (V * inverseScales Y t) X
  gram : RoundedProduct u Xᵀ X G
  symmetric : Gᵀ = G
  sketch_small : productBudget u S H ≤ ε / 2
  gram_small : theta η (productBudget u H (V * inverseScales Y t))
    (productBudget u Xᵀ X) < 1
  separated : (ε + productBudget u S H)^2 / (1 - η) ≤
    (sigma Y (r - 1) - productBudget u S H)^2 / (2 * (1 + η))

/-- All exact Gram factors give the same right singular information. -/
def Output {s n t r : ℕ} (Y : Mat s n) (V : Mat n t) (G R : Mat t t)
    (Vr : Mat n r) : Prop :=
  Rᵀ * R = G ∧ LeadingRight (R * scales Y t * Vᵀ) Vr

/-- Candidate explicit finite-u target of Theorem prop:mp-recovery. G is the
symmetric matrix after reflecting either triangle. -/
def MixedProjectionBound : Prop :=
  ∀ {m n s r t : ℕ} (H : Mat m n) (S : Mat s m) (Y : Mat s n)
    (V : Mat n t) (X : Mat m t) (G : Mat t t) (η ε u : ℝ),
    MixedRun H S Y V X G η ε u r →
    let ds := productBudget u S H
    let θ := theta η (productBudget u H (V * inverseScales Y t)) (productBudget u Xᵀ X)
    G.PosDef ∧ ∀ (R : Mat t t) (Vr : Mat n r), Output Y V G R Vr →
      frobSq (H - H * (Vr * Vrᵀ)) ≤
        (1 + θ) / (1 - θ) * tailEnergy H r +
        2 * (r : ℝ) * (η * ((ε + ds) / Real.sqrt (1 - η)) +
          3 * Real.sqrt (1 + η) * ds)^2

/-- Candidate uniform small-roundoff interpretation of the asymptotic clause.
Dimensions, input, distortion, entry bound and the two threshold constants
are fixed before quantifying over u, sketches or choices at SVD ties. -/
def MixedAsymptoticBound : Prop :=
  ∀ {m n s : ℕ} (r : ℕ) (H : Mat m n) (η K a b : ℝ), 0 < a → a ≤ b →
    ∃ C D u₀ : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ 0 < u₀ ∧
    ∀ {t : ℕ} (S : Mat s m) (Y : Mat s n) (V : Mat n t) (X : Mat m t)
      (G R : Mat t t) (Vr : Mat n r) (ε u : ℝ), u ≤ u₀ →
      (∀ i j, |S i j| ≤ K) →
      a * Real.sqrt u * Real.sqrt (frobSq H) ≤ ε →
      ε ≤ b * Real.sqrt u * Real.sqrt (frobSq H) →
      MixedRun H S Y V X G η ε u r → Output Y V G R Vr →
      frobSq (H - H * (Vr * Vrᵀ)) ≤
        (1 + C * Real.sqrt u) * tailEnergy H r + D * u

/-- An ordinary product in already stored precision (no two input conversions). -/
def StoredProduct {m k n : ℕ} (u : ℝ) (A : Mat m k) (B : Mat k n) (C : Mat m n) : Prop :=
  ∀ i j, |(C - A * B) i j| ≤ gamma k u * (magnitude A * magnitude B) i j

/-- Compact SVD of an input after its backward perturbation: the exactly
orthonormal representative convention adopted at the start of the appendix. -/
def CompactSVD {m n k : ℕ} (A : Mat m n) (U : Mat m k) (d : Fin k → ℝ)
    (V : Mat n k) : Prop :=
  Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ (∀ j, 0 < d j) ∧ Antitone d ∧ A = U * diagonal d * Vᵀ

/-- Compact factors and operations from a successful run. The constants K₁,K₂
bound the SVDs' normwise backward errors. The model allocates separate roundings
to each column division and to each multiplication in forming B. -/
def BackwardRun {m n s t k : ℕ} (H : Mat m n) (S : Mat s m) (Y : Mat s n)
    (E₁ : Mat s n) (V T : Mat n t) (X : Mat m t) (G R RSig : Mat t t)
    (B E₂ : Mat t n) (U : Mat t k) (d : Fin k → ℝ) (W : Mat n k)
    (u c K₁ K₂ : ℝ) : Prop :=
  let Y' := Y + E₁
  let ε := c * u * ‖Y‖
  let D := scales Y' t
  StoredProduct u S H Y ∧
    Real.sqrt (frobSq E₁) ≤ K₁ * u * Real.sqrt (frobSq Y) ∧
    t = (Finset.univ.filter (fun j : Fin n => ε < sigma Y' j.val)).card ∧
    LeadingRight Y' V ∧
    (∀ i j, ∃ δ : ℝ, |δ| ≤ u ∧ T i j = (V i j / sigma Y' j.val) * (1 + δ)) ∧
    StoredProduct u H T X ∧ StoredProduct u Xᵀ X G ∧ Gᵀ = G ∧
    (∀ i j, |(Rᵀ * R - G) i j| ≤ gamma (t + 1) u *
      (magnitude Rᵀ * magnitude R) i j) ∧
    (∀ i j, j < i → R i j = 0) ∧ (∀ i, 0 < R i i) ∧
    StoredProduct u R D RSig ∧ StoredProduct u RSig Vᵀ B ∧
    Real.sqrt (frobSq E₂) ≤ K₂ * u * Real.sqrt (frobSq B) ∧
    CompactSVD (B + E₂) U d W

/-- Candidate backward-error postcondition for all successful modeled runs.
The bound on the sketch norm is fixed before constants are chosen, and the
error constant may additionally depend on c. Separate successful-factorization
existence for the specified actual numerical routines remains open. -/
def BackwardStabilityBound : Prop :=
  ∀ (m n s : ℕ) (η K K₁ K₂ : ℝ), 0 ≤ η → η < 1 → 0 ≤ K → 0 ≤ K₁ → 0 ≤ K₂ →
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧ ∀ c : ℝ, c₀ ≤ c →
      ∃ C : ℝ, 0 < C ∧
      ∀ {t k : ℕ} (H : Mat m n) (S : Mat s m) (Y E₁ : Mat s n) (V T : Mat n t)
        (X : Mat m t) (G R RSig : Mat t t) (B E₂ : Mat t n) (U : Mat t k)
        (d : Fin k → ℝ) (W : Mat n k) (u : ℝ),
        H ≠ 0 → ‖S‖ ≤ K → EmbedsRange η S H → 0 < u → C₀ * u ≤ 1 →
        BackwardRun H S Y E₁ V T X G R RSig B E₂ U d W u c K₁ K₂ →
        ∃ (Uₕ : Mat m k) (Δ : Mat m n), Uₕᵀ * Uₕ = 1 ∧
          H + Δ = Uₕ * diagonal d * Wᵀ ∧
          Real.sqrt (frobSq Δ) ≤ C * u * Real.sqrt (frobSq H)

/-- Passing from componentwise domination to the spectral norm uses
coordinatewise absolute values of the test vector, preserving its Euclidean norm. -/
theorem entrywise_opNorm_bound {m n : ℕ} (E D : Mat m n) (a : ℝ)
    (ha : 0 ≤ a) (hb : ∀ i j, |E i j| ≤ a * D i j) : ‖E‖ ≤ a * ‖D‖ := by
  rw [Matrix.l2_opNorm_def E]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => |z j|)
  have hw : ‖w‖ = ‖z‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.real_norm_sq_eq, w]
  let v := Matrix.toEuclideanLin E z
  let y := Matrix.toEuclideanLin D w
  have he i : |v i| ≤ a * y i := by
    change |∑ j, E i j * z j| ≤ a * ∑ j, D i j * |z j|
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hb i j) (abs_nonneg _)
  have hsq : ‖v‖^2 ≤ (a * ‖y‖)^2 := by
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := he i
    have hh := sq_le_sq₀ (abs_nonneg (v i)) ((abs_nonneg _).trans h)
    simpa only [sq_abs, mul_pow] using hh.mpr h
  have hnorm := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))).mp hsq
  have hd := Matrix.l2_opNorm_mulVec D w
  change ‖y‖ ≤ ‖D‖ * ‖w‖ at hd
  rw [hw] at hd
  change ‖v‖ ≤ a * ‖D‖ * ‖z‖
  exact hnorm.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd ha)

/-- The explicit d_s, d_x and d_g spectral budgets follow from the componentwise model. -/
theorem rounded_product_opNorm {m k n : ℕ} (A : Mat m k) (B : Mat k n) (C : Mat m n)
    (u : ℝ) (hu : 0 ≤ u) (hk : ((k + 2 : ℕ) : ℝ) * u < 1)
    (h : RoundedProduct u A B C) : ‖C - A * B‖ ≤ productBudget u A B := by
  apply entrywise_opNorm_bound _ _ _ _ h
  unfold gamma
  exact div_nonneg (by positivity) (by linarith)

/-- Equations for the unrounded and rounded Gram stages. -/
theorem gram_error_identity {m t : ℕ} (X E : Mat m t) (F : Mat t t) :
    (X + E)ᵀ * (X + E) + F - Xᵀ * X =
    Xᵀ * E + Eᵀ * X + Eᵀ * E + F := by
  simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
  abel

theorem transpose_opNorm {m n : ℕ} (A : Mat m n) : ‖Aᵀ‖ = ‖A‖ := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.l2_opNorm_conjTranspose A

/-- Operator-norm perturbation in the retained coordinates. -/
theorem gram_error_norm {m t : ℕ} (X E : Mat m t) (F : Mat t t) :
    ‖(X + E)ᵀ * (X + E) + F - Xᵀ * X‖ ≤
      2 * ‖X‖ * ‖E‖ + ‖E‖^2 + ‖F‖ := by
  rw [gram_error_identity]
  calc
    _ ≤ ((‖Xᵀ * E‖ + ‖Eᵀ * X‖) + ‖Eᵀ * E‖) + ‖F‖ := by
      exact (norm_add_le _ _).trans (add_le_add_left
        ((norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)) _)
    _ ≤ ((‖X‖ * ‖E‖ + ‖E‖ * ‖X‖) + ‖E‖ * ‖E‖) + ‖F‖ := by
      simpa only [transpose_opNorm] using
        add_le_add_left (add_le_add (add_le_add (Matrix.l2_opNorm_mul Xᵀ E)
          (Matrix.l2_opNorm_mul Eᵀ X)) (Matrix.l2_opNorm_mul Eᵀ E)) ‖F‖
    _ = _ := by ring

/-- If SX is a perturbed isometry U - ET, the OSE transfers its two-sided
norm bounds back to X. All hypotheses are pointwise and z need not be unit. -/
theorem noisy_conditioning {s m t : ℕ} (S : Mat s m) (X : Mat m t)
    (U N : Mat s t) (η : ℝ) (hη : 0 ≤ η) (hη' : η < 1)
    (hSX : S * X = U - N) (hU : ∀ z, ‖Matrix.toEuclideanLin U z‖ = ‖z‖)
    (hN : ‖N‖ ≤ 1 / 2)
    (z : EuclideanSpace ℝ (Fin t))
    (he : Real.sqrt (1 - η) * ‖Matrix.toEuclideanLin X z‖ ≤
        ‖Matrix.toEuclideanLin (S * X) z‖ ∧
      ‖Matrix.toEuclideanLin (S * X) z‖ ≤
        Real.sqrt (1 + η) * ‖Matrix.toEuclideanLin X z‖) :
    ‖z‖ / (2 * Real.sqrt (1 + η)) ≤ ‖Matrix.toEuclideanLin X z‖ ∧
    ‖Matrix.toEuclideanLin X z‖ ≤ 3 * ‖z‖ / (2 * Real.sqrt (1 - η)) := by
  have hz : ‖Matrix.toEuclideanLin N z‖ ≤ ‖z‖ / 2 := by
    have h := Matrix.l2_opNorm_mulVec N z
    change ‖Matrix.toEuclideanLin N z‖ ≤ ‖N‖ * ‖z‖ at h
    nlinarith [mul_le_mul_of_nonneg_right hN (norm_nonneg z)]
  rw [hSX, map_sub, LinearMap.sub_apply] at he
  have hi := norm_sub_le (Matrix.toEuclideanLin U z) (Matrix.toEuclideanLin N z)
  have lo := norm_sub_norm_le (Matrix.toEuclideanLin U z) (Matrix.toEuclideanLin N z)
  rw [hU] at hi lo
  constructor
  · apply (div_le_iff₀ (by positivity)).mpr
    linarith [he.2]
  · apply (le_div_iff₀ (by positivity)).mpr
    linarith [he.1]

theorem retained_gt {s n t : ℕ} (Y : Mat s n) (ε : ℝ) (ht : t ≤ n)
    (hc : t = (Finset.univ.filter (fun j : Fin n => ε < sigma Y j.val)).card)
    (j : Fin t) : ε < sigma Y j.val := by
  by_contra! h
  let i : Fin n := ⟨j.val, lt_of_lt_of_le j.isLt ht⟩
  have hsub : Finset.univ.filter (fun k : Fin n => ε < sigma Y k.val) ⊆ Finset.Iio i := by
    intro k hk
    apply Finset.mem_Iio.mpr
    by_contra! hle
    exact (not_lt.mpr (le_trans ((Matrix.toEuclideanLin Y).singularValues_antitone hle) h))
      (Finset.mem_filter.mp hk).2
  have hcard := Finset.card_le_card hsub
  rw [← hc, Fin.card_Iio] at hcard
  exact (not_le_of_gt j.isLt) hcard

theorem norm_of_orthonormal_columns {m n : ℕ} (V : Mat m n) (hV : Vᵀ * V = 1)
    (z : EuclideanSpace ℝ (Fin n)) : ‖Matrix.toEuclideanLin V z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change ∑ i, ((V *ᵥ z.ofLp) i) ^ 2 = ∑ i, (z.ofLp i) ^ 2
  simpa only [dotProduct, ← sq] using
    (show (V *ᵥ z.ofLp) ⬝ᵥ (V *ᵥ z.ofLp) = z.ofLp ⬝ᵥ z.ofLp by
      calc
        _ = z.ofLp ⬝ᵥ ((Vᵀ * V) *ᵥ z.ofLp) := by
          symm
          rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
        _ = _ := by rw [hV, one_mulVec])

theorem norm_le_of_pointwise {m n : ℕ} (A : Mat m n) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ z, ‖Matrix.toEuclideanLin A z‖ ≤ c * ‖z‖) : ‖A‖ ≤ c := by
  rw [Matrix.l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ hc h

/-- Noisy conditioning derived directly from thresholded eigendirections,
componentwise sketch rounding and the embedding on the original data. -/
theorem conditioning_of_run {m n s r t : ℕ} {H : Mat m n} {S : Mat s m} {Y : Mat s n}
    {V : Mat n t} {X : Mat m t} {G : Mat t t} {η ε u : ℝ}
    (h : MixedRun H S Y V X G η ε u r) (z : EuclideanSpace ℝ (Fin t)) :
    let X₀ := H * (V * inverseScales Y t)
    ‖z‖ / (2 * Real.sqrt (1 + η)) ≤ ‖Matrix.toEuclideanLin X₀ z‖ ∧
      ‖Matrix.toEuclideanLin X₀ z‖ ≤ 3 * ‖z‖ / (2 * Real.sqrt (1 - η)) := by
  have hε := h.threshold_pos
  let D := inverseScales Y t
  let T := V * D
  let U := Y * T
  let N := (Y - S * H) * T
  have hs j := retained_gt Y ε h.retained_basis.1 h.retained_count j
  have hσ (j : Fin t) : sigma Y j.val ≠ 0 := (h.threshold_pos.trans (hs j)).ne'
  have hU : Uᵀ * U = 1 := by
    change (Y * (V * D))ᵀ * (Y * (V * D)) = 1
    rw [transpose_mul, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Yᵀ Y,
      ← Matrix.mul_assoc (Yᵀ * Y) V, h.retained_basis.2.2]
    change (diagonal _ )ᵀ * Vᵀ * (V * diagonal _ * diagonal _) = 1
    rw [diagonal_transpose, Matrix.mul_assoc, Matrix.mul_assoc V, ← Matrix.mul_assoc Vᵀ V,
      h.retained_basis.2.1, Matrix.one_mul, diagonal_mul_diagonal, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext j
    simp [sq, hσ j]
  have hVn : ‖V‖ ≤ 1 := norm_le_of_pointwise V 1 zero_le_one fun x => by
    simp [norm_of_orthonormal_columns V h.retained_basis.2.1]
  have hDn : ‖D‖ ≤ 1 / ε := by
    change ‖diagonal _‖ ≤ 1 / ε
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 1 / ε)).mpr
    intro j
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (h.threshold_pos.trans (hs j))), one_div]
    exact inv_anti₀ h.threshold_pos (hs j).le
  have hN : ‖N‖ ≤ 1 / 2 := by
    have hY := rounded_product_opNorm S H Y u h.roundoff_pos.le h.long_product h.sketch
    calc
      _ ≤ ‖Y - S * H‖ * ‖V * D‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ productBudget u S H * (‖V‖ * ‖D‖) :=
        mul_le_mul hY (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
          ((norm_nonneg _).trans hY)
      _ ≤ (ε / 2) * (1 * (1 / ε)) := mul_le_mul h.sketch_small
        (mul_le_mul hVn hDn (norm_nonneg _) zero_le_one) (by positivity) (by positivity)
      _ = 1 / 2 := by field_simp [h.threshold_pos.ne']
  apply noisy_conditioning S (H * T) U N η h.distortion_nonneg h.distortion_lt
    _ (norm_of_orthonormal_columns _ hU) hN z
  · have he := h.embedding (Matrix.toEuclideanLin T z)
    have composition {a b c : ℕ} (A : Mat a b) (B : Mat b c) (w : EuclideanSpace ℝ (Fin c)) :
        Matrix.toEuclideanLin A (Matrix.toEuclideanLin B w) = Matrix.toEuclideanLin (A * B) w := by
      apply WithLp.ofLp_injective
      exact mulVec_mulVec w.ofLp A B
    dsimp only at he
    rw [composition, composition] at he
    constructor
    · apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
      simpa [mul_pow, Real.sq_sqrt (sub_nonneg.mpr h.distortion_lt.le)] using he.1
    · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      simpa [mul_pow, Real.sq_sqrt (by linarith [h.distortion_nonneg] : 0 ≤ 1 + η)] using he.2
  · simp [U, N, Matrix.sub_mul, Matrix.mul_assoc]

/-- The retained Gram error is bounded directly from the actual three rounded
products, at precisely the absolute scale used to define θ. -/
theorem gram_budget_of_run {m n s r t : ℕ} {H : Mat m n} {S : Mat s m} {Y : Mat s n}
    {V : Mat n t} {X : Mat m t} {G : Mat t t} {η ε u : ℝ}
    (h : MixedRun H S Y V X G η ε u r) :
    let T := V * inverseScales Y t
    let X₀ := H * T
    let dx := productBudget u H T
    let dg := productBudget u Xᵀ X
    ‖G - X₀ᵀ * X₀‖ ≤ 3 * dx / Real.sqrt (1 - η) + dx^2 + dg := by
  let T := V * inverseScales Y t
  let X₀ := H * T
  let dx := productBudget u H T
  let dg := productBudget u Xᵀ X
  change ‖G - X₀ᵀ * X₀‖ ≤ 3 * dx / Real.sqrt (1 - η) + dx^2 + dg
  have hs : 0 < Real.sqrt (1 - η) := Real.sqrt_pos.mpr (sub_pos.mpr h.distortion_lt)
  have hX : ‖X₀‖ ≤ 3 / (2 * Real.sqrt (1 - η)) := by
    apply norm_le_of_pointwise _ _ (by positivity)
    intro z
    convert (conditioning_of_run h z).2 using 1
    ring
  have hx : ‖X - X₀‖ ≤ dx := rounded_product_opNorm H T X u h.roundoff_pos.le h.short_product h.precondition
  have hg : ‖G - Xᵀ * X‖ ≤ dg := rounded_product_opNorm Xᵀ X G u h.roundoff_pos.le h.long_product h.gram
  have hgram := gram_error_norm X₀ (X - X₀) (G - Xᵀ * X)
  rw [add_sub_cancel, add_sub_cancel] at hgram
  refine hgram.trans ?_
  have hdx : 0 ≤ dx := (norm_nonneg _).trans hx
  calc
    _ ≤ 2 * (3 / (2 * Real.sqrt (1 - η))) * dx + dx^2 + dg := by
      gcongr
    _ = _ := by ring

/-- The numerical threshold condition makes the computed symmetric Gram
positive definite. In particular, Cholesky can be performed in the exact
small-arithmetic model without assuming its success. -/
theorem gram_posDef_of_run {m n s r t : ℕ} {H : Mat m n} {S : Mat s m} {Y : Mat s n}
    {V : Mat n t} {X : Mat m t} {G : Mat t t} {η ε u : ℝ}
    (h : MixedRun H S Y V X G η ε u r) : G.PosDef := by
  let X₀ := H * (V * inverseScales Y t)
  let dx := productBudget u H (V * inverseScales Y t)
  let dg := productBudget u Xᵀ X
  let F := G - X₀ᵀ * X₀
  have hp : 0 < 1 + η := by linarith [h.distortion_nonneg]
  have hs : 0 < Real.sqrt (1 + η) := Real.sqrt_pos.mpr hp
  have hf : ‖F‖ < 1 / (4 * (1 + η)) := by
    apply lt_of_le_of_lt (gram_budget_of_run h)
    apply (lt_div_iff₀ (by positivity)).mpr
    simpa [theta, mul_comm] using h.gram_small
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using h.symmetric
  intro z hz
  let w : EuclideanSpace ℝ (Fin t) := WithLp.toLp 2 z
  have hw : 0 < ‖w‖ := norm_pos_iff.mpr (by
    intro h0
    exact hz (congrArg WithLp.ofLp h0))
  have hcond := (conditioning_of_run h w).1
  change ‖w‖ / (2 * Real.sqrt (1 + η)) ≤ ‖Matrix.toEuclideanLin X₀ w‖ at hcond
  have hlow : ‖w‖^2 / (4 * (1 + η)) ≤ ‖Matrix.toEuclideanLin X₀ w‖^2 := by
    have hc := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hcond
    norm_num [div_pow, mul_pow, Real.sq_sqrt hp.le] at hc
    exact hc
  have hFq : |z ⬝ᵥ (F *ᵥ z)| ≤ ‖F‖ * ‖w‖^2 := by
    have hinner := abs_real_inner_le_norm w (Matrix.toEuclideanCLM (n := Fin t) (𝕜 := ℝ) F w)
    rw [Matrix.inner_toEuclideanCLM] at hinner
    refine hinner.trans ?_
    have hFw := Matrix.l2_opNorm_mulVec F w
    change ‖Matrix.toEuclideanCLM (n := Fin t) (𝕜 := ℝ) F w‖ ≤ ‖F‖ * ‖w‖ at hFw
    simpa [sq, mul_left_comm] using mul_le_mul_of_nonneg_left hFw hw.le
  have hXq : z ⬝ᵥ ((X₀ᵀ * X₀) *ᵥ z) = ‖Matrix.toEuclideanLin X₀ w‖^2 := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, sq]
    rfl
  have hdecomp : z ⬝ᵥ (G *ᵥ z) = z ⬝ᵥ ((X₀ᵀ * X₀) *ᵥ z) + z ⬝ᵥ (F *ᵥ z) := by
    simp [F, Matrix.sub_mulVec, dotProduct_sub]
  have hsmall := mul_lt_mul_of_pos_right hf (sq_pos_of_pos hw)
  rw [hXq] at hdecomp
  simpa only [star_trivial] using (show 0 < z ⬝ᵥ (G *ᵥ z) by
    linarith [neg_le_of_abs_le hFq, (by ring : 1 / (4 * (1 + η)) * ‖w‖^2 = ‖w‖^2 / (4 * (1 + η)))])

/-- Appendix algebra, before taking norm bounds for the three separate errors. -/
theorem retained_backward_identity {m n t : ℕ} (X E Q : Mat m t) (R D : Mat t t)
    (V : Mat n t) (F : Mat t n) :
    (X - E) * D * Vᵀ - Q * (R * D * Vᵀ + F) =
    - (E * D * Vᵀ) + (X - Q * R) * D * Vᵀ - Q * F := by
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel

/-- Assemble a compact backward witness. The preceding analysis must still bound
the difference Q*B-H and the SVD's backward error. -/
theorem backward_witness {m n t k : ℕ} (H : Mat m n) (Q : Mat m t)
    (B E : Mat t n) (U : Mat t k) (D : Mat k k) (V : Mat n k)
    (hQ : Qᵀ * Q = 1) (hU : Uᵀ * U = 1) (hSVD : B + E = U * D * Vᵀ) :
    ∃ (W : Mat m k) (Δ : Mat m n), Wᵀ * W = 1 ∧
      H + Δ = W * D * Vᵀ ∧ Δ = (Q * B - H) + Q * E := by
  refine ⟨Q * U, Q * (B + E) - H, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ Q, hQ, Matrix.one_mul, hU]
  · rw [add_sub_cancel, hSVD]
    simp only [Matrix.mul_assoc]
  · rw [Matrix.mul_add]
    abel

end RPHOSVD.Mixed
