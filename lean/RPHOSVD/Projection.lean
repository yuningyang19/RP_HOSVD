import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! Matrix statements for the exact-arithmetic RP kernel. `tailEnergy` denotes the sum of
squared singular values, i.e. the convention used by the projection proofs. The `...Claim`
declarations specify the three public statements proved in ExactProjection, Refined and Retained. -/
namespace RPHOSVD.Projection

open Matrix
noncomputable section

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

def frobSq {m n} (A : Mat m n) : ℝ := (Aᵀ * A).trace

def sigma {m n} (A : Mat m n) (i : ℕ) : ℝ := A.toEuclideanLin.singularValues i

/-- `r` is the number retained, so zero-based index `r` is the first discarded index. -/
def tailEnergy {m n} (A : Mat m n) (r : ℕ) : ℝ :=
  ∑ j : Fin n, if r ≤ j.val then sigma A j.val ^ 2 else 0

def opNorm {m n} (A : Mat m n) : ℝ := ‖A.toEuclideanLin.toContinuousLinearMap‖

def vecSq {m} (x : Fin m → ℝ) : ℝ := ∑ j, x j ^ 2

def EmbedsRange {m n s} (H : Mat m n) (S : Mat s m) (η : ℝ) : Prop :=
  0 < η ∧ η < 1 ∧ ∀ z : Fin n → ℝ,
    (1 - η) * vecSq (H *ᵥ z) ≤ vecSq (S *ᵥ (H *ᵥ z)) ∧
    vecSq (S *ᵥ (H *ᵥ z)) ≤ (1 + η) * vecSq (H *ᵥ z)

/-- An ordered full right singular basis, allowing ties, rectangularity and a kernel. -/
def RightBasis {m n} (A : Mat m n) (W : Mat n n) : Prop :=
  Wᵀ * W = 1 ∧ W * Wᵀ = 1 ∧
  Aᵀ * A * W = W * diagonal (fun i : Fin n => sigma A i.val ^ 2)

def firstCols {n k} (W : Mat n n) (hk : k ≤ n) : Mat n k :=
  W.submatrix id (Fin.castLE hk)

def projector {n k} (V : Mat n k) : Mat n n := V * Vᵀ

def retainedDiag {s n t} (Y : Mat s n) : Mat t t := diagonal fun i => sigma Y i.val

def invRetainedDiag {s n t} (Y : Mat s n) : Mat t t := diagonal fun i => (sigma Y i.val)⁻¹

/-- A run of lines 1–5, described by SVD/Cholesky witnesses. The global threshold
assumption in §3 gives `r ≤ t`. The discarded threshold includes equality. -/
structure Run (m n s r t : ℕ) where
  H : Mat m n
  S : Mat s m
  ε : ℝ
  ε_nonneg : 0 ≤ ε
  rank_pos : 1 ≤ r
  rank_le_retained : r ≤ t
  retained_le_n : t ≤ n
  sketchBasis : Mat n n
  sketchBasis_spec : RightBasis (S * H) sketchBasis
  threshold : ∀ i : Fin n, i.val < t ↔ ε < sigma (S * H) i.val
  R : Mat t t
  chol_gram : let V := firstCols sketchBasis retained_le_n
              let X := H * V * (invRetainedDiag (t := t) (S * H))
              Rᵀ * R = Xᵀ * X
  outputBasis : Mat n n
  outputBasis_spec : let V := firstCols sketchBasis retained_le_n
                     let B := R * (retainedDiag (t := t) (S * H)) * Vᵀ
                     RightBasis B outputBasis

variable {m n s r t : ℕ}

def Run.V (a : Run m n s r t) := firstCols a.sketchBasis a.retained_le_n
def Run.B (a : Run m n s r t) := a.R * (retainedDiag (t := t) (a.S * a.H)) * a.Vᵀ
def Run.P (a : Run m n s r t) := projector a.V
def Run.U (a : Run m n s r t) := firstCols a.outputBasis (a.rank_le_retained.trans a.retained_le_n)
def Run.Pout (a : Run m n s r t) := projector a.U

/-- Proposition `thm:rp`. The second residual in its exact identity is expressed by
its SVD tail energy, including the case of repeated singular values. -/
def projectionClaim : Prop := ∀ {m n s r t} (a : Run m n s r t) (η : ℝ),
  EmbedsRange a.H a.S η →
    frobSq (a.H - a.H * a.Pout) =
      frobSq (a.H * (1 - a.P)) + tailEnergy (a.H * a.P) r ∧
    frobSq (a.H - a.H * a.Pout) ≤
      tailEnergy a.H r + ((n - t : ℕ) : ℝ) / (1 - η) * a.ε ^ 2

/-- Theorem `thm:rp-refined`, including the all-directions-retained clause. -/
def refinedProjectionClaim : Prop := ∀ {m n s r t} (a : Run m n s r t) (η : ℝ),
  EmbedsRange a.H a.S η → a.ε ^ 2 ≤ (1 - η) / 2 * sigma a.B (r - 1) ^ 2 →
    frobSq (a.H - a.H * a.Pout) ≤ tailEnergy a.H r + 2 * r * η^2 / (1 - η) * a.ε^2 ∧
    (a.ε < sigma (a.S * a.H) (n - 1) → frobSq (a.H - a.H * a.Pout) ≤ tailEnergy a.H r)

/-- Lemma `lem:retained-subspace-error`. Both the output SVD and the choice of
orthonormal bases are quantified, accommodating multiplicity at the cutoff. -/
def retainedSubspaceClaim : Prop := ∀ {m n r t : ℕ} (H : Mat m n) (V : Mat n t)
    (D : Mat n (n - t)) (Q : Mat m t) (U : Mat t t) (hr : r ≤ t),
  1 ≤ r → t ≤ n → Vᵀ * V = 1 → Dᵀ * D = 1 → Vᵀ * D = 0 →
  projector V + projector D = 1 → Function.Injective (H * V).mulVecLin →
  Qᵀ * Q = 1 → LinearMap.range Q.mulVecLin = LinearMap.range (H * V).mulVecLin →
  RightBasis (H * V) U → opNorm (H * D) ^ 2 ≤ sigma (H * V) (r - 1) ^ 2 / 2 →
  frobSq (H - (H * V) * projector (firstCols U hr) * Vᵀ) ≤
    tailEnergy H r + 2 * r * opNorm (Qᵀ * H * D) ^ 2

/-- Gram recovery for every witness run, including rank deficient input. -/
theorem gramRecovery (a : Run m n s r t) : a.Bᵀ * a.B = (a.H * a.P)ᵀ * (a.H * a.P) := by
  let Y := a.S * a.H
  let D := retainedDiag (t := t) Y
  let J := invRetainedDiag (t := t) Y
  have hpos (i : Fin t) : 0 < sigma Y i.val :=
    lt_of_le_of_lt a.ε_nonneg ((a.threshold (Fin.castLE a.retained_le_n i)).mp i.isLt)
  have hJD : J * D = 1 := by
    simp [J, D, invRetainedDiag, retainedDiag, diagonal_mul_diagonal, (hpos _).ne']
  let X := a.H * a.V * J
  let C := D * a.Vᵀ
  have h₁ : a.B = a.R * C := by simp [Run.B, C, D, Y, Matrix.mul_assoc]
  have h₂ : X * C = a.H * a.P := by
    simp [X, C, Run.P, projector, Matrix.mul_assoc, ← Matrix.mul_assoc J D, hJD]
  calc
    a.Bᵀ * a.B = Cᵀ * (a.Rᵀ * a.R) * C := by rw [h₁, transpose_mul]; simp [Matrix.mul_assoc]
    _ = Cᵀ * (Xᵀ * X) * C := by rw [a.chol_gram]; rfl
    _ = (X * C)ᵀ * (X * C) := by rw [transpose_mul X C]; simp [Matrix.mul_assoc]
    _ = (a.H * a.P)ᵀ * (a.H * a.P) := by rw [h₂]

/-- Pythagoras for right multiplication by complementary orthogonal projectors. -/
theorem frobSplit (H : Mat m n) (P : Mat n n) (hs : Pᵀ = P) (hp : P * P = P) :
    frobSq H = frobSq (H * (1 - P)) + frobSq (H * P) := by
  have comp : (1 - P) * (1 - P) = 1 - P := by
    simp [Matrix.mul_sub, Matrix.sub_mul, hp]
  have tr (E : Mat n n) (he : Eᵀ = E) (hi : E * E = E) :
      frobSq (H * E) = (E * (Hᵀ * H)).trace := by
    rw [frobSq, transpose_mul, he, ← Matrix.mul_assoc, Matrix.mul_assoc E Hᵀ H,
      trace_mul_cycle, ← Matrix.mul_assoc, hi, Matrix.mul_assoc]
  rw [tr _ (by simp [hs]) comp, tr _ hs hp, Matrix.sub_mul, one_mul, trace_sub, frobSq]
  ring

/-- Algebraic orthogonal split used in the exact-error formula. This bridge takes
nested symmetric projectors; the identification of the chosen bases is separate. -/
theorem nestedProjectionSplit (H : Mat m n) (P E : Mat n n)
    (hs : Pᵀ = P) (hp : P * P = P) (hE : E * P = E) :
    frobSq (H - H * E) = frobSq (H * (1 - P)) + frobSq (H * P - H * E) := by
  have h := frobSplit (H - H * E) P hs hp
  simpa [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hE] using h

/-- Taking leading columns of an orthogonal matrix preserves column orthonormality. -/
theorem firstCols_orthonormal {k} (W : Mat n n) (hk : k ≤ n) (hW : Wᵀ * W = 1) :
    (firstCols W hk)ᵀ * firstCols W hk = 1 := by
  let f := Fin.castLE hk
  change Wᵀ.submatrix f id * W.submatrix id f = 1
  rw [← Matrix.submatrix_mul Wᵀ W f id f Function.bijective_id, hW]
  apply Matrix.submatrix_one
  exact Fin.castLE_injective hk

theorem Run.V_orthonormal (a : Run m n s r t) : a.Vᵀ * a.V = 1 :=
  firstCols_orthonormal _ _ a.sketchBasis_spec.1

theorem Run.U_orthonormal (a : Run m n s r t) : a.Uᵀ * a.U = 1 :=
  firstCols_orthonormal _ _ a.outputBasis_spec.1

/-- The Frobenius energy equals the sum of the column energies. -/
theorem frobSq_cols (A : Mat m n) : frobSq A = ∑ j, vecSq (A.col j) := by
  simp [frobSq, Matrix.trace, Matrix.mul_apply, vecSq, pow_two, Matrix.col]

/-- The sketch embedding inequalities can be summed for arbitrary collections of columns. -/
theorem embeddingFrob {k} (H : Mat m n) (S : Mat s m) (η : ℝ) (Z : Mat n k)
    (h : EmbedsRange H S η) :
    (1 - η) * frobSq (H * Z) ≤ frobSq (S * H * Z) ∧
    frobSq (S * H * Z) ≤ (1 + η) * frobSq (H * Z) := by
  have hcol {d e f} (A : Mat d e) (B : Mat e f) (j : Fin f) :
      (A * B).col j = A *ᵥ B.col j := by rfl
  simp only [Matrix.mul_assoc, frobSq_cols, hcol, Finset.mul_sum]
  exact ⟨Finset.sum_le_sum (fun i _ => (h.2.2 (Z.col i)).1),
    Finset.sum_le_sum (fun i _ => (h.2.2 (Z.col i)).2)⟩

/-- The sketch singular-vector condition gives the energy in each column exactly. -/
theorem basisColumnEnergy {d} {A : Mat d n} {W : Mat n n} (hW : RightBasis A W) (i : Fin n) :
    vecSq ((A * W).col i) = sigma A i.val ^ 2 := by
  have gram : (A * W)ᵀ * (A * W) = diagonal (fun j : Fin n => sigma A j.val ^ 2) := by
    rw [Matrix.transpose_mul A W, ← Matrix.mul_assoc, Matrix.mul_assoc Wᵀ Aᵀ A,
      Matrix.mul_assoc, hW.2.2, ← Matrix.mul_assoc, hW.1, one_mul]
  have hii := congrArg (fun T : Mat n n => T i i) gram
  change (∑ j, (A * W) j i * (A * W) j i) = _ at hii
  simpa [vecSq, Matrix.col, pow_two] using hii

/-- A square full right basis preserves all Frobenius energy. -/
theorem fullBasisEnergy {d} {A : Mat d n} {W : Mat n n} (hW : RightBasis A W) :
    frobSq A = ∑ i : Fin n, sigma A i.val ^ 2 := by
  have equal : frobSq (A * W) = frobSq A := by
    rw [frobSq, Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc Wᵀ Aᵀ A,
      trace_mul_cycle, ← Matrix.mul_assoc, hW.2.1]
    simp [frobSq]
  rw [← equal, frobSq_cols]
  exact Finset.sum_congr rfl fun i _ => basisColumnEnergy hW i

/-- Frobenius energy is unchanged by multiplication on the right by a coisometry. -/
theorem rightFrameEnergy {k} (A : Mat m k) (V : Mat n k) (hV : Vᵀ * V = 1) :
    frobSq (A * Vᵀ) = frobSq A := by
  rw [frobSq, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mul_assoc, Matrix.mul_assoc V Aᵀ A, trace_mul_cycle,
    ← Matrix.mul_assoc, hV]
  simp [frobSq]

/-- Exact tail identity for a specified ordered right singular basis. -/
theorem basisResidualTail {k} (A : Mat m n) (W : Mat n n) (hk : k ≤ n) (hW : RightBasis A W) :
    frobSq (A * (1 - projector (firstCols W hk))) = tailEnergy A k := by
  let V := firstCols W hk
  have hV : Vᵀ * V = 1 := firstCols_orthonormal _ _ hW.1
  have hs : (projector V)ᵀ = projector V := by simp [projector, transpose_mul]
  have hi : projector V * projector V = projector V := by
    simp [projector, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V, hV]
  have hsplit := frobSplit A (projector V) hs hi
  have he : frobSq (A * projector V) = ∑ i : Fin k, sigma A i.val ^ 2 := by
    rw [projector, ← Matrix.mul_assoc, rightFrameEnergy _ _ hV, frobSq_cols]
    exact Finset.sum_congr rfl (fun i _ => basisColumnEnergy hW (Fin.castLE hk i))
  have partition : (∑ i : Fin n, sigma A i.val ^ 2) =
      tailEnergy A k + ∑ i : Fin k, sigma A i.val ^ 2 := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    simp [tailEnergy, Fin.sum_univ_add, Fin.castAdd, add_comm, fun i : Fin k => i.isLt.not_ge]
  rw [he, fullBasisEnergy hW, partition] at hsplit
  linarith only [hsplit]

/-- Number of discarded sketch values times the squared threshold. -/
theorem Run.sketchTailBound (a : Run m n s r t) :
    tailEnergy (a.S * a.H) t ≤ ((n - t : ℕ) : ℝ) * a.ε^2 := by
  let Y := a.S * a.H
  have discarded (i : Fin n) (hi : t ≤ i.val) : sigma Y i.val ^ 2 ≤ a.ε^2 := by
    have h := le_of_not_gt (fun hg => hi.not_gt ((a.threshold i).mpr hg))
    have hn : 0 ≤ sigma Y i.val := Y.toEuclideanLin.singularValues_nonneg _
    nlinarith [a.ε_nonneg]
  have hcount : (∑ i : Fin n, if t ≤ i.val then a.ε ^ 2 else 0) =
      ((n - t : ℕ) : ℝ) * a.ε^2 := by
    obtain ⟨d, e⟩ := Nat.exists_eq_add_of_le a.retained_le_n
    subst n
    simp [Fin.sum_univ_add, Fin.castAdd, fun i : Fin t => i.isLt.not_ge]
  rw [← hcount]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : t ≤ i.val
  · simpa only [if_pos hi] using discarded i hi
  · simp [hi]

/-- Original-data discarded Frobenius energy, derived from the sketch threshold
and the embedding. This is the complete discarded term in `thm:rp`. -/
theorem discardedEnergyBound (a : Run m n s r t) (η : ℝ) (h : EmbedsRange a.H a.S η) :
    frobSq (a.H * (1 - a.P)) ≤ ((n - t : ℕ) : ℝ) / (1 - η) * a.ε ^ 2 := by
  have hs := (embeddingFrob a.H a.S η (1 - a.P) h).1
  rw [show frobSq (a.S * a.H * (1 - a.P)) = tailEnergy (a.S * a.H) t from
    basisResidualTail _ _ _ a.sketchBasis_spec] at hs
  have he := hs.trans a.sketchTailBound
  have hpos : 0 < 1 - η := sub_pos.mpr h.2.1
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hpos).2 (by rwa [mul_comm] at he)

/-- Equal column Gram matrices give equal ordered singular values, including trailing zeros. -/
theorem sigma_eq_of_gram_eq {d} (A : Mat m n) (B : Mat d n)
    (h : Aᵀ * A = Bᵀ * B) (i : ℕ) : sigma A i = sigma B i := by
  have eqGram (k : ℕ) (T : Mat k n) :
      (Tᵀ * T).toEuclideanLin = T.toEuclideanLin.adjoint ∘ₗ T.toEuclideanLin := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial T, ← T.toEuclideanLin_conjTranspose_eq_adjoint]
    exact Matrix.toLpLin_mul 2 2 2 _ _
  have hE := congrArg Matrix.toEuclideanLin h
  rw [eqGram, eqGram] at hE
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  by_cases hi : i < n
  · simp only [sigma, LinearMap.singularValues_of_lt _ hn hi]
    have he := (A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvalues_eq_eigenvalues_iff hn
      B.toEuclideanLin.isSymmetric_adjoint_comp_self hn).mpr (congrArg LinearMap.charpoly hE)
    rw [he]
  · simp [sigma, LinearMap.singularValues_of_finrank_le _ (hn.trans_le (le_of_not_gt hi))]

/-- The computed right basis is also a right singular basis for the retained original matrix. -/
theorem Run.retainedRightBasis (a : Run m n s r t) : RightBasis (a.H * a.P) a.outputBasis := by
  obtain ⟨hl, hr, he⟩ := a.outputBasis_spec
  refine ⟨hl, hr, ?_⟩
  change a.Bᵀ * a.B * a.outputBasis = a.outputBasis * diagonal (fun i : Fin n => sigma a.B i.val ^ 2) at he
  rw [gramRecovery a] at he
  simpa only [← sigma_eq_of_gram_eq _ _ (gramRecovery a)] using he

/-- With all sketch directions retained, the RP residual is exactly the original SVD tail. -/
theorem fullRetentionExact (a : Run m n s r t) (hall : t = n) :
    frobSq (a.H - a.H * a.Pout) = tailEnergy a.H r := by
  subst t
  have hI : a.P = 1 := by simpa [Run.P, Run.V, projector, firstCols] using a.sketchBasis_spec.2.1
  have hb := a.retainedRightBasis
  simp only [hI, Matrix.mul_one] at hb
  simpa [Run.Pout, Run.U, Matrix.mul_sub] using
    (basisResidualTail a.H a.outputBasis (a.rank_le_retained.trans a.retained_le_n) hb)

/-- The manuscript's strict minimum-sketch-singular-value condition implies full retention. -/
theorem Run.full_of_min (a : Run m n s r t)
    (h : a.ε < sigma (a.S * a.H) (n - 1)) : t = n := by
  have hn : 0 < n := lt_of_lt_of_le (lt_of_lt_of_le (by omega : 0 < 1) a.rank_pos)
    (a.rank_le_retained.trans a.retained_le_n)
  have hk : n - 1 < n := by omega
  have hi := (a.threshold ⟨n - 1, hk⟩).mpr h
  change n - 1 < t at hi
  have ht := a.retained_le_n
  omega

/-- Gram of the selected sketch columns in right singular coordinates. -/
theorem firstGram {d k} (A : Mat d n) (W : Mat n n) (hk : k ≤ n) (hW : RightBasis A W) :
    (A * firstCols W hk)ᵀ * (A * firstCols W hk) =
    diagonal (fun i : Fin k => sigma A i.val ^ 2) := by
  let f := Fin.castLE hk
  have hg : (A * W)ᵀ * (A * W) = diagonal (fun i : Fin n => sigma A i.val ^ 2) := by
    rw [Matrix.transpose_mul A W, ← Matrix.mul_assoc, Matrix.mul_assoc Wᵀ Aᵀ A,
      Matrix.mul_assoc, hW.2.2, ← Matrix.mul_assoc, hW.1, one_mul]
  change (A * W).transpose.submatrix f id * (A * W).submatrix id f = _
  rw [← Matrix.submatrix_mul (A * W)ᵀ (A * W) f id f Function.bijective_id, hg]
  exact Matrix.submatrix_diagonal _ f (Fin.castLE_injective hk)

/-- Positive sketch directions ensure the recovered factor has at least the retained rank. -/
theorem Run.rank_B (a : Run m n s r t) : a.B.rank = t := by
  let Y := a.S * a.H
  have hpos (i : Fin t) : 0 < sigma Y i.val :=
    lt_of_le_of_lt a.ε_nonneg ((a.threshold (Fin.castLE a.retained_le_n i)).mp i.isLt)
  have hy : (Y * a.V).rank = t := by
    have hg : (Y * a.V)ᵀ * (Y * a.V) = diagonal (fun i : Fin t => sigma Y i.val ^ 2) :=
      firstGram _ _ a.retained_le_n a.sketchBasis_spec
    rw [← Matrix.rank_transpose_mul_self, hg, Matrix.rank_diagonal]
    simp [fun i : Fin t => (hpos i).ne']
  have hPV : a.P * a.V = a.V := by simp [Run.P, projector, Matrix.mul_assoc, a.V_orthonormal]
  have hY : Y * a.V = a.S * ((a.H * a.P) * a.V) := by simp [Y, Matrix.mul_assoc, hPV]
  have hr : a.B.rank = (a.H * a.P).rank := by
    rw [← Matrix.rank_transpose_mul_self a.B, gramRecovery, Matrix.rank_transpose_mul_self]
  apply le_antisymm a.B.rank_le_height
  calc
    t = (Y * a.V).rank := hy.symm
    _ ≤ (a.H * a.P * a.V).rank := hY ▸ Matrix.rank_mul_le_right _ _
    _ ≤ (a.H * a.P).rank := Matrix.rank_mul_le_left _ _
    _ = a.B.rank := hr.symm

/-- Every selected output direction has strictly positive singular value. -/
theorem Run.selectedPositive (a : Run m n s r t) (i : Fin r) : 0 < sigma a.B i.val := by
  have hr : a.B.rank = Module.finrank ℝ (LinearMap.range a.B.toEuclideanLin) :=
    a.B.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin t) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  exact (a.B.toEuclideanLin.singularValues_pos_iff_lt_finrank_range).mpr
    (by rw [← hr, a.rank_B]; exact lt_of_lt_of_le i.isLt a.rank_le_retained)

/-- The retained projector fixes each selected output singular vector. -/
theorem Run.outputNested (a : Run m n s r t) : a.Pout * a.P = a.Pout := by
  have hV := a.V_orthonormal
  have hP : a.Pᵀ = a.P := by simp [Run.P, projector, transpose_mul]
  have hBP : a.B * a.P = a.B := by
    simp [Run.B, Run.P, projector, Matrix.mul_assoc, ← Matrix.mul_assoc a.Vᵀ a.V, hV]
  have hPB : a.P * a.Bᵀ = a.Bᵀ := by
    simpa [Matrix.transpose_mul, hP] using congrArg Matrix.transpose hBP
  let G := a.Bᵀ * a.B
  let W := a.outputBasis
  let D := diagonal (fun i : Fin n => sigma a.B i.val ^ 2)
  have hGW : G * W = W * D := a.outputBasis_spec.2.2
  have hPW : a.P * W * D = W * D := by
    rw [Matrix.mul_assoc, ← hGW, ← Matrix.mul_assoc, show a.P * G = G by
      simp [G, ← Matrix.mul_assoc, hPB]]
  have hPU : a.P * a.U = a.U := by
    ext j i
    let v := Fin.castLE (a.rank_le_retained.trans a.retained_le_n) i
    have h := congrArg (fun T : Mat n n => T j v) hPW
    simp only [D, Matrix.mul_diagonal] at h
    exact mul_right_cancel₀ (pow_ne_zero 2 (a.selectedPositive i).ne') h
  have hUP : a.Uᵀ * a.P = a.Uᵀ := by
    simpa [Matrix.transpose_mul, hP] using congrArg Matrix.transpose hPU
  simp [Run.Pout, projector, Matrix.mul_assoc, hUP]

/-- Complete first (exact-identity) clause of Proposition `thm:rp`. -/
theorem exactProjectionIdentity (a : Run m n s r t) :
    frobSq (a.H - a.H * a.Pout) = frobSq (a.H * (1 - a.P)) + tailEnergy (a.H * a.P) r := by
  have hs : a.Pᵀ = a.P := by simp [Run.P, projector, transpose_mul]
  have hi : a.P * a.P = a.P := by
    simp [Run.P, projector, Matrix.mul_assoc, ← Matrix.mul_assoc a.Vᵀ a.V, a.V_orthonormal]
  have hPE : a.P * a.Pout = a.Pout := by
    have hE : a.Poutᵀ = a.Pout := by simp [Run.Pout, projector, transpose_mul]
    simpa [transpose_mul, hs, hE] using congrArg Matrix.transpose a.outputNested
  rw [nestedProjectionSplit _ _ _ hs hi a.outputNested]
  congr 1
  have h := basisResidualTail (a.H * a.P) a.outputBasis (a.rank_le_retained.trans a.retained_le_n)
    a.retainedRightBasis
  change frobSq ((a.H * a.P) * (1 - a.Pout)) = _ at h
  simpa only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hPE] using h

end
end RPHOSVD.Projection
