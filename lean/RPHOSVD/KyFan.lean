import RPHOSVD.Projection

/-! Ordered right singular bases and finite-dimensional variational estimates. -/
namespace RPHOSVD.Projection
open Matrix
noncomputable section

variable {m n r t : ℕ}

/-- An ordered full right singular basis exists for every real rectangular matrix,
including a rank-deficient matrix and a matrix with repeated singular values. -/
theorem exists_rightBasis (A : Mat m n) : ∃ W, RightBasis A W := by
  let T := A.toEuclideanLin
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn
  let W := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix b.toBasis
  have hw := (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_mem_unitary b
  change W ∈ unitary (Mat n n) at hw
  have hw' := (Unitary.mem_iff.mp hw)
  have hstar : star W = Wᵀ := Matrix.conjTranspose_eq_transpose_of_trivial W
  have hg : (Aᵀ * A).toEuclideanLin = T.adjoint ∘ₗ T := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial A, ← A.toEuclideanLin_conjTranspose_eq_adjoint]
    exact Matrix.toLpLin_mul 2 2 2 _ _
  refine ⟨W, ?_, ?_, ?_⟩
  · simpa only [← hstar] using hw'.1
  · simpa only [← hstar] using hw'.2
  · ext i j
    have he := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hn j
    rw [← T.sq_singularValues_fin hn j] at he
    change (T.adjoint ∘ₗ T) (b j) = (T.singularValues j ^ 2 : ℝ) • b j at he
    rw [← hg] at he
    have hc := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) he
    change ((Aᵀ * A) *ᵥ (fun k => W k j)) i = _ at hc
    rw [Matrix.mul_diagonal]
    change _ = W i j * T.singularValues j ^ 2
    change _ = T.singularValues j ^ 2 * W i j at hc
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm (T.singularValues j ^ 2)] using hc

/-- No row of a matrix with orthonormal columns has squared norm greater than one. -/
theorem frame_leverage_le_one (C : Mat n r) (hC : Cᵀ * C = 1) (i : Fin n) :
    (projector C) i i ≤ 1 := by
  let P := projector C
  have hs : Pᵀ = P := by simp [P, projector, transpose_mul]
  have hp : P * P = P := by simp [P, projector, Matrix.mul_assoc, ← Matrix.mul_assoc Cᵀ C, hC]
  have hu : ∑ j, P i j ^ 2 = P i i := by
    have hj (j : Fin n) : P j i = P i j := congrArg (fun M : Mat n n => M i j) hs
    simpa [Matrix.mul_apply, hj, pow_two] using congrArg (fun M : Mat n n => M i i) hp
  have h := Finset.single_le_sum (f := fun j => P i j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [hu] at h
  change P i i ≤ 1
  nlinarith

/-- A decreasing nonnegative spectrum paired with weights in [0,1] of total mass
r is bounded by the sum of its first r entries. -/
theorem weightedSum_le_head (a : ℕ → ℝ) (w : Fin n → ℝ) (hr : r ≤ n)
    (ha : Antitone a) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (hs : ∑ i, w i = r) :
    ∑ i, a i.val * w i ≤ ∑ i : Fin r, a i.val := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  let p := a r
  have h₁ (i : Fin r) : a i.val * w (Fin.castAdd d i) ≤
      a i.val + p * (w (Fin.castAdd d i) - 1) := by
    have h := mul_nonneg (sub_nonneg.mpr (ha i.isLt.le))
      (sub_nonneg.mpr (hw (Fin.castAdd d i)).2)
    dsimp [p]
    nlinarith only [h]
  have h₂ (i : Fin d) : a (r + i.val) * w (Fin.natAdd r i) ≤ p * w (Fin.natAdd r i) :=
    mul_le_mul_of_nonneg_right (ha (Nat.le_add_right r i.val)) (hw _).1
  have e₁ := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h₁ i)
  have e₂ := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h₂ i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at e₁ e₂
  rw [Fin.sum_univ_add] at hs ⊢
  simp only [Fin.val_castAdd, Fin.val_natAdd] at *
  nlinarith only [e₁, e₂, congrArg (fun x : ℝ => p * x) hs]

/-- Finite-dimensional Ky Fan inequality for a real rectangular matrix and an
arbitrary orthonormal r-frame, including repeated singular values. -/
theorem frameEnergy_le_head (A : Mat m n) (C : Mat n r) (hr : r ≤ n)
    (hC : Cᵀ * C = 1) :
    frobSq (A * C) ≤ ∑ i : Fin r, sigma A i.val ^ 2 := by
  obtain ⟨W, hW⟩ := exists_rightBasis A
  let Z := Wᵀ * C
  have hZ : Zᵀ * Z = 1 := by
    simp [Z, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc W Wᵀ, hW.2.1, hC]
  let w := fun i => (projector Z) i i
  have hw (i : Fin n) : 0 ≤ w i ∧ w i ≤ 1 := by
    refine ⟨?_, frame_leverage_le_one _ hZ i⟩
    simpa only [w, projector, Matrix.mul_apply, transpose_apply] using
      (Finset.sum_nonneg (s := Finset.univ) (fun j _ => mul_self_nonneg (Z i j)))
  have hmass : ∑ i, w i = r := by
    change (Z * Zᵀ).trace = r
    rw [trace_mul_comm, hZ, trace_one]
    simp
  have hCeq : C = W * Z := by simp [Z, ← Matrix.mul_assoc, hW.2.1]
  have hg : Wᵀ * (Aᵀ * A) * W = diagonal (fun i : Fin n => sigma A i.val ^ 2) := by
    rw [Matrix.mul_assoc, hW.2.2, ← Matrix.mul_assoc, hW.1, one_mul]
  have henergy : frobSq (A * C) = ∑ i : Fin n, sigma A i.val ^ 2 * w i := by
    rw [hCeq, frobSq, transpose_mul, transpose_mul]
    calc
      _ = (Zᵀ * (Wᵀ * (Aᵀ * A) * W) * Z).trace := by simp [Matrix.mul_assoc]
      _ = (diagonal (fun i : Fin n => sigma A i.val ^ 2) * (Z * Zᵀ)).trace := by
        rw [hg, trace_mul_cycle, ← Matrix.mul_assoc]
        simpa only [Matrix.mul_assoc] using trace_mul_comm (Z * Zᵀ) (diagonal (fun i : Fin n => sigma A i.val ^ 2))
      _ = _ := by simp [Matrix.trace, Matrix.diagonal_mul, w, projector]
  rw [henergy]
  apply weightedSum_le_head (fun i => sigma A i ^ 2) w hr _ hw hmass
  intro i j hij
  exact pow_le_pow_left₀ (A.toEuclideanLin.singularValues_nonneg j)
    (A.toEuclideanLin.singularValues_antitone hij) 2

end
end RPHOSVD.Projection
