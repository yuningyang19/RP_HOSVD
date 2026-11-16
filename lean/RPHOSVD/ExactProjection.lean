import RPHOSVD.KyFan

/-! The Eckart–Young variational comparison and the complete ordinary RP error bound. -/
namespace RPHOSVD.Projection
open Matrix
noncomputable section
variable {m n r : ℕ}

private theorem frob_nonneg (A : Mat m n) : 0 ≤ frobSq A := by
  rw [frobSq_cols]
  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _

private theorem frob_zero (A : Mat m n) (hA : frobSq A = 0) : A = 0 := by
  rw [frobSq_cols] at hA
  have hc (j : Fin n) : vecSq (A.col j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp hA j
      (Finset.mem_univ j)
  ext i j
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp (hc j) i
    (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hz

private theorem rightProjectorProperties {k} (V : Mat n k) (hV : Vᵀ * V = 1) :
    (projector V)ᵀ = projector V ∧ projector V * projector V = projector V := by
  constructor <;> simp [projector, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V, hV]

private theorem energyPartition (A : Mat m n) (hr : r ≤ n) :
    frobSq A = tailEnergy A r + ∑ i : Fin r, sigma A i.val ^ 2 := by
  obtain ⟨W, hw⟩ := exists_rightBasis A
  rw [fullBasisEnergy hw]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  simp [tailEnergy, Fin.sum_univ_add, Fin.castAdd, add_comm, fun i : Fin r => i.isLt.not_ge]

private theorem projectedEnergy (A : Mat m n) (V : Mat n r) (hV : Vᵀ * V = 1) :
    frobSq (A * projector V) = frobSq (A * V) := by
  rw [projector, ← Matrix.mul_assoc, rightFrameEnergy _ _ hV]

/-- The squared SVD tail is bounded by the error of every matrix of rank at most r. -/
theorem tailEnergy_le_error (A B : Mat m n) (hr : r ≤ n) (hB : B.rank ≤ r) :
    tailEnergy A r ≤ frobSq (A - B) := by
  obtain ⟨W, hW⟩ := exists_rightBasis B
  let V := firstCols W hr
  let P := projector V
  have hV : Vᵀ * V = 1 := firstCols_orthonormal _ _ hW.1
  obtain ⟨hs, hi⟩ := rightProjectorProperties V hV
  have hB0 : B * (1 - P) = 0 := by
    apply frob_zero
    rw [show frobSq (B * (1 - P)) = tailEnergy B r from basisResidualTail _ _ _ hW]
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : r ≤ i.val
    · have eqRank : B.rank = Module.finrank ℝ (LinearMap.range B.toEuclideanLin) :=
        B.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      have hz := (B.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range).mpr
        (eqRank.symm.le.trans (hB.trans h))
      simp [h, sigma, hz]
    · simp [h]
  have hsA := frobSplit A P hs hi
  have hsAB := frobSplit (A - B) P hs hi
  have hsmall : frobSq (A * (1 - P)) ≤ frobSq (A - B) := by
    rw [Matrix.sub_mul, hB0, sub_zero] at hsAB
    linarith [frob_nonneg ((A - B) * P)]
  have hmax := frameEnergy_le_head A V hr hV
  have he := projectedEnergy A V hV
  change frobSq (A * P) = _ at he
  linarith [energyPartition A hr]

/-- Multiplication by an arbitrary orthogonal projector cannot increase any SVD tail. -/
theorem tailEnergy_projector_le {k} (A : Mat m n) (V : Mat n k) (hr : r ≤ n)
    (hV : Vᵀ * V = 1) : tailEnergy (A * projector V) r ≤ tailEnergy A r := by
  obtain ⟨W, hW⟩ := exists_rightBasis A
  let C := firstCols W hr
  let P := projector V
  let E := projector C
  have hrB : ((A * E) * P).rank ≤ r := by
    calc
      _ ≤ (A * E).rank := Matrix.rank_mul_le_left _ _
      _ ≤ E.rank := Matrix.rank_mul_le_right _ _
      _ ≤ C.rank := Matrix.rank_mul_le_left _ _
      _ ≤ r := by simpa using C.rank_le_card_width
  have h := tailEnergy_le_error (A * P) ((A * E) * P) hr hrB
  rw [← Matrix.sub_mul] at h
  have hh := basisResidualTail A W hr hW
  change frobSq (A * (1 - E)) = _ at hh
  rw [Matrix.mul_sub, Matrix.mul_one] at hh
  obtain ⟨hs, hi⟩ := rightProjectorProperties V hV
  have hspl := frobSplit (A - A * E) P hs hi
  exact h.trans (by linarith [frob_nonneg ((A - A * E) * (1 - P))])

/-- Proposition `thm:rp` in both clauses. -/
theorem projection : projectionClaim := by
  intro m n s r t a η h
  refine ⟨exactProjectionIdentity a, ?_⟩
  rw [exactProjectionIdentity]
  have htail := tailEnergy_projector_le a.H a.V (a.rank_le_retained.trans a.retained_le_n)
    a.V_orthonormal
  change tailEnergy (a.H * a.P) r ≤ _ at htail
  linarith [discardedEnergyBound a η h]

end
end RPHOSVD.Projection
