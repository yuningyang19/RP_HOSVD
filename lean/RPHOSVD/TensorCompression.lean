import RPHOSVD.TensorLoss

namespace RPHOSVD.Tensor
open Matrix
noncomputable section
variable {d : ℕ} {n r : Fin d → ℕ}

/-- The zero factors are ignored in parallel mode: before any compression
the long-side change of coordinates is just a permutation. -/
private theorem parallelRows (U : Factors n r) (j : Fin d) :
    offProduct U .parallel j * (offProduct U .parallel j).transpose = (1 : Matrix (shapeOff n j) (shapeOff n j) ℝ) := by
  ext x y; rw [Matrix.mul_apply]
  change (∑ c, offProduct U .parallel j x c * offProduct U .parallel j y c) = _
  rw [offGram]
  have hn (k : Fin d) : ¬compressBefore .parallel j k := by simp [compressBefore]
  simp_rw [if_neg (hn _)]
  by_cases h : x=y
  · subst y; simp
  · obtain ⟨k,hk⟩ := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ k); exact Matrix.one_apply_ne hk

private def indexedOff (U : Factors n r) (j : Fin d) (mode : Schedule) :
    Projection.Mat (Fintype.card (shapeOff n j)) (width n r mode j) :=
  (offProduct U mode j).reindex (Fintype.equivFin _) (Fintype.equivFin _)

theorem unfoldingCompression (a : ArrayR n) (U : Factors n r) (j : Fin d) (mode : Schedule)
    (hU : ∀ k, (U k).transpose * U k = 1) :
    ∃ F : Projection.Mat (width n r .parallel j) (width n r mode j),
      F.transpose * F = 1 ∧
      (unfolding a U mode j).transpose =
      F.transpose * (unfolding a (0 : Factors n r) .parallel j).transpose := by
  let L := indexedOff (0 : Factors n r) j .parallel
  let R := indexedOff U j mode
  let A : Projection.Mat (n j) (Fintype.card (shapeOff n j)) :=
    (rawOriginal a j).reindex (Equiv.refl _) (Fintype.equivFin _)
  have rel (W : Factors n r) (m : Schedule) :
      unfolding a W m j = A * indexedOff W j m := by
    ext i c
    let b := (Fintype.equivFin (Cols n r m j)).symm c
    have hi := unfolding_factor a W m j i b
    rw [show Fintype.equivFin _ b = c from (Fintype.equivFin _).apply_symm_apply c] at hi
    rw [hi]; simp only [A,indexedOff,Matrix.mul_apply,Matrix.reindex_apply, Matrix.submatrix_apply]
    exact Fintype.sum_equiv (Fintype.equivFin _) _ _ (by simp [b])
  have hL : L * L.transpose = (1 : Projection.Mat (Fintype.card (shapeOff n j)) (Fintype.card (shapeOff n j))) := by
    have hh := parallelRows (0 : Factors n r) j
    let E := (Fintype.equivFin (shapeOff n j)).symm
    let J := (Fintype.equivFin (Cols n r .parallel j)).symm
    let B := offProduct (0 : Factors n r) .parallel j
    change B.submatrix E J * B.transpose.submatrix J E = _
    rw [Matrix.submatrix_mul_equiv _ _ E J E, hh, Matrix.submatrix_one_equiv]
  have hR : R.transpose * R = (1 : Projection.Mat (width n r mode j) (width n r mode j)) := by
    have hh := offProduct_orthonormal U mode j hU
    let E := (Fintype.equivFin (shapeOff n j)).symm
    let J := (Fintype.equivFin (Cols n r mode j)).symm
    let B := offProduct U mode j
    change B.transpose.submatrix J E * B.submatrix E J = _
    rw [Matrix.submatrix_mul_equiv _ _ J E J, hh, Matrix.submatrix_one_equiv]
  refine ⟨L.transpose * R, ?_, ?_⟩
  · rw [transpose_mul,transpose_transpose,Matrix.mul_assoc, ← Matrix.mul_assoc L L.transpose,
      hL,Matrix.one_mul,hR]
  · rw [rel U mode,rel 0 .parallel,transpose_mul,transpose_mul,transpose_mul,transpose_transpose]
    change R.transpose * A.transpose = R.transpose * L * (L.transpose * A.transpose)
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc L L.transpose,hL,Matrix.one_mul]

end
end RPHOSVD.Tensor
