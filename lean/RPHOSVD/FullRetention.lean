import RPHOSVD.Projection

namespace RPHOSVD.Projection
open Matrix
noncomputable section

/-- Full retention in Theorem 3.1 refers only to *positive* singular values.
Consequently this case can occur with t strictly below n. -/
theorem nonzeroRetentionExact {m n s r t : ℕ} (a : Run m n s r t) (η : ℝ)
    (embed : EmbedsRange a.H a.S η)
    (retained : ∀ i : Fin n, 0 < sigma (a.S * a.H) i.val → a.ε < sigma (a.S * a.H) i.val) :
    frobSq (a.H - a.H * a.Pout) = tailEnergy a.H r := by
  have zeroTail : tailEnergy (a.S * a.H) t = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : t ≤ j.val
    · have hz : sigma (a.S*a.H) j.val = 0 := le_antisymm
        (le_of_not_gt (fun hp ↦ hj.not_gt ((a.threshold j).mpr (retained j hp))))
        (LinearMap.singularValues_nonneg _ _)
      simp [hj,hz]
    · simp [hj]
  have h₁ := (embeddingFrob a.H a.S η (1-a.P) embed).1
  rw [show frobSq (a.S*a.H*(1-a.P)) = tailEnergy (a.S*a.H) t from
    basisResidualTail _ _ _ a.sketchBasis_spec, zeroTail] at h₁
  have hn : frobSq (a.H * (1-a.P)) ≤ 0 :=
    nonpos_of_mul_nonpos_right h₁ (sub_pos.mpr embed.2.1)
  let L := a.H * (1-a.P)
  have hentry (i : Fin m) (j : Fin n) : L i j = 0 := by
    have hi : (L i j)^2 ≤ vecSq (L.col j) :=
      Finset.single_le_sum (f := fun k ↦ (L k j)^2) (fun k _ ↦ sq_nonneg _) (Finset.mem_univ i)
    have hj : vecSq (L.col j) ≤ frobSq L := by
      rw [frobSq_cols]
      exact Finset.single_le_sum (fun k _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
        (Finset.mem_univ j)
    have hh : (L i j)^2 ≤ 0 := hi.trans (hj.trans hn)
    nlinarith [sq_nonneg (L i j)]
  have hL : a.H * (1 - a.P) = 0 := Matrix.ext (fun i j ↦ hentry i j)
  have hHP : a.H * a.P = a.H := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hL
    exact hL.symm
  rw [exactProjectionIdentity, hL, hHP]
  simp [frobSq]

end
end RPHOSVD.Projection
