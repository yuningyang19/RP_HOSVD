import RPHOSVD.BackwardTail

namespace RPHOSVD.Mixed
open Matrix
noncomputable section

theorem frob_left_frame {m t n : ℕ} (Q : Mat m t) (A : Mat t n) (hQ : Qᵀ*Q = 1) :
    frob (Q*A) = frob A := by
  have bridge {b a : ℕ} (Z : Mat b a) : frobSq Z = Projection.frobSq Z := by
    rw [frobSq,Projection.frobSq_cols,Finset.sum_comm]; rfl
  simp only [frob,bridge,Projection.frobSq,transpose_mul,Matrix.mul_assoc,
    ← Matrix.mul_assoc Qᵀ Q,hQ,Matrix.one_mul]

/-- Assemble the backward SVD witness without a separate hypothesis on
the scale of B. Its Frobenius size is controlled by proximity of QB to H. -/
theorem finalBackwardWitness {m n t k : ℕ} (H : Mat m n) (V : Mat n t) (Q : Mat m t)
    (B E : Mat t n) (U : Mat t k) (d : Fin k → ℝ) (W : Mat n k)
    (u K₂ A D : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) (hA : 0 ≤ A) (hD : 0 ≤ D) (hK : 0 ≤ K₂)
    (hQ : Qᵀ*Q = 1) (hsvd : CompactSVD (B+E) U d W)
    (discarded : frob (H*(1-V*Vᵀ)) ≤ D*u*frob H)
    (retained : frob (H*(V*Vᵀ)-Q*B) ≤ A*u*frob H)
    (err : frob E ≤ K₂*u*frob B) :
    ∃ (Uₕ : Mat m k) (Δ : Mat m n), Uₕᵀ*Uₕ=1 ∧ H+Δ=Uₕ*diagonal d*Wᵀ ∧
      frob Δ ≤ (A+D+K₂*(1+A+D))*u*frob H := by
  have hdiff : frob (Q*B-H) ≤ (A+D)*u*frob H := by
    have hh := frob_add (H*(1-V*Vᵀ)) (H*(V*Vᵀ)-Q*B)
    rw [show H*(1-V*Vᵀ)+(H*(V*Vᵀ)-Q*B)=H-Q*B by rw [Matrix.mul_sub,Matrix.mul_one]; abel] at hh
    have flip (Z T : Mat m n) : frob (Z-T) = frob (T-Z) := by
      rw [← neg_sub T Z]; simp only [frob,frobSq,Matrix.neg_apply, neg_sq]
    rw [flip]; linarith
  have Bbound : frob B ≤ (1+A+D)*frob H := by
    have h := frob_add (Q*B-H) H
    rw [sub_add_cancel, frob_left_frame _ _ hQ] at h
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu' (add_nonneg hA hD)) (frob_nonneg H)]
  obtain ⟨Z,Δ,hZ,id',hh⟩ := backward_witness H Q B E U (diagonal d) W hQ hsvd.1 hsvd.2.2.2.2
  refine ⟨Z,Δ,hZ,id',?_⟩
  rw [hh]
  have tri := frob_add (Q*B-H) (Q*E)
  rw [frob_left_frame _ _ hQ] at tri
  nlinarith [mul_le_mul_of_nonneg_left Bbound (mul_nonneg hK hu)]

end
end RPHOSVD.Mixed
