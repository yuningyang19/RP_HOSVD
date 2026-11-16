import RPHOSVD.BackwardTail
import RPHOSVD.MixedTruncation

noncomputable section
namespace RPHOSVD.Mixed
open Matrix
open scoped Matrix.Norms.L2Operator

private theorem frob_proj_eq {m n : ℕ} (A : Mat m n) : frobSq A = Projection.frobSq A := by
  rw [frobSq,Projection.frobSq_cols,Finset.sum_comm]; rfl

theorem complement_contract {m n t : ℕ} (A : Mat m n) (V : Mat n t) (hv : Vᵀ*V=1) :
    frob (A*(1-V*Vᵀ)) ≤ frob A := by
  apply Real.sqrt_le_sqrt
  rw [frob_proj_eq,frob_proj_eq]
  have hs := Projection.frobSplit A (V*Vᵀ) (by simp [transpose_mul])
    (by simp [Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V, hv])
  have hn : 0 ≤ Projection.frobSq (A*(V*Vᵀ)) := by
    rw [Projection.frobSq_cols]; exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  linarith

theorem truncated_sketch_loss {s n t : ℕ} (Y : Mat s n) (V : Mat n t) (ε : ℝ) (hε : 0 ≤ ε)
    (hV : LeadingRight Y V) (hc : t = (Finset.univ.filter (fun i : Fin n ↦ ε < sigma Y i.val)).card) :
    frob (Y*(1-V*Vᵀ)) ≤ Real.sqrt n * ε := by
  have discarded (i : Fin n) (hi : t ≤ i.val) : sigma Y i.val ≤ ε := by
    by_contra! hg
    have sub : Finset.Iic i ⊆ Finset.univ.filter (fun j : Fin n ↦ ε < sigma Y j.val) := by
      intro z hz
      have hzi : z ≤ i := Finset.mem_Iic.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg.trans_le
        (Y.toEuclideanLin.singularValues_antitone hzi)⟩
    have hd := Finset.card_le_card sub
    rw [Fin.card_Iic,← hc] at hd; omega
  obtain ⟨W,hW⟩ := Projection.exists_rightBasis Y
  let Z := Projection.firstCols W hV.1
  have h := leading_optimal Y hV Z (Projection.firstCols_orthonormal W hV.1 hW.1)
  rw [frob_proj_eq (Y*(1-Z*Zᵀ))] at h
  change _ ≤ Projection.frobSq (Y*(1-Projection.projector Z)) at h
  rw [Projection.basisResidualTail _ _ _ hW] at h
  have tail : Projection.tailEnergy Y t ≤ (n:ℝ)*ε^2 := calc
    _ ≤ ∑ _i : Fin n, ε^2 := by
      apply Finset.sum_le_sum; intro i _
      by_cases hi : t ≤ i.val
      · simpa only [if_pos hi,Projection.sigma,sigma] using pow_le_pow_left₀ (Y.toEuclideanLin.singularValues_nonneg _) (discarded i hi) 2
      · simp [hi,sq_nonneg]
    _ = _ := by simp
  apply (sq_le_sq₀ (frob_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hε)).mp
  rw [frob_sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  exact h.trans tail

/-- Under a noisy sketch the original discarded energy remains O(threshold + sketch error).
The bound includes t=0. -/
theorem discardedBackward {s m n t : ℕ} (H : Mat m n) (S : Mat s m) (Y : Mat s n) (V : Mat n t)
    (ε η : ℝ) (he : η < 1) (hε : 0 ≤ ε) (emb : EmbedsRange η S H)
    (hV : LeadingRight Y V) (hc : t = (Finset.univ.filter (fun i : Fin n ↦ ε < sigma Y i.val)).card) :
    Real.sqrt (1-η)*frob (H*(1-V*Vᵀ)) ≤ Real.sqrt n * ε + frob (Y-S*H) := by
  let C := 1-V*Vᵀ
  have emb' : EmbedsRange η S (H*C) := by
    intro z
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_mul] using emb (Matrix.toEuclideanLin C z)
  have low := embed_frob_lower (H*C) S η emb' he
  have align : S*(H*C) = Y*C + -((Y-S*H)*C) := by rw [Matrix.sub_mul,Matrix.mul_assoc]; abel
  rw [align] at low
  have hn (A : Mat s n) : frob (-A) = frob A := by simp only [frob,frobSq,Matrix.neg_apply,neg_sq]
  have tri := frob_add (Y*C) (-((Y-S*H)*C))
  rw [hn] at tri
  exact low.trans (tri.trans (add_le_add (truncated_sketch_loss Y V ε hε hV hc)
    (complement_contract _ V hV.2.1)))

end RPHOSVD.Mixed
