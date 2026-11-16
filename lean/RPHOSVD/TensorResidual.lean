import RPHOSVD.TensorLoss

namespace RPHOSVD.Tensor
open Matrix
noncomputable section
variable {d : ℕ} {n r : Fin d → ℕ}

private theorem e0 (a : ArrayR n) (U : Factors n r) :
    captured a U 0 = ∑ x, (a x)^2 := by
  classical
  have id' := modeProduct_one n
  unfold captured
  apply Finset.sum_congr rfl; intro x _
  have delta (p : Index n) : (∏ k, prefixP U 0 k (x k) (p k)) = (1 : Matrix (Index n) (Index n) ℝ) x p :=
    by simpa [prefixP, modeProduct] using congrArg (fun T ↦ T x p) id'
  simp_rw [delta]
  simp [Matrix.one_apply, mul_ite, pow_two]

private theorem ed (a : ArrayR n) (U : Factors n r) :
    captured a U d = ∑ x, a x * reconstruction a U x := by
  unfold captured reconstruction
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  simp [prefixP, Fin.is_lt, mul_assoc]

theorem residual_energy (a : ArrayR n) (U : Factors n r) (hu : ∀ k, (U k).transpose * U k = 1) :
    residualSq a U = captured a U 0 - captured a U d := by
  let F := modeProduct U
  let P := F*F.transpose
  have hs : P.transpose=P := by simp [P, transpose_mul]
  have hp : P*P=P := tuckerProjector_idempotent U hu
  let y := P.mulVec a
  have heq : reconstruction a U = y := reconstruction_eq a U
  have hy : y ⬝ᵥ y = a ⬝ᵥ y := by
    calc
      _ = a ⬝ᵥ (P.transpose.mulVec y) := by
        change (P.mulVec a) ⬝ᵥ y = _
        conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ = _ := by rw [hs]; change _ = a ⬝ᵥ (P.mulVec a)
                  rw [show P.mulVec y = (P*P).mulVec a from Matrix.mulVec_mulVec _ _ _, hp]
  have hh : ∑ x, (y x)^2 = ∑ x, a x * y x := by simpa [dotProduct, pow_two] using hy
  rw [residualSq, heq, e0, ed, heq]
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc,
    ← Finset.mul_sum,hh]
  ring

private theorem proj_props (U : Factors n r) (hu : ∀ k, (U k).transpose * U k = 1)
    (j : Fin d) : ((U j)*(U j).transpose).transpose = U j*(U j).transpose ∧
      (U j*(U j).transpose)*(U j*(U j).transpose) = U j*(U j).transpose := by
  constructor <;> simp [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (U j).transpose (U j), hu]

/-- At step j, energy before/after projection equals the energy captured by the
prefix with respectively j/j+1 factors. -/
theorem current_before_after (a : ArrayR n) (U : Factors n r) (hu : ∀ k, (U k).transpose * U k = 1)
    (j : Fin d) :
    let H := (unfolding a U .sequential j).transpose
    Projection.frobSq H = captured a U j.val ∧
    Projection.frobSq (H*(U j*(U j).transpose)) = captured a U (j.val+1) := by
  dsimp only
  have hh (P : Projection.Mat (n j) (n j)) (hs : P.transpose=P) (hi : P*P=P)
      (q : ℕ) (hj : prefixP U q j = P)
      (hother : ∀ k : {k : Fin d // k ≠ j}, prefixP U q k.val = if k.val < j then U k.val*(U k.val).transpose else 1) :
      Projection.frobSq ((unfolding a U .sequential j).transpose * P) = captured a U q := by
    rw [stepEnergy _ _ _ _ _ hs hi]
    unfold captured; apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro p _
    rw [splitProd j]
    simp_rw [hj, hother]
    have ho (k : Fin d) : compressBefore .sequential j k ↔ k < j := ⟨And.right, fun h ↦ ⟨rfl,h⟩⟩
    simp_rw [if_congr (ho _) rfl rfl]
    ring
  constructor
  · simpa using hh 1 (by simp) (by simp) j.val (by simp [prefixP]) (fun k ↦ rfl)
  · exact hh _ (proj_props U hu j).1 (proj_props U hu j).2 (j.val+1) (by simp [prefixP]) (fun k ↦ by
      have he : (k.val.val < j.val+1) ↔ k.val < j := by
        have hk := k.property
        change k.val.val < j.val + 1 ↔ k.val.val < j.val
        have hn : k.val.val ≠ j.val := fun h ↦ hk (Fin.ext h)
        omega
      simp [prefixP,he])

theorem sum_current_loss (a : ArrayR n) (U : Factors n r) (hu : ∀ k, (U k).transpose * U k = 1) :
    residualSq a U = ∑ j, Projection.frobSq ((unfolding a U .sequential j).transpose *
        (1-U j*(U j).transpose)) := by
  rw [residual_energy _ _ hu]
  have diff (j : Fin d) :
      Projection.frobSq ((unfolding a U .sequential j).transpose * (1-U j*(U j).transpose)) =
        captured a U j.val - captured a U (j.val+1) := by
    obtain ⟨before,after⟩ := current_before_after a U hu j
    have hs := Projection.frobSplit (unfolding a U .sequential j).transpose _
      (proj_props U hu j).1 (proj_props U hu j).2
    linarith only [before, after, hs]
  simp_rw [diff]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ captured a U j - captured a U (j+1))]
  exact (Finset.sum_range_sub' (captured a U) d).symm

end
end RPHOSVD.Tensor
