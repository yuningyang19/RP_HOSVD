import RPHOSVD.TensorUnfold
import RPHOSVD.TensorNearBest

namespace RPHOSVD.Tensor
open Matrix
noncomputable section
variable {d : ℕ} {n r : Fin d → ℕ}

theorem splitProd (j : Fin d) (f : Fin d → ℝ) :
    (∏ k, f k) = f j * ∏ k : {k : Fin d // k ≠ j}, f k.val := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun k ↦ k = j) f]
  congr 1
  let : Fintype {k : Fin d // k = j} := Subtype.fintype _
  exact Fintype.prod_subsingleton (fun k : {k : Fin d // k = j} ↦ f k.val) ⟨j,rfl⟩

def prefixP (U : Factors n r) (q : ℕ) (k : Fin d) :
    Matrix (Fin (n k)) (Fin (n k)) ℝ :=
  if k.val < q then (U k)*(U k).transpose else 1

def captured (a : ArrayR n) (U : Factors n r) (q : ℕ) : ℝ :=
  ∑ x : Index n, ∑ p : Index n, a x * a p * ∏ k, prefixP U q k (x k) (p k)

private theorem rowP (U : Factors n r) (j : Fin d) (mode : Schedule)
    (k : {k : Fin d // k ≠ j}) (i l : Fin (n k.val)) :
    (∑ c, offFactor U mode j k i c * offFactor U mode j k l c) =
      (if compressBefore mode j k.val then U k.val * (U k.val).transpose else 1) i l := by
  classical
  by_cases h : compressBefore mode j k.val
  · conv_rhs => rw [if_pos h, Matrix.mul_apply]
    let e := finCongr (if_pos h : (if compressBefore mode j k.val then r k.val else n k.val) = r k.val)
    exact Fintype.sum_equiv e _ _ (fun c ↦ by simp [offFactor,h,e])
  · conv_rhs => rw [if_neg h,Matrix.one_apply]
    let e := finCongr (if_neg h : (if compressBefore mode j k.val then r k.val else n k.val) = n k.val)
    calc
      _ = ∑ c : Fin (n k.val), (if i=c then 1 else 0 : ℝ) * (if l=c then 1 else 0) :=
        Fintype.sum_equiv e _ _ (fun c ↦ by simp [offFactor,h,e])
      _ = _ := by simp [mul_ite]

theorem offGram (U : Factors n r) (mode : Schedule) (j : Fin d)
    (x p : shapeOff n j) :
    (∑ c : Cols n r mode j, offProduct U mode j x c * offProduct U mode j p c) =
      ∏ k : {k : Fin d // k ≠ j},
        (if compressBefore mode j k.val then U k.val * (U k.val).transpose else 1) (x k) (p k) := by
  simp only [offProduct, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k c ↦ offFactor U mode j k (x k) c * offFactor U mode j k (p k) c)]
  simp_rw [rowP]

private theorem energy_form {m b : ℕ} (H : Projection.Mat m b) (P : Projection.Mat b b)
    (hs : P.transpose=P) (hi : P*P=P) :
    Projection.frobSq (H*P) = ∑ c, ∑ i, ∑ l, H c i * H c l * P i l := by
  have h : Projection.frobSq (H*P) = (H*P*H.transpose).trace := by
    simp only [Projection.frobSq, transpose_mul, hs]
    rw [trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_assoc H P P, hi]
  rw [h]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro c _
  rw [Finset.sum_comm]
  congr 1; ext i
  apply Finset.sum_congr rfl; intro l _; ring

/-- Energy of a mode projection on the unfolding, expressed in the original entries.
Both the ordinary and compressed unfoldings appear in this identity. -/
theorem stepEnergy (a : ArrayR n) (U : Factors n r) (mode : Schedule) (j : Fin d)
    (P : Projection.Mat (n j) (n j)) (hs : P.transpose=P) (hi : P*P=P) :
    Projection.frobSq ((unfolding a U mode j).transpose * P) =
      ∑ x : Index n, ∑ p : Index n, a x * a p * P (x j) (p j) *
        ∏ k : {k : Fin d // k ≠ j},
          (if compressBefore mode j k.val then U k.val * (U k.val).transpose else 1)
              (x k.val) (p k.val) := by
  classical
  rw [energy_form _ _ hs hi]
  let w (x : Index n) (i : Fin (n j)) (c : Cols n r mode j) : ℝ :=
    a x * (if x j = i then 1 else 0) * offProduct U mode j (fun k ↦ x k.val) c
  have hD (b i) : (unfolding a U mode j).transpose b i = ∑ x, w x i ((Fintype.equivFin _).symm b) := rfl
  simp_rw [hD, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  -- Move the two original tensor indices to the outside; then collapse the row deltas.
  let g (c : Fin (width n r mode j)) i l x p :=
    (w x i ((Fintype.equivFin _).symm c) * w p l ((Fintype.equivFin _).symm c)) * P i l
  change (∑ c, ∑ i, ∑ l, ∑ x, ∑ p, g c i l x p) = _
  have swap (i : Fin (n j)) (c : Fin (width n r mode j)) :
      (∑ l, ∑ x, ∑ p, g c i l x p) = ∑ x, ∑ p, ∑ l, g c i l x p := by
    rw [Finset.sum_comm]; congr 1; ext x; rw [Finset.sum_comm]
  simp_rw [swap]
  have swap2 (c : Fin (width n r mode j)) :
      (∑ i, ∑ x, ∑ p, ∑ l, g c i l x p) = ∑ x, ∑ p, ∑ i, ∑ l, g c i l x p := by
    rw [Finset.sum_comm]; congr 1; ext x; rw [Finset.sum_comm]
  simp_rw [swap2]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro p _
  have delta (c : Fin (width n r mode j)) : (∑ i, ∑ l, g c i l x p) =
      a x * a p * P (x j) (p j) * (offProduct U mode j (fun k ↦ x k.val) ((Fintype.equivFin _).symm c) *
        offProduct U mode j (fun k ↦ p k.val) ((Fintype.equivFin _).symm c)) := by
    simp [g,w, mul_ite,ite_mul]; ring
  simp_rw [delta, ← Finset.mul_sum]
  congr 1
  rw [← offGram U mode j (fun k ↦ x k.val) (fun k ↦ p k.val)]
  exact Fintype.sum_equiv (Fintype.equivFin _).symm _ _ (fun _ ↦ rfl)

end
end RPHOSVD.Tensor
