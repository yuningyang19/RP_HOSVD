import RPHOSVD.TensorCompression
import RPHOSVD.TensorResidual
import RPHOSVD.MixedRecovery

noncomputable section
namespace RPHOSVD.Tensor
open Matrix
variable {d : ℕ} {n r : Fin d → ℕ}

def totalEnergy (a : ArrayR n) : ℝ := ∑ x : Index n, (a x)^2

/-- Original unfolding only permutes entries. Current unfolding cannot
increase their total squared energy. This bound is deterministic and uniform
in the realized sketches and previous factors. -/
theorem energyBound (a : ArrayR n) (U : Factors n r) (mode : Schedule)
    (hu : ∀ j, (U j).transpose * U j = 1) (j : Fin d) :
    Mixed.frobSq (unfolding a U mode j).transpose ≤ totalEnergy a := by
  let Z := (0 : Factors n r)
  let O := (unfolding a Z .parallel j).transpose
  have orig : Projection.frobSq O = totalEnergy a := by
    have eq := stepEnergy a Z .parallel j 1 (by simp) (by simp)
    have hn (k : Fin d) : ¬compressBefore .parallel j k := by simp [compressBefore]
    simp only [Matrix.mul_one] at eq
    rw [show Projection.frobSq O = _ from eq]
    unfold totalEnergy
    apply Finset.sum_congr rfl; intro x _
    have id' := modeProduct_one n
    have delta (p : Index n) :
        (1 : Matrix (Fin (n j)) (Fin (n j)) ℝ) (x j) (p j) *
          ∏ k : {k : Fin d // k ≠ j}, (1 : Matrix (Fin (n k.val)) (Fin (n k.val)) ℝ) (x k.val) (p k.val) =
            (1 : Matrix (Index n) (Index n) ℝ) x p := by
      rw [← splitProd j (fun k ↦ (1 : Matrix (Fin (n k)) (Fin (n k)) ℝ) (x k) (p k))]
      exact congrArg (fun T ↦ T x p) id'
    simp_rw [if_neg (hn _), mul_assoc (a x*a _) _ _,delta]
    simp [Matrix.one_apply,mul_ite,pow_two]
  obtain ⟨F,hF,hH⟩ := unfoldingCompression a U j mode hu
  rw [hH]
  have bridge {m k : ℕ} (A : Mixed.Mat m k) : Mixed.frobSq A = Projection.frobSq A := by
    rw [Projection.frobSq_cols, Mixed.frobSq, Finset.sum_comm]
    rfl
  rw [bridge]; exact (frobCompress _ _ hF).trans orig.le

theorem mixed_to_projection {m n s : ℕ} (H : Projection.Mat m n) (S : Projection.Mat s m)
    (η : ℝ) (hg : Projection.EmbedsRange H S η) : Mixed.EmbedsRange η S H := by
  intro z
  have hh := hg.2.2 z.ofLp
  simpa only [EuclideanSpace.real_norm_sq_eq, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Projection.vecSq] using hh

end RPHOSVD.Tensor
