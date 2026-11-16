import RPHOSVD.TensorScale
import RPHOSVD.TensorLift
import RPHOSVD.MixedAsymptotic
import RPHOSVD.MixedProjection

noncomputable section
namespace RPHOSVD.Tensor
open Matrix MeasureTheory

private theorem energy_eq {m n : ℕ} (A : Mixed.Mat m n) :
    Mixed.frobSq A = Projection.frobSq A := by
  rw [Projection.frobSq_cols, Mixed.frobSq, Finset.sum_comm]; rfl

/-- The Section 3 mixed tensor bound follows from the finite-u matrix theorem,
with constants uniform in all realizations and in the varying sequential unfoldings. -/
theorem tensorMP_of_explicit (finite : Mixed.MixedProjectionBound) : tensorMPClaim := by
  intro d n r s a mode η δ K lo hi ranks he he' hd hd' hl hh
  choose C D rad hC hD hrad bound using fun j ↦
    Mixed.uniform_asymptotic_of_explicit finite (width n r mode j) (n j) (s j) (r j)
      η K lo hi he.le he' hl hh
  let u₀ : ℝ := ∏ j, min 1 (rad j)
  have small (j : Fin d) : u₀ ≤ rad j := by
    unfold u₀; rw [Fintype.prod_eq_mul_prod_compl j]
    have rest : (∏ k ∈ {j}ᶜ, min 1 (rad k)) ≤ 1 := by
      exact Finset.prod_le_one (fun k _ ↦ le_min (by norm_num) (hrad k).le) (fun k _ ↦ min_le_left _ _)
    calc
      _ ≤ min 1 (rad j) * 1 := mul_le_mul_of_nonneg_left rest (le_min (by norm_num) (hrad j).le)
      _ ≤ _ := by simp
  let E := totalEnergy a
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  refine ⟨∑ j,C j, (∑ j,D j)*E, u₀, Finset.sum_nonneg (fun j _ ↦ hC j),
    mul_nonneg (Finset.sum_nonneg (fun j _ ↦ hD j)) hE,
    Finset.prod_pos (fun j _ ↦ lt_min (by norm_num) (hrad j)), ?_⟩
  intro u hu hsmall Ω inst μ hp S U hind law adapted bounded run
  apply (stepEmbeddings mode a μ S U η δ ⟨he,he'⟩ hd'.le hind law adapted).trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hg
  simp only [Set.mem_iInter,Set.mem_ofPred_eq] at hg
  let H (j : Fin d) := (unfolding a (U ω) mode j).transpose
  choose t Y V X G R ε low high runs out using (fun j ↦ run j ω (mixed_to_projection _ _ _ (hg j)))
  have hu' (j) : (U ω j).transpose * U ω j = 1 := (out j).2.2.1
  have size (j) : Mixed.frobSq (H j) ≤ E := energyBound _ _ _ hu' _
  have hm (j) := bound j (H j) (S j ω) (Y j) (V j) (X j) (G j) (R j) (U ω j) (ε j) u
    (hsmall.trans (small j)) (bounded j ω) (low j) (high j) (runs j) (out j)
  let T (j : Fin d) := tailEnergy (unfolding a (0 : Factors n r) .parallel j) (r j)
  let c := ∑ j,C j
  have hc : 0 ≤ c := Finset.sum_nonneg fun i _ ↦ hC i
  have one (j : Fin d) : Projection.frobSq ((H j)*(1-(U ω j)*(U ω j).transpose)) ≤
      (1+c*Real.sqrt u)*T j + D j*u*E := by
    have cs : C j ≤ c := Finset.single_le_sum (fun i _ ↦ hC i) (Finset.mem_univ j)
    have mt : Mixed.tailEnergy (H j) (r j) ≤ T j := mode_tail a (U ω) mode hu' j (ranks j).2
    have mt0 : 0 ≤ Mixed.tailEnergy (H j) (r j) :=
      Finset.sum_nonneg fun i _ ↦ by split <;> positivity
    rw [Matrix.mul_sub, Matrix.mul_one, ← energy_eq]
    exact (hm j).trans (add_le_add (mul_le_mul (by gcongr) mt mt0
      (by positivity))
      (mul_le_mul_of_nonneg_left (size j) (mul_nonneg (hD j) hu.le)))
  apply (local_to_tensor a (U ω) mode hu').trans
  apply (Finset.sum_le_sum (fun j _ ↦ one j)).trans_eq
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]
  change _ + (∑ j,D j)*u*E = _ + ((∑ j,D j)*E)*u
  dsimp [c,T,tailSum]; ring

/-- Paper Theorem 3.2. -/
theorem tensorMP : tensorMPClaim := tensorMP_of_explicit Mixed.mixedProjection

end RPHOSVD.Tensor
