import RPHOSVD.TensorResidual
import RPHOSVD.TensorCompression
import RPHOSVD.TensorProbability
import RPHOSVD.Refined
import RPHOSVD.FullRetention

noncomputable section
namespace RPHOSVD.Tensor
open MeasureTheory Matrix
variable {d : ℕ} {n r : Fin d → ℕ}

private theorem parallel_same (a : ArrayR n) (U : Factors n r) (j : Fin d) :
    unfolding a U .parallel j = unfolding a (0 : Factors n r) .parallel j := by
  ext i c
  have hn (k : Fin d) : ¬compressBefore .parallel j k := by simp [compressBefore]
  simp [unfolding, hn]

theorem local_to_tensor (a : ArrayR n) (U : Factors n r) (mode : Schedule)
    (hu : ∀ j, (U j).transpose * U j = 1) :
    residualSq a U ≤ ∑ j, Projection.frobSq ((unfolding a U mode j).transpose *
      (1-U j*(U j).transpose)) := by
  cases mode with
  | sequential => exact (sum_current_loss a U hu).le
  | parallel =>
    rw [sum_current_loss a U hu]
    apply Finset.sum_le_sum; intro j _
    obtain ⟨F,hF,hH⟩ := unfoldingCompression a U j .sequential hu
    rw [hH, parallel_same a U, Matrix.mul_assoc]
    exact frobCompress _ _ hF

theorem mode_tail (a : ArrayR n) (U : Factors n r) (mode : Schedule)
    (hu : ∀ j, (U j).transpose * U j = 1) (j : Fin d) (hr : r j ≤ n j) :
    Projection.tailEnergy (unfolding a U mode j).transpose (r j) ≤
      tailEnergy (unfolding a (0 : Factors n r) .parallel j) (r j) := by
  obtain ⟨F,hF,hH⟩ := unfoldingCompression a U j mode hu
  rw [hH]; exact tailCompress _ _ hF hr

/-- Paper Theorem 3.1, for both execution schedules and also when only the
positive singular directions have been retained. -/
theorem tensorRP : tensorRPClaim := by
  intro Ω mst μ hprob d n r s a mode η δ ε S U ranks hη hη' hδ hδ' hind law adapted run
  have hgood := stepEmbeddings mode a μ S U η δ ⟨hη,hη'⟩ hδ'.le hind law adapted
  apply hgood.trans; refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hg
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hg
  choose t A eqH eqS eqε eqU scale using (fun j ↦ run j ω (hg j))
  have hu (j) : (U ω j).transpose * U ω j = 1 := by
    rw [← eqU j]; exact (A j).U_orthonormal
  let loc (j : Fin d) := Projection.frobSq ((unfolding a (U ω) mode j).transpose *
        (1-U ω j*(U ω j).transpose))
  let tail (j : Fin d) := tailEnergy (unfolding a (0 : Factors n r) .parallel j) (r j)
  have form (j) : loc j = Projection.frobSq ((A j).H - (A j).H * (A j).Pout) := by
    simp [loc,eqH j,Projection.Run.Pout,Projection.projector,eqU j, Matrix.mul_sub]
  have emb (j) : Projection.EmbedsRange (A j).H (A j).S η := by simpa [eqH j,eqS j] using hg j
  have transfer (j) : Projection.tailEnergy (A j).H (r j) ≤ tail j := by
    rw [eqH j]; exact mode_tail a (U ω) mode hu j (ranks j).2.1
  have total : residualSq a (U ω) ≤ ∑ j, loc j := local_to_tensor _ _ _ hu
  constructor
  · apply sumModeErrors loc tail r ε _ η total
    intro j; rw [form j]
    have hs := (Projection.refinedProjection (A j) η (emb j) (by simpa [eqε j] using scale j)).1
    rw [eqε j] at hs
    have hm : 2 * (r j : ℝ) * η^2 /(1-η) * (ε j)^2 =
         2*η^2/(1-η)*((r j : ℝ)*(ε j)^2) := by ring
    linarith [transfer j]
  · intro all
    apply total.trans; apply Finset.sum_le_sum; intro j _
    rw [form j, Projection.nonzeroRetentionExact (A j) η (emb j)]
    · exact transfer j
    · simpa only [fullRetained,eqH j,eqS j,eqε j] using all j

end RPHOSVD.Tensor
