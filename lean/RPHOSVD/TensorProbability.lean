import RPHOSVD.Adaptive
import RPHOSVD.TensorClaims

namespace RPHOSVD.Tensor
open MeasureTheory ProbabilityTheory
noncomputable section
universe v

/-- Current and past tuples of independent sketches remain independent, for arbitrary
measurable functions of the strictly earlier tuple. -/
theorem past_indep {Ω : Type v} [MeasurableSpace Ω] {d : ℕ} {β : Fin d → Type*}
    [∀ j, MeasurableSpace (β j)] {A : Type*} [MeasurableSpace A]
    {μ : Measure Ω} (S : ∀ j, Ω → β j) (j : Fin d)
    (h : iIndepFun S μ) (hm : ∀ j, Measurable (S j))
    (f : (∀ k : {k : Fin d // k < j}, β k.val) → A) (hf : Measurable f) :
    IndepFun (fun ω ↦ f (fun k ↦ S k.val ω)) (S j) μ := by
  classical
  let past := Finset.univ.filter (fun k : Fin d ↦ k < j)
  have hd : Disjoint past ({j} : Finset _) := by simp [past]
  have hh := h.indepFun_finset past {j} hd hm
  let g := fun (x : ∀ k : ↥past, β k.val) ↦ f (fun k ↦ x ⟨k.val, by simpa [past] using k.property⟩)
  have hg : Measurable g := hf.comp (measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _))
  exact hh.comp hg (measurable_pi_apply (⟨j, by simp⟩ : ↥({j} : Finset (Fin d))))

/-- Once the factors have been selected from the histories of their own modes,
the current transposed unfolding is determined by a measurable function of the *strict* past. -/
theorem unfolding_past {Ω : Type v} {d : ℕ} {n r s : Fin d → ℕ} (mode : Schedule)
    (a : ArrayR n) (S : ∀ j, Ω → Sketch n r s mode j) (U : Ω → Factors n r)
    (h : Adapted S U) (j : Fin d) :
    ∃ f : (∀ k : {k : Fin d // k < j}, Sketch n r s mode k.val) →
        Raw (width n r mode j) (n j),
      Measurable f ∧ ∀ ω, (unfolding a (U ω) mode j).transpose = f (fun k ↦ S k.val ω) := by
  classical
  choose sel hsel eq using h
  let F := fun (x : ∀ k : {k : Fin d // k < j}, Sketch n r s mode k.val) (k : Fin d) ↦
    if hk : k < j then (sel k (fun l ↦ x ⟨l.val, lt_of_le_of_lt l.property hk⟩) :
      Matrix (Fin (n k)) (Fin (r k)) ℝ) else 0
  let f := fun x ↦ (unfolding a (F x) mode j).transpose
  refine ⟨f, ?_, ?_⟩
  · have hF (k : Fin d) (i : Fin (n k)) (l : Fin (r k)) : Measurable (fun x ↦ F x k i l) := by
      by_cases hk : k < j
      · simp only [F, dif_pos hk]
        exact (measurable_pi_apply l).comp ((measurable_pi_apply i).comp ((hsel k).comp
          (measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _)))
      · simp only [F, dif_neg hk]; exact measurable_const
    apply measurable_pi_lambda; intro col; apply measurable_pi_lambda; intro row
    change Measurable (fun x ↦ unfolding a (F x) mode j row col)
    unfold unfolding
    apply Finset.measurable_sum; intro p _
    apply Measurable.const_mul
    apply Finset.measurable_prod; intro k _
    dsimp only
    split_ifs with hk
    · exact hF _ _ _
    all_goals exact measurable_const
  · intro ω; ext col row
    change unfolding a (U ω) mode j row col = unfolding a (F (fun k ↦ S k.val ω)) mode j row col
    unfold unfolding; apply Finset.sum_congr rfl; intro p _
    congr 1
    apply Finset.prod_congr rfl; intro k _
    dsimp only
    split_ifs with hk
    · simp only [F, dif_pos hk.2]; exact eq _ ω _ _
    all_goals rfl

/-- The embedding holds simultaneously for *actual* adaptive unfoldings with
probability at least 1−dδ; no conditioning on a future factor is assumed. -/
theorem stepEmbeddings {Ω : Type v} [MeasurableSpace Ω] {d : ℕ} {n r s : Fin d → ℕ}
    (mode : Schedule) (a : ArrayR n) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : ∀ j, Ω → Sketch n r s mode j) (U : Ω → Factors n r)
    (η δ : ℝ) (he : 0 < η ∧ η < 1) (hd : δ ≤ 1) (hind : iIndepFun S μ)
    (law : ∀ j, OSELaw μ (S j) (n j) η δ) (hU : Adapted S U) :
    1-d*δ ≤ μ.real (⋂ j, {ω | Projection.EmbedsRange
        (unfolding a (U ω) mode j).transpose (S j ω) η}) := by
  have hS (j) : Measurable (S j) := measurable_pi_lambda _ fun i ↦
    measurable_pi_lambda _ fun k ↦ (law j).1 i k
  let X (j : Fin d) (ω : Ω) : Raw (width n r mode j) (n j) :=
    (unfolding a (U ω) mode j).transpose
  have specs (j : Fin d) : Measurable (X j) ∧ IndepFun (X j) (S j) μ := by
    obtain ⟨f,hf,eq⟩ := unfolding_past mode a S U hU j
    have hx : X j = fun ω ↦ f (fun k ↦ S k.val ω) := funext eq
    rw [hx]
    exact ⟨hf.comp (measurable_pi_lambda _ fun k ↦ hS k.val), past_indep S j hind hS f hf⟩
  let good (j : Fin d) : Set Ω := {ω | Projection.EmbedsRange (X j ω) (S j ω) η}
  have meas (j : Fin d) : MeasurableSet (good j) := by
    let e : Set (Raw (width n r mode j) (n j) × Raw (s j) (width n r mode j)) :=
      {p | Projection.EmbedsRange p.1 p.2 η}
    change MeasurableSet ((fun ω ↦ (X j ω, S j ω)) ⁻¹' e)
    exact MeasurableSet.preimage (measurableEmbedding η) ((specs j).1.prodMk (hS j))
  have bound (j : Fin d) : 1-δ ≤ μ.real (good j) :=
    adaptiveEmbedding μ (X j) (S j) η δ he hd (specs j).1 (hS j) (specs j).2 (law j)
  exact simultaneous μ good δ meas bound

end
end RPHOSVD.Tensor
