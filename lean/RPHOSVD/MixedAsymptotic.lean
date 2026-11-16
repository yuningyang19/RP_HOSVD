import RPHOSVD.Mixed

/-! Uniform finite-dimensional estimates for the asymptotic clause. -/
namespace RPHOSVD.Mixed
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section

private def ones (m n : ℕ) : Mat m n := fun _ _ => 1

private theorem ones_norm_le (m n : ℕ) : ‖ones m n‖ ≤ (m+1 : ℝ) * (n+1) := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  let y := Matrix.toEuclideanLin (ones m n) z
  have hy (i : Fin m) : |y i| ≤ n * ‖z‖ := by
    change |∑ j, (1:ℝ) * z j| ≤ _
    simp only [one_mul]
    calc
      _ ≤ ∑ j, |z j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, ‖z‖ := Finset.sum_le_sum fun j _ => PiLp.norm_apply_le z j
      _ = _ := by simp
  have hsum : ‖y‖^2 ≤ (m:ℝ) * ((n:ℝ) * ‖z‖)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      (show (y i)^2 ≤ ((n:ℝ) * ‖z‖)^2 by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hy i) 2))
  change ‖y‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  refine hsum.trans ?_
  have hm : (m:ℝ) ≤ ((m:ℝ)+1)^2 := by nlinarith [sq_nonneg (m:ℝ), Nat.cast_nonneg (α:=ℝ) m]
  calc
    _ ≤ ((m:ℝ)+1)^2 * (((n:ℝ)+1) * ‖z‖)^2 := by gcongr; linarith
    _ = _ := by ring

theorem entry_le_norm {m n : ℕ} (A : Mat m n) (i : Fin m) (j : Fin n) :
    |A i j| ≤ ‖A‖ := by
  let e : EuclideanSpace ℝ (Fin n) := PiLp.single 2 j 1
  have h := (PiLp.norm_apply_le (Matrix.toEuclideanLin A e) i).trans (Matrix.l2_opNorm_mulVec A e)
  simpa [e, Matrix.toLpLin_apply, Matrix.mulVec_single, Real.norm_eq_abs] using h

theorem magnitude_bound {m n : ℕ} (A : Mat m n) (C : ℝ) (hc : 0 ≤ C)
    (h : ∀ i j, |A i j| ≤ C) : ‖magnitude A‖ ≤ C * ((m+1 : ℝ)*(n+1)) := by
  have hh := entrywise_opNorm_bound (magnitude A) (ones m n) C hc
    (fun i j => (by simpa [magnitude, ones] using h i j))
  exact hh.trans (mul_le_mul_of_nonneg_left (ones_norm_le m n) hc)

theorem gamma_upper (k : ℕ) (u : ℝ) (hu : 0 ≤ u) (hk : (k:ℝ)*u ≤ 1/2) :
    0 ≤ gamma k u ∧ gamma k u ≤ (2*(k:ℝ))*u := by
  have hd : 0 < 1-(k:ℝ)*u := by linarith
  unfold gamma
  refine ⟨div_nonneg (by positivity) hd.le, (div_le_iff₀ hd).mpr ?_⟩
  nlinarith [mul_nonneg (show 0 ≤ (k:ℝ)*u by positivity) (show 0 ≤ 1/2 - (k:ℝ)*u by linarith)]

private theorem sqrt_small (u : ℝ) (hu : 0 ≤ u) (h : u ≤ 1) :
    u ≤ Real.sqrt u ∧ Real.sqrt u ≤ 1 := by
  have hs := Real.sq_sqrt hu
  have hs' := Real.sqrt_nonneg u
  constructor <;> nlinarith [mul_nonneg hs' (show 0 ≤ 1 - Real.sqrt u by nlinarith)]

private theorem entry_t {m n s t r : ℕ} {H : Mat m n} {S : Mat s m} {Y : Mat s n}
    {V : Mat n t} {X : Mat m t} {G : Mat t t} {η ε u : ℝ}
    (run : MixedRun H S Y V X G η ε u r) (i : Fin n) (j : Fin t) :
    |(V * inverseScales Y t) i j| ≤ 1/ε := by
  have he := congrArg (fun A : Mat t t => A j j) run.retained_basis.2.1
  have hh : ∑ k, V k j ^ 2 = 1 := by simpa [Matrix.mul_apply, sq] using he
  have hv : |V i j| ≤ 1 := by
    have h0 := Finset.single_le_sum (f := fun k => V k j ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hh] at h0
    rw [abs_le]
    constructor <;> nlinarith
  have hs := retained_gt Y ε run.retained_basis.1 run.retained_count j
  have hs' := run.threshold_pos.trans hs
  rw [inverseScales, Matrix.mul_diagonal, abs_mul, abs_of_pos (inv_pos.mpr hs'), one_div]
  simpa only [one_mul] using mul_le_mul hv (inv_anti₀ run.threshold_pos hs.le)
    (inv_nonneg.mpr hs'.le) zero_le_one

private theorem exact_x_bound {m n s t r : ℕ} {H : Mat m n} {S : Mat s m} {Y : Mat s n}
    {V : Mat n t} {X : Mat m t} {G : Mat t t} {η ε u : ℝ}
    (run : MixedRun H S Y V X G η ε u r) :
    ‖H * (V * inverseScales Y t)‖ ≤ 3 / (2*Real.sqrt (1-η)) := by
  have hs : 0 < Real.sqrt (1-η) := Real.sqrt_pos.mpr (sub_pos.mpr run.distortion_lt)
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  change ‖Matrix.toEuclideanLin (H * (V * inverseScales Y t)) z‖ ≤ _
  convert (conditioning_of_run run z).2 using 1
  ring

theorem frobSq_nonneg {m n : ℕ} (H : Mat m n) : 0 ≤ frobSq H :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem entry_le_frob {m n : ℕ} (H : Mat m n) (i : Fin m) (j : Fin n) :
    |H i j| ≤ Real.sqrt (frobSq H) := by
  have hrow := Finset.single_le_sum (f := fun j => H i j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have htotal := Finset.single_le_sum (f := fun i => ∑ j, H i j ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt (frobSq_nonneg _)]
  exact hrow.trans htotal

private theorem asymptotic_budgets {m n s : ℕ} (r : ℕ)
    (η K a : ℝ) (hη : η < 1) (ha : 0 < a) :
    ∃ A B C u₀ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧ 0 < u₀ ∧ u₀ ≤ 1 ∧
    ∀ {t : ℕ} (H : Mat m n) (S : Mat s m) (Y : Mat s n) (V : Mat n t) (X : Mat m t) (G : Mat t t)
      (ε u : ℝ), u ≤ u₀ → (∀ i j, |S i j| ≤ K) →
      0 < Real.sqrt (frobSq H) → a * Real.sqrt u * Real.sqrt (frobSq H) ≤ ε →
      MixedRun H S Y V X G η ε u r →
      productBudget u S H ≤ A*Real.sqrt (frobSq H)*u ∧ productBudget u H (V * inverseScales Y t) ≤ B*Real.sqrt u ∧
      productBudget u Xᵀ X ≤ C*u := by
  let M := ((m+2:ℕ):ℝ)
  let N := ((n+2:ℕ):ℝ)
  let hnorm := (m+1:ℝ)*(n+1)
  let A := (2*M) * (|K| *((s+1:ℝ)*(m+1))) * hnorm
  let B := (2*N) * hnorm * ((n+1:ℝ)*(n+1)) / a
  let L := 3 / (2*Real.sqrt (1-η)) + B
  let J := L * ((m+1:ℝ)*(n+1))
  let C := (2*M) * (J*J)
  let u₀ := min 1 (min (1/(2*M)) (1/(2*N)))
  have hM : 0 < M := by dsimp [M]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hB : 0 ≤ B := by dsimp [B,hnorm]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨A,B,C,u₀,by dsimp [A,hnorm]; positivity,hB,by dsimp [C,J]; positivity,
    by dsimp [u₀]; positivity,min_le_left _ _,?_⟩
  intro t H S Y V X G ε u hu hS hf he run
  let f := Real.sqrt (frobSq H)
  have hmH : ‖magnitude H‖ ≤ hnorm*f := by
    simpa [mul_comm,hnorm,f] using magnitude_bound H f hf.le (entry_le_frob H)
  let T := V * inverseScales Y t
  have hu' := run.roundoff_pos
  have he' := run.threshold_pos
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu'
  have hroot := Real.sq_sqrt hu'.le
  have us := sqrt_small u hu'.le (hu.trans (min_le_left _ _))
  have hrt : (t:ℝ) ≤ n := by exact_mod_cast run.retained_basis.1
  have hγM := gamma_upper (m+2) u hu'.le (by
    change M*u ≤ 1/2
    have hh := (le_div_iff₀ (by positivity : 0 < 2*M)).mp
      (hu.trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith)
  have hγN := gamma_upper (n+2) u hu'.le (by
    change N*u ≤ 1/2
    have hh := (le_div_iff₀ (by positivity : 0 < 2*N)).mp
      (hu.trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith)
  have sm := magnitude_bound S |K| (abs_nonneg _) (fun i j => (hS i j).trans (le_abs_self K))
  have ds : productBudget u S H ≤ A*f*u := by
    unfold productBudget
    calc
      _ ≤ ((2*M)*u) * (‖magnitude S‖ * ‖magnitude H‖) :=
        mul_le_mul hγM.2 (Matrix.l2_opNorm_mul _ _) (norm_nonneg _) (by positivity)
      _ ≤ ((2*M)*u) * ((|K| *((s+1:ℝ)*(m+1))) * (hnorm*f)) := by gcongr
      _ = _ := by dsimp [A,hnorm]; ring
  have tm : ‖magnitude T‖ ≤ (1/ε) * ((n+1:ℝ)*(n+1)) := by
    apply (magnitude_bound T (1/ε) (by positivity) (entry_t run)).trans
    gcongr
  have dx : productBudget u H T ≤ B * Real.sqrt u := by
    unfold productBudget
    calc
      _ ≤ ((2*N)*u) * (‖magnitude H‖ * ‖magnitude T‖) :=
        mul_le_mul hγN.2 (Matrix.l2_opNorm_mul _ _) (norm_nonneg _) (by positivity)
      _ ≤ ((2*N)*u) * ((hnorm*f) * ((1/ε) * ((n+1:ℝ)*(n+1)))) := by
        dsimp only [hnorm]; gcongr
      _ = (2*N*(hnorm*f)*((n+1:ℝ)*(n+1))) * (u/ε) := by ring
      _ ≤ (2*N*(hnorm*f)*((n+1:ℝ)*(n+1))) * (Real.sqrt u / (a*f)) := by
        have hh : u*(a*f) ≤ Real.sqrt u * ε := by
          have hh := mul_le_mul_of_nonneg_left he hs.le
          calc
            u*(a*f) = Real.sqrt u * (a*Real.sqrt u*f) := by calc
              _ = (Real.sqrt u)^2 * (a*f) := by rw [hroot]
              _ = _ := by ring
            _ ≤ _ := hh
        have hdiv := (div_le_div_iff₀ he' (mul_pos ha hf)).mpr hh
        exact mul_le_mul_of_nonneg_left hdiv (by dsimp only [hnorm]; positivity)
      _ = _ := by
        have hf' : f ≠ 0 := hf.ne'
        dsimp only [B]
        field_simp [ha.ne', hf']
  have hx : ‖X‖ ≤ L := by
    have herror := rounded_product_opNorm H T X u hu'.le run.short_product run.precondition
    have hi := norm_add_le (X-H*T) (H*T)
    rw [sub_add_cancel] at hi
    have hxc := exact_x_bound run
    have hdx1 : B*Real.sqrt u ≤ B := by nlinarith [mul_le_mul_of_nonneg_left us.2 hB]
    change ‖H*T‖ ≤ _ at hxc
    dsimp only [L]
    linarith
  have mx : ‖magnitude X‖ ≤ J := by
    apply (magnitude_bound X L hL (fun i j => (entry_le_norm X i j).trans hx)).trans
    dsimp only [J]; gcongr
  have mt : magnitude Xᵀ = (magnitude X)ᵀ := rfl
  refine ⟨ds, dx, ?_⟩
  unfold productBudget
  rw [mt]
  calc
    _ ≤ ((2*M)*u) * (‖(magnitude X)ᵀ‖ * ‖magnitude X‖) :=
      mul_le_mul hγM.2 (Matrix.l2_opNorm_mul _ _) (norm_nonneg _) (by positivity)
    _ ≤ ((2*M)*u) * (J*J) := by rw [transpose_opNorm]; gcongr
    _ = C*u := by dsimp [C]; ring

/-- Uniform across all H and admissible runs of the specified dimensions. -/
theorem uniform_asymptotic_of_explicit (finite : MixedProjectionBound) (m n s r : ℕ)
    (η K a b : ℝ) (hη0 : 0 ≤ η) (hη : η < 1) (ha : 0 < a) (hab : a ≤ b) :
    ∃ C D u₀ : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ 0 < u₀ ∧
      ∀ {t : ℕ} (H : Mat m n) (S : Mat s m) (Y : Mat s n) (V : Mat n t) (X : Mat m t)
        (G R : Mat t t) (Vr : Mat n r) (ε u : ℝ), u ≤ u₀ → (∀ i j, |S i j| ≤ K) →
        a * Real.sqrt u * Real.sqrt (frobSq H) ≤ ε →
        ε ≤ b * Real.sqrt u * Real.sqrt (frobSq H) →
        MixedRun H S Y V X G η ε u r → Output Y V G R Vr →
        frobSq (H - H * (Vr * Vrᵀ)) ≤ (1+C*Real.sqrt u)*tailEnergy H r + D*u*frobSq H := by
  obtain ⟨A,B,C,u₁,hA,hB,hC,hu₁,hsmall,hsizes⟩ :=
    asymptotic_budgets (m:=m) (n:=n) (s:=s) r η K a hη ha
  let Kθ := 4*(1+η) * (3*B/Real.sqrt (1-η) + B^2 + C)
  let L := η * ((b + A)/Real.sqrt (1-η)) + 3*Real.sqrt (1+η)*A
  let v := 1/(2*(Kθ+1))
  have hl : 0 < Real.sqrt (1-η) := Real.sqrt_pos.mpr (sub_pos.mpr hη)
  have hb : 0 ≤ b := ha.le.trans hab
  have hK : 0 ≤ Kθ := by dsimp [Kθ]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  refine ⟨4*Kθ, 2*(r:ℝ)*L^2, min u₁ (v^2), by positivity, by positivity,
    lt_min hu₁ (sq_pos_of_pos hv), ?_⟩
  intro t H S Y V X G R Vr ε u hrad hS hεl hεu run out
  let f := Real.sqrt (frobSq H)
  have hf : 0 < f := by
    by_contra! hneg
    have hz : f = 0 := le_antisymm hneg (Real.sqrt_nonneg _)
    change ε ≤ b * _ * f at hεu
    rw [hz,mul_zero] at hεu
    exact run.threshold_pos.not_ge hεu
  let T := V * inverseScales Y t
  let ds := productBudget u S H
  let dx := productBudget u H T
  let dg := productBudget u Xᵀ X
  let θ := theta η dx dg
  have hu := run.roundoff_pos
  have hroot := Real.sq_sqrt hu.le
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hle := hrad.trans (min_le_left _ _)
  have huq := sqrt_small u hu.le (hle.trans hsmall)
  have hsu : Real.sqrt u ≤ v := by
    apply (sq_le_sq₀ hs.le hv.le).mp
    simpa only [hroot] using hrad.trans (min_le_right _ _)
  obtain ⟨hds,hdx,hdg⟩ := hsizes H S Y V X G ε u hle hS hf hεl run
  change ds ≤ A*f*u at hds
  change dx ≤ B*Real.sqrt u at hdx
  change dg ≤ C*u at hdg
  have hds0 : 0 ≤ ds := (norm_nonneg _).trans
    (rounded_product_opNorm S H Y u hu.le run.long_product run.sketch)
  have hdx0 : 0 ≤ dx := (norm_nonneg _).trans
    (rounded_product_opNorm H T X u hu.le run.short_product run.precondition)
  have hdg0 : 0 ≤ dg := (norm_nonneg _).trans
    (rounded_product_opNorm Xᵀ X G u hu.le run.long_product run.gram)
  have hθ : θ ≤ Kθ * Real.sqrt u := by
    have hx2 := pow_le_pow_left₀ hdx0 hdx 2
    rw [mul_pow, hroot] at hx2
    have hb2 := mul_le_mul_of_nonneg_left huq.1 (sq_nonneg B)
    have hgc := mul_le_mul_of_nonneg_left huq.1 hC
    dsimp only [θ,theta,Kθ]
    calc
      _ ≤ 4*(1+η) * (3*(B*Real.sqrt u)/Real.sqrt (1-η) + B^2*Real.sqrt u + C*Real.sqrt u) := by
        gcongr <;> first | exact hdx | exact hx2.trans hb2 | exact hdg.trans hgc
      _ = _ := by ring
  have hhalf : θ ≤ 1/2 := by
    apply hθ.trans
    apply (mul_le_mul_of_nonneg_left hsu hK).trans
    change Kθ * (1/(2*(Kθ+1))) ≤ 1/2
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hden : 0 < 1-θ := by linarith
  have ratio : (1+θ)/(1-θ) ≤ 1 + (4*Kθ)*Real.sqrt u := by
    calc
      _ = 1 + 2*θ/(1-θ) := by field_simp; ring
      _ ≤ 1 + 4*Kθ*Real.sqrt u := by
        apply add_le_add_right
        apply (div_le_iff₀ hden).mpr
        have hh := mul_nonneg (by positivity : 0 ≤ 4*Kθ*Real.sqrt u)
          (by linarith : 0 ≤ (1-θ) - 1/2)
        nlinarith only [hh,hθ]
  have hc : η*((ε+ds)/Real.sqrt (1-η)) + 3*Real.sqrt (1+η)*ds ≤ L * f * Real.sqrt u := by
    have hf' : ε ≤ b * f * Real.sqrt u := by simpa [f, mul_right_comm] using hεu
    have hds' := hds.trans (mul_le_mul_of_nonneg_left huq.1 (mul_nonneg hA hf.le))
    calc
      _ ≤ η*((b*f*Real.sqrt u+A*f*Real.sqrt u)/Real.sqrt (1-η)) +
        3*Real.sqrt (1+η)*(A*f*Real.sqrt u) := by gcongr
      _ = _ := by dsimp [L]; ring
  have henergy : 0 ≤ tailEnergy H r := by
    unfold tailEnergy
    exact Finset.sum_nonneg fun i _ => by split <;> positivity
  have hε := run.threshold_pos
  have hc2 := pow_le_pow_left₀ (by positivity) hc 2
  rw [mul_pow, mul_pow, hroot, Real.sq_sqrt (frobSq_nonneg H)] at hc2
  have hfinite := (finite H S Y V X G η ε u run).2 R Vr out
  refine hfinite.trans ?_
  change ((1+θ)/(1-θ))*_ + 2*(r:ℝ)*_ ≤ _
  calc
    _ ≤ (1+(4*Kθ)*Real.sqrt u)*tailEnergy H r + 2*(r:ℝ)*((L^2*frobSq H)*u) := by gcongr
    _ = _ := by ring

/-- Fixed-H version matching the manuscript's single-matrix theorem. -/
theorem mixed_asymptotic_of_explicit (finite : MixedProjectionBound) : MixedAsymptoticBound := by
  intro m n s r H η K a b ha hab
  by_cases hη : 0 ≤ η ∧ η < 1
  · obtain ⟨C,D,u₀,hC,hD,hu,est⟩ := uniform_asymptotic_of_explicit finite m n s r η K a b hη.1 hη.2 ha hab
    refine ⟨C,D*frobSq H,u₀,hC,mul_nonneg hD (frobSq_nonneg H),hu,?_⟩
    intro t S Y V X G R Vr ε u hu hS hε he run out
    simpa [mul_right_comm] using est H S Y V X G R Vr ε u hu hS hε he run out
  · refine ⟨0,0,1,le_rfl,le_rfl,zero_lt_one,?_⟩
    intro t S Y V X G R Vr ε u _ _ _ _ run
    exact (hη ⟨run.distortion_nonneg,run.distortion_lt⟩).elim

end
end RPHOSVD.Mixed
