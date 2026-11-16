import RPHOSVD.Backward
import RPHOSVD.BackwardTail
import RPHOSVD.BackwardGram
import RPHOSVD.Polar
import RPHOSVD.BackwardRetained
import RPHOSVD.DiscardedBackward
import RPHOSVD.BackwardWitness

/-! Uniform constants and closure for successful same-precision RP runs. -/
namespace RPHOSVD.Mixed
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section

private theorem frob_pos_of_ne_zero {m n : ℕ} (H : Mat m n) (hh : H ≠ 0) : 0 < frob H := by
  exact (norm_pos_iff.mpr hh).trans_le (opNorm_le_frob H)

/-- A uniform small-roundoff radius bounds a successful computed triangular
factor and produces a nearby orthonormal frame, uniformly over all retained dimensions. -/
theorem uniformBackwardGram (m n : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ C rad : ℝ, 0 < C ∧ 0 < rad ∧ ∀ {t : ℕ} (X : Mat m t) (G R : Mat t t) (u : ℝ),
      t ≤ n → 0 ≤ u → u ≤ rad → (∀ z : EuclideanSpace ℝ (Fin t), a * ‖z‖ ≤ ‖X.toEuclideanLin z‖) →
      ‖X‖ ≤ b → StoredProduct u Xᵀ X G →
      (∀ i j, |(Rᵀ*R-G) i j| ≤ gamma (t+1) u * (magnitude Rᵀ * magnitude R) i j) →
      (∀ i j, j < i → R i j = 0) → (∀ i, 0 < R i i) →
      IsUnit R.det ∧ ‖R‖ ≤ 2*b ∧ ∃ Q : Mat m t, Qᵀ * Q = 1 ∧ ‖X*R⁻¹-Q‖ ≤ C*u := by
  let L := gramScale m n
  let F := 5*L*b^2
  let J := (2/a)^2 * F
  let rad := min (1/(2*L)) (min (a^2/(2*F)) (1/(4*J)))
  have hL : 0 < L := by dsimp [L,gramScale]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  refine ⟨J,rad,hJ,by dsimp [rad]; positivity,?_⟩
  intro t X G R u htn hu hus lo hi hg hrr htri hdiag
  have hsL := (le_div_iff₀ (by positivity : 0 < 2*L)).mp (hus.trans (min_le_left ..))
  have hsF := (le_div_iff₀ (by positivity : 0 < 2*F)).mp (hus.trans ((min_le_right ..).trans (min_le_left ..)))
  have hsJ := (le_div_iff₀ (by positivity : 0 < 4*J)).mp (hus.trans ((min_le_right ..).trans (min_le_right ..)))
  obtain ⟨hR,gErr⟩ := backwardGram_budget X G R u b htn hu hi
    (show L*u ≤ 1/2 by linarith only [hsL]) hg hrr
  obtain ⟨hRd,_,gNorm⟩ := backwardGram_normalized X R a (F*u) ha lo htri hdiag gErr
    (by linarith only [hsF])
  have g : ‖(X*R⁻¹)ᵀ*(X*R⁻¹)-1‖ ≤ J*u := by simpa only [J,mul_assoc] using gNorm
  obtain ⟨Q,hQ,hQp⟩ := polarProximity (X*R⁻¹) (g.trans_lt (by linarith only [hsJ]))
  exact ⟨hRd,hR,Q,hQ,hQp.trans g⟩

/-- Appendix A.1, for every successful run satisfying the stored-product,
triangular Cholesky and small-SVD backward contracts. The run itself supplies
the computed factors. Its existence as an execution of a numerical routine
is a separate property from this backward-error postcondition. -/
theorem backwardStability : BackwardStabilityBound := by
  intro m n s η K K₁ K₂ hη hη' hK hK₁ hK₂
  obtain ⟨α,a,u₁,hα,ha,hu₁,sketch⟩ := sketchBackwardBudget m n s η K K₁ hη' hK hK₁
  let p := Real.sqrt (1+η)
  let q := Real.sqrt (1-η)
  let l := 1/(4*p)
  let b := 3/(2*q)+1
  let β := 2*((n+1:ℕ):ℝ)*(n+1:ℝ)
  let D := (1+K₁)*a
  have hp : 0 < p := Real.sqrt_pos.mpr (by linarith)
  have hq : 0 < q := Real.sqrt_pos.mpr (sub_pos.mpr hη')
  have hl : 0 < l := by dsimp [l]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨P,u₂,hP,hu₂,gram⟩ := uniformBackwardGram m n l b hl hb
  obtain ⟨A,hA,retained⟩ := retainedBackwardBudget m n β (2*b) P D hβ.le (by positivity) hP.le hD
  let c₀ := (2*a + 4*p*β + 1) / α
  let u₀ := min 1 (min u₁ (min u₂ (1/(2*((n+1:ℕ):ℝ)))))
  have h₀ : 0 < u₀ := by dsimp [u₀]; positivity
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  refine ⟨c₀,1/u₀,hc₀,by positivity,?_⟩
  intro c hc
  have hcp : 0 < c := hc₀.trans_le hc
  have hcprod : 2*a + 4*p*β + 1 ≤ c*α := (div_le_iff₀ hα).mp hc
  let D' := (Real.sqrt n * c * a + a)/q
  have hD' : 0 < D' := by dsimp [D']; positivity
  refine ⟨A+D'+K₂*(1+A+D'),by positivity,?_⟩
  intro t k H S Y E V T X G R Z B E₂ U d W u hH hS hemb hu hsmall run
  obtain ⟨hY,hE,hcount,hV,hdiv,hX,hG,_,hr,htri,hdiag,hZ,hB,hE₂,hsvd⟩ := run
  have hus : u ≤ u₀ := by
    rw [one_div_mul_eq_div, div_le_iff₀ h₀,one_mul] at hsmall
    exact hsmall
  have hu1 := hus.trans (min_le_left ..)
  have hsk := hus.trans ((min_le_right ..).trans (min_le_left ..))
  have hgr := hus.trans ((min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..)))
  have hnu := hus.trans ((min_le_right ..).trans ((min_le_right ..).trans (min_le_right ..)))
  have hn : ((n+1:ℕ):ℝ)*u ≤ 1/2 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2*((n+1:ℕ):ℝ))).mp hnu
    linarith only [ht]
  have hn' : (n:ℝ)*u ≤ 1/2 := by
    apply le_trans _ hn
    apply mul_le_mul_of_nonneg_right _ hu.le
    exact_mod_cast Nat.le_succ n
  have hf := frob_pos_of_ne_zero H hH
  obtain ⟨hylow,hserr,hyup⟩ := sketch H S Y E u hu hsk hS hemb hY hE
  obtain ⟨hxlo,hxhi,hxerr⟩ := backward_conditioning_threshold H S Y E V T X η u c α a
    hη hη' hu hα hf hylow hserr hn hcp (by linarith [mul_pos (by positivity : 0 < 4*p) hβ])
    (by change 4*p*β ≤ c*α; linarith) hemb hV hcount hdiv hX
  obtain ⟨hunit,hRR,Q,hQ,hQerr⟩ := gram X G R u hV.1 hu.le hgr hxlo hxhi hG hr htri hdiag
  have hYS : frob (scales (Y+E) t) ≤ D*frob H := by
    apply (retained_scales_le _ hV.1).trans
    apply (frob_add _ _).trans
    have hs : K₁*u ≤ K₁ := by simpa using mul_le_mul_of_nonneg_left hu1 hK₁
    change frob E ≤ K₁*u*frob Y at hE
    have he1 := hE.trans (mul_le_mul_of_nonneg_right hs (frob_nonneg Y))
    have he' := mul_le_mul_of_nonneg_left hyup hK₁
    dsimp [D]; linarith only [he1,he',hyup]
  obtain ⟨hres,_⟩ := retained H V X Q R (scales (Y+E) t) Z B u hV.1 hu.le hu1 hn'
    hV.2.1 hQ hunit hRR hQerr hYS hxerr hZ hB
  have loss := discardedBackward H S (Y+E) V (c*u*‖Y‖) η hη' (by positivity) hemb hV hcount
  have hdiscard : frob (H*(1-V*Vᵀ)) ≤ D'*u*frob H := by
    have hYnorm : ‖Y‖ ≤ a*frob H := (opNorm_le_frob Y).trans hyup
    have hs := mul_le_mul_of_nonneg_left hYnorm (by positivity : 0 ≤ Real.sqrt n * (c*u))
    change q*frob (H*(1-V*Vᵀ)) ≤ _ at loss
    dsimp [D']
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,le_div_iff₀ hq]
    linarith only [loss,hserr,hs]
  exact finalBackwardWitness H V Q B E₂ U d W u K₂ A D' hu.le hu1 hA.le hD'.le hK₂ hQ hsvd hdiscard hres hE₂

end
end RPHOSVD.Mixed
