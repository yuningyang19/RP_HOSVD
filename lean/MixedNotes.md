# Mixed precision and the appendix

The manuscript labels are `prop:mp-recovery` and `prop:rp-backward-stability`. All Lean names below belong to `RPHOSVD.Mixed`.

## Mixed precision

`MixedRun` relates the input, sketch, retained right singular directions, rounded preconditioned matrix and symmetric Gram matrix. `RoundedProduct` includes both low-precision input conversions. It applies to the final symmetric Gram because its componentwise majorant is symmetric and unchanged by reflecting either triangle. `LeadingRight` allows choices inside a repeated singular subspace. `Output` uses the exact Gram-factor identity. All its solutions give the same recovered right Gram as the triangular Cholesky factor.

`MixedProjectionBound` states the positive-definiteness and projection-residual conclusions for finite roundoff. `tailEnergy` sums squared singular values beginning at zero-based index r. `conditioning_of_run`, `gram_budget_of_run` and `gram_posDef_of_run` give conditioning, spectral perturbation and positive definiteness from the modeled computation. In `MixedRecovery.lean`, `relative_gram_order` and `recovered_frob_comparison` transfer the Löwner sandwich to arbitrary right multipliers. `error_reduction_of_run` proves Equation `eq:mp-error-reduction`, including output rank, nesting and optimality at ties. `mixedProjection` in `MixedProjection.lean` combines this reduction with the noisy spectral separation and retained/discarded coupling.

In `MixedAsymptotic.lean`, `uniform_asymptotic_of_explicit` derives the asymptotic clause from the finite inequality, with uniform constants across all inputs of the given dimensions, all admissible sketches and all choices at ties. It bounds the additive term by D u ‖H‖²_F. The dimensions, rank, distortion, bound on sketch entries, and threshold-scale constants are fixed before C, D and the roundoff radius are chosen. `mixed_asymptotic_of_explicit` specializes the result to the single-matrix formulation.

## Same-precision backward error

`BackwardRun` specifies the ordinary multiplication model, column divisions, perturbed SVD inputs, the triangular Gram factor’s componentwise backward error, and the two products forming B. `BackwardStabilityBound` states the postcondition for successful runs under these contracts. The threshold and roundoff constants may depend on the two fixed routine constants, dimensions, distortion and a bound on the sketch norm. Only the final error constant may additionally depend on the threshold multiplier c. All are chosen before the input H.

`scaled_roundoff_frob` proves the bound γ_(n+1) √t ‖H‖_F for the scaled multiplication error from componentwise divisions and the ordinary product contract. `backward_conditioning_threshold` derives a uniform lower singular bound and upper operator-norm bound for the computed X. `sketchBackwardBudget`, `backwardGram_budget`, `backwardGram_normalized`, `polarProximity` and `discardedBackward` supply the remaining sketch, Gram, whitening and discarded-direction estimates. `retainedBackwardBudget` bounds the error of approximating the retained input by QB and the size of the actual computed B, allowing both multiplications in its formation to round. `finalBackwardWitness` composes the computed compact factors with Q and gives the backward reconstruction identity.

The appendix model uses orthogonal representatives for the computed singular vectors and absorbs their differences into the error terms. The postcondition applies to successful runs satisfying the stated numerical routine contracts.
