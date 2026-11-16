# RP_HOSVD

MATLAB implementation of randomized-preconditioned HOSVD/STHOSVD and their mixed-precision variants, with the Section 6 comparison experiments and plotting code, plus Figures 1–2 reproduction entry points.

Run the experiment scripts to generate numerical results and figures locally.

## Quick start

Use MATLAB R2025a (the development version), a configured C compiler (`mex -setup C`), and Statistics and Machine Learning Toolbox for the RTSMS sampling routines. Start MATLAB in this directory:

```matlab
setup_rp_hosvd
addpath('tests'); run_smoke_tests
```

The smoke test checks the method interfaces on a small tensor.

## Reproduce the experiments

Run `run_this_experiment.m` in the desired folder:

| Folder | Experiment | Outputs |
|---|---|---|
| `experiments/00_intro_comparison` | Figure 1: HOSVD time and accuracy comparison | Time bars and error values |
| `experiments/05_gram_accuracy` | Figure 2: SVD, Gram and RP accuracy | Singular-value and projection-error curves |
| `experiments/01_dimensions` | Orders 3–6, varying mode dimension | HOSVD/STHOSVD curves |
| `experiments/02_spectra` | Slow, medium, fast decay | HOSVD/STHOSVD curves |
| `experiments/03_fixed_volume` | Ten fourth-order shapes | HOSVD/STHOSVD curves |
| `experiments/04_real_data` | DC Mall, Miranda, CAVE | HOSVD/STHOSVD curves |

Each folder contains `run_this_experiment.m` to compute results and generate the figure, and `plot_this_experiment.m` to replot existing results. `run_all` runs the four tensor experiment categories (varying dimensions, spectra, fixed volume and real data); `plot_all` replots their figures.

For a small end-to-end example:

```matlab
run_experiment('spectra','Profile','smoke','Threads',2)
```

The default `Profile='paper'` uses the paper dimensions and repeat counts. Results are saved under `results/<category>_<profile>/` as per-call MAT records, a CSV, and PDF/PNG plots. Existing records are resumed by default. Use a fresh OutputRoot when changing code or settings, rather than mixing measurements.

Real data are downloaded from the original sources on first use and checked against archive SHA256 hashes. See [data sources](data/README.md), [parameters and experiment details](docs/EXPERIMENTS.md), and [code provenance](THIRD_PARTY.md).

For example, run Figures 1 and 2 from the repository root:

```matlab
run('experiments/00_intro_comparison/run_this_experiment.m')
run('experiments/05_gram_accuracy/run_this_experiment.m')
```

To redraw them from existing results:

```matlab
run('experiments/00_intro_comparison/plot_this_experiment.m')
run('experiments/05_gram_accuracy/plot_this_experiment.m')
```

## Lean statements and proofs

To read a particular result, find its paper number in the [statement and proof index](lean/COVERAGE.md) and follow the **Statement** or **Proof** link. Theorems 3.1–3.2 give tensor error and probability bounds for RP-HOSVD and RP-STHOSVD. Results 4.1–4.4 cover matrix conditioning and projection errors. Theorem 5.1 gives the mixed-precision matrix error bound. Proposition A.1 bounds the backward error of the factors returned by a successful run under the paper’s arithmetic model.

All eight proofs pass the Lean kernel check without `sorry`. To reproduce the check from the repository root, install elan and Python 3, then run

```sh
cd lean
lake exe cache get
lake build
python3 scripts/check_targets.py
```

The final command checks that each proof has the expected statement and reports the axioms it uses. The [Lean README](lean/README.md) documents the pinned Lean and Mathlib versions and the correspondence with the manuscript.

## License

The original code and accompanying documentation by Yiying Chen and Yuning Yang are released under the [MIT License](LICENSE). Third-party components are governed by their respective licenses and notices. See [code provenance](THIRD_PARTY.md) for sources and licensing details, including components whose upstream license is unspecified.
