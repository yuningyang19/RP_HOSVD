# Experiments

## Methods and parameters

Each HOSVD and STHOSVD comparison includes SVD; RP-SS, RP-KronSS, MP-RP-SS, MP-RP-KronSS; KRP-SS/KronSS, Shift-SS/KronSS, Stable-MLN-SS/KronSS, RTSMS-SS/KronSS; MSK-SS; MLB-SS/KronSS.

| Method | Parameters |
|---|---|
| RP and MP-RP | Sketch size 2n; KronSS factor sizes rounded upward. Numerical cutoff 2eps times the sketch spectral norm. |
| MSK | p=10 |
| MLB | p=10 |
| Shift | p=10; one shifted power iteration |
| KRP | p=0 |
| Stable-MLN | Extra width min(n-r,max(2,ceil(r/2))); stabilization delta=1 |
| RTSMS | Temporary ranks min(n,round(1.5r)); least-squares sampling factor k=4 |

SS matrices have min(s,8) signed nonzero entries per column, scaled by 1/sqrt(min(s,8)). KronSS applies Kronecker products of small SS factors through mode products. KRP-SS forms a Khatri–Rao product of SS factors; KRP-KronSS uses a right Kronecker sketch and r-column QR basis. RTSMS-KronSS uses KronSS for the auxiliary least-squares sketch.

## Data

`config/paper_inputs.json` specifies dimensions, target ranks and random seeds for 56 inputs and 110 settings.

- **Varying dimensions:** orders 3–6, K=n, target ranks round(0.2n), medium decay.
- **Varying spectra:** size 200^4, K=200, target ranks 10:10:100. Weights are proportional to 1/k, exp(-5.98(k-1)/(K-1)) or exp(-17.94(k-1)/(K-1)).
- **Fixed volume:** ten fourth-order shapes with volume 200^4, K=100 and target ranks (20,20,20,20).
- **Real data:** DC Mall, Miranda and CAVE, with ranks max(1,round(rho*n)), rho=0.05:0.05:0.50. Sources and download instructions are in [data/README.md](../data/README.md).

Synthetic tensors are generated from orthogonal CP factors. Synthetic experiments use five runs per configuration. Real-data experiments use one run for SVD/RP/MP-RP and two for the other methods. The default thread count is 32.

## Measurements and figures

The runner records algorithm time, reconstruction error, MATLAB/BLAS version and thread count. Reconstruction error is evaluated from the returned factors and core using blocked reconstruction. Input hashes check the regenerated data against the configured input identities.

The left panels show median speedup over the corresponding classical decomposition; the right panels show E/E_classic-1. Synthetic bands are the 20th–80th percentiles when five runs are available. The error-axis transformation is sign(y)*log10(1+abs(y)/1e-6), with ticks labeled in the original error units. Insets show the four RP/MP-RP curves.

Each experiment folder provides `run_this_experiment.m` and `plot_this_experiment.m`. Results are stored under `results/`.

- **Figure 1:** `experiments/00_intro_comparison`, HOSVD time bars for the S01 fixed-volume input.
- **Figure 2:** `experiments/05_gram_accuracy`, SVD/Gram/RP accuracy for 2000-by-50 matrices with SS and 2eps.
