# Figure 2: SVD, Gram and RP accuracy

Run `run_this_experiment.m` to compute the results and generate Figure 2. Run `plot_this_experiment.m` to redraw the figure from existing results.

The experiment uses 2000-by-50 matrices with random orthogonal factors and singular values geometrically decreasing from 1 to 1e-14. RP uses an SS test matrix with 100 rows and a 2eps numerical threshold. The target ranks are 5:5:45, with 20 trials. Curves show medians and bands show the 20th–80th percentiles.

Results are saved in `results/gram_accuracy_ss/`; the figure is exported as `gram_rp_accuracy.pdf` and `.png`.
