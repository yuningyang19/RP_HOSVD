# Figure 1: HOSVD time and accuracy comparison

Run `run_this_experiment.m` to compute the results and generate Figure 1. Run `plot_this_experiment.m` to redraw the figure from existing results.

The experiment uses a 200^4 tensor with medium spectral decay, K=100 and target ranks (20,20,20,20). Each of the nine methods is run five times, using SS test matrices for the randomized methods.

Measurements are saved in `results/shapes_paper/records/`; the figure is exported to `results/intro_comparison/intro_time_accuracy.pdf` and `.png`.
