% One-click paper experiment; run from any working directory.
root=fileparts(fileparts(fileparts(mfilename('fullpath'))));addpath(root);
run_experiment('spectra');
