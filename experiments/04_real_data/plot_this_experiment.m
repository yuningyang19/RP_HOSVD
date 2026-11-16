% Replot the category from local records, without rerunning any algorithm.
root=fileparts(fileparts(fileparts(mfilename('fullpath'))));addpath(root);
plot_experiment('real');
