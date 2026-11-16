function plot_all(varargin)
%PLOT_ALL Replot the eight main curve figures from locally generated records.
for group={'dimensions','spectra','shapes','real'},plot_experiment(group{1},varargin{:});end
end
