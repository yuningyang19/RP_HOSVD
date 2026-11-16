function run_all(varargin)
%RUN_ALL Run the four Section 6 curve categories sequentially, then plot.
for group={'dimensions','spectra','shapes','real'},run_experiment(group{1},varargin{:});end
end
