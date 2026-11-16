function [fig,data]=run_gram_accuracy(varargin)
%RUN_GRAM_ACCURACY Figure 2 singular-value and projection accuracy.

root=setup_rp_hosvd();p=inputParser;
p.addParameter('Sketch','ss',@(s)strcmp(s,'ss'));
p.addParameter('OutputRoot',fullfile(root,'results'));p.parse(varargin{:});o=p.Results;
    rngState = rng;
    restoreRng = onCleanup(@() rng(rngState));
    outDir=fullfile(o.OutputRoot,['gram_accuracy_' o.Sketch]);if ~isfolder(outDir),mkdir(outDir);end
    m = 2000;
    n = 50;
    s = 2*n;
    seeds = 20260930 + (0:19);
    ranks = 5:5:45;
    prescribed = logspace(0, -14, n).';
    methods = {'SVD', 'Gram', 'RP'};
    spectralErrors = zeros(numel(seeds), n, 3);
    projectionRatios = zeros(numel(seeds), numel(ranks), 3);
    retained = zeros(size(seeds));
    negativeEigenvalues = zeros(size(seeds));
    whitenedCondition = zeros(size(seeds));
    for trial = 1:numel(seeds)
        rng(seeds(trial), 'twister');
        [q, ~] = qr(randn(m,n), 0);
        [v, ~] = qr(randn(n,n), 0);
        a = (q .* prescribed.') * v';
        [~, dA, vA] = svd(a, 'econ');
        storedSpectrum = diag(dA);
        g = a'*a;
        [vG, lambda] = eig((g+g')/2, 'vector');
        [lambda, order] = sort(lambda, 'descend');
        vG = vG(:,order);
        negativeEigenvalues(trial) = nnz(lambda < 0);
        % Clip only when displaying singular values; never change Gram vectors.
        gramSpectrum = sqrt(max(lambda,0));
        pilot_srand(double(seeds(trial)));sketch=sparsesign(s,m,min(8,s));
        [~, dY, vY] = svd(sketch*a, 'econ');
        sketchSpectrum = diag(dY);
        keep = sketchSpectrum > 2*eps*sketchSpectrum(1);
        retained(trial) = nnz(keep);
        assert(retained(trial) == n, ...
            'This figure requires full retention; review the prescribed spectrum.');
        ve = vY(:,keep);
        de = sketchSpectrum(keep);
        x = (a*ve) ./ de.';
        whitenedCondition(trial) = cond(x);
        rSmall = chol(x'*x);
        b = (rSmall .* de.') * ve';
        [~, dB, vB] = svd(b, 'econ');
        spectra = {storedSpectrum, gramSpectrum, diag(dB)};
        bases = {vA, vG, vB};
        for method = 1:3
            spectralErrors(trial,:,method) = ...
                (abs(spectra{method}-prescribed)./prescribed).';
            for k = 1:numel(ranks)
                targetRank = ranks(k);
                w = bases{method}(:,1:targetRank);
                residual = norm(a-(a*w)*w', 'fro');
                optimal = norm(storedSpectrum(targetRank+1:end));
                projectionRatios(trial,k,method) = residual/optimal;
            end
        end
    end
    data = struct('shape', [m,n], 'sketchRows', s, 'seeds', seeds, ...
        'ranks', ranks, 'prescribedSpectrum', prescribed, 'methods', {methods}, ...
        'spectralErrors', spectralErrors, 'projectionRatios', projectionRatios, ...
        'retained', retained, 'negativeGramEigenvalues', negativeEigenvalues, ...
        'whitenedCondition', whitenedCondition, 'matlabVersion', version, ...
        'sketchDistribution', o.Sketch, ...
        'cutoff', '2*eps*sigma_1(Y)', ...
        'spectralReference', 'prescribed input spectrum', ...
        'projectionReference', 'tail energy from direct SVD of stored A');
    save(fullfile(outDir, 'gram_accuracy_data.mat'), 'data');
    fid = fopen(fullfile(outDir, 'gram_accuracy_data.json'), 'w');
    assert(fid >= 0, 'Cannot open the JSON output.');
    closeFile = onCleanup(@() fclose(fid));
    fprintf(fid, '%s\n', jsonencode(data, PrettyPrint=true));
    fig = plot_gram_accuracy(data);
    exportgraphics(fig, fullfile(outDir, 'gram_rp_accuracy.pdf'), ...
        ContentType='vector', BackgroundColor='white');
    exportgraphics(fig, fullfile(outDir, 'gram_rp_accuracy.png'), ...
        Resolution=220, BackgroundColor='white');
    savefig(fig, fullfile(outDir, 'gram_rp_accuracy.fig'));
    fprintf('MATLAB %s: %d trials, %d-by-%d, sketch %d, retained [%d,%d].\n', ...
        version, numel(seeds), m, n, s, min(retained), max(retained));
    fprintf('At rank %d, median residual ratios [SVD, Gram, RP]:\n', ranks(end));
    disp(squeeze(median(projectionRatios(:,end,:),1)).');
end

