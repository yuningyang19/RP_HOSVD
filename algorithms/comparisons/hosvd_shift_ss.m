function [U,G,info] = hosvd_shift_ss(T,r,p,q,opts)
% Code sources: see ../../THIRD_PARTY.md.
%HOSVD_SHIFT_SS Che et al. adaptive-shift HOSVD with ordinary sparse sign.
% Reimplementation of arXiv:2506.04840v1 Algorithm 3 (Algorithm 4 for ST),
% replacing only the initial Gaussian projection with replayable SS.
% Defaults: p=10, q=1, as in the paper. opts.Seed enables replay.
% Each orthogonalization is direct svd(...,'econ'), including shifted steps.
% U is the first r columns of the final Q; no extra projected-rSVD step.
if nargin<3 || isempty(p), p=10; end
if nargin<4 || isempty(q), q=1; end
if nargin<5, opts=struct(); end
validateattributes(q,{'numeric'},{'scalar','integer','positive','finite'});
clock=tic;
[r,p,~,opts,stream]=tuckerbench.settings(T,r,p,opts); d=numel(r);
info=struct('source','Che et al. arXiv:2506.04840v1 Algorithms 3/4', ...
    'implementation','paper SS adaptation','sequential',opts.Sequential, ...
    'seed',opts.Seed,'q',q,'widths',zeros(1,d), ...
    'shifts',zeros(q+1,d),'total_seconds',0);
if opts.CaptureSketches, info.sketches=cell(1,d); end
U=cell(1,d); G=T;
for j=opts.Order
    other=[1:j-1 j+1:d];
    if opts.Sequential, C=tens2mat(G,j,other); else, C=tens2mat(T,j,other); end
    ell=min([r(j)+p(j),size(C,1),size(C,2)]);
    S=tuckerbench.sparseSign(ell,size(C,2),stream);
    [Q,~,~]=svd(full(C*S'),'econ'); alpha=0;
    if opts.CaptureSketches, info.sketches{j}=S; end
    clear S
    for iteration=1:q
        [Q,D,~]=svd(C*(C'*Q)-alpha*Q,'econ');
        smallest=D(ell,ell);
        if smallest>alpha, alpha=(smallest+alpha)/2; end
        info.shifts(iteration+1,j)=alpha;
    end
    U{j}=Q(:,1:r(j)); info.widths(j)=ell;
    G=tucker_mode_product_fast(G,U{j},j,opts.Backend);
end
info.total_seconds=toc(clock);
end
