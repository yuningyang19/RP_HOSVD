function [U,G,info] = hosvd_mlb_ss(T,r,p,opts)
% Code sources: see ../../THIRD_PARTY.md.
%HOSVD_MLB_SS Paper-based MLB Kronecker two-stage HOSVD, small-factor SS.
% [U,G,info]=hosvd_mlb_ss(T,r,p,opts). p defaults to 5; opts.Seed enables
% replay. H shares factors and a dimension tree; opts.Sequential uses the
% current tensor and independent per-stage factors (see hosvd_seq_mlb_ss).
% Implemented from arXiv:2211.13028v2, sections 4.2--4.4.
% Gaussian/SRHT factors are replaced by SS; no original distribution theorem
% is asserted. The second stage is direct-SVD ST-HOSVD on the small core.
if nargin<3 || isempty(p), p=5; end
if nargin<4, opts=struct(); end
clock=tic;
[r,p,dims,opts,stream]=tuckerbench.settings(T,r,p,opts); d=numel(r);
info=struct('source','MLB arXiv:2211.13028v2','implementation','paper SS adaptation', ...
    'sequential',opts.Sequential,'seed',opts.Seed,'widths',zeros(1,d), ...
    'oversampled_ranks',zeros(1,d),'subranks',zeros(d,d), ...
    'used_tree',~opts.Sequential && opts.UseTree,'total_seconds',0);
if opts.CaptureSketches, info.factors=cell(1,d); end
Uhat=cell(1,d); Ghat=T;
if ~opts.Sequential
    targets=min([r+p;dims;prod(dims)./dims],[],1);
    a=tuckerbench.subranks(dims,targets,true,[]); Phi=cell(1,d);
    for j=1:d, Phi{j}=full(tuckerbench.sparseSign(a(j),dims(j),stream)'); end
    Y=tuckerbench.modeSketches(T,Phi,opts.UseTree,opts.Backend);
    for j=opts.Order
        [Uhat{j},~]=qr(Y{j},0); info.widths(j)=size(Y{j},2);
        info.oversampled_ranks(j)=size(Uhat{j},2); info.subranks(j,:)=a;
    end
    if opts.CaptureSketches, info.factors=Phi; end
    Ghat=tucker_core_fast(T,Uhat,opts.Order);
else
    for j=opts.Order
        current=arrayfun(@(k) size(Ghat,k),1:d); other=[1:j-1 j+1:d];
        target=min([r(j)+p(j),current(j),prod(current(other))]);
        a=tuckerbench.subranks(current,target,false,j); Phi=cell(1,d);
        for k=other
            Phi{k}=full(tuckerbench.sparseSign(a(k),current(k),stream)');
        end
        Z=tuckerbench.contract(Ghat,Phi,other,opts.Backend);
        Yj=tens2mat(Z,j,other); [Uhat{j},~]=qr(Yj,0);
        info.widths(j)=size(Yj,2); info.oversampled_ranks(j)=size(Uhat{j},2);
        info.subranks(j,:)=a;
        if opts.CaptureSketches, info.factors{j}=Phi; end
        Ghat=tucker_mode_product_fast(Ghat,Uhat{j},j,opts.Backend);
    end
end
if opts.CaptureSketches, info.oversampled_factors=Uhat; end
[V,G]=tuckerbench.truncateCore(Ghat,r,opts.Order,opts.Backend);
U=cell(1,d);
for j=1:d, U{j}=Uhat{j}*V{j}; end
info.total_seconds=toc(clock);
end
