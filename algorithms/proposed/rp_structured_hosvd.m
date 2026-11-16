function [U,G,info] = rp_structured_hosvd(T,r,precision,sequential,family,useTree,policy,treePolicy)
% Structured RP with direct unfoldings and a dimension tree.
% Kronecker factors are applied through mode contractions.
% treePolicy: balanced (default) or planned.

% HOSVD: shared factors/tree. ST: fresh factors per changing tensor stage.
% Direct SVD branches use double svd(C,'econ').
%
% Copyright (c) 2026 Yiying Chen and Yuning Yang.
% Contact: yyang@gxu.edu.cn
% SPDX-License-Identifier: MIT
% See the LICENSE file in the repository root for the license terms.

if nargin<6, useTree=true; end
if nargin<7, policy=[]; end
if nargin<8, treePolicy='balanced'; end
d=ndims(T); U=cell(1,d);
info=struct('sketch_s',0,'recovery_s',0,'core_s',0,'widths',zeros(1,d), ...
    'subranks',zeros(d,d),'methods',{cell(1,d)},'retained',zeros(1,d));
if sequential
    G=T;
    for j=1:d
        n=size(G,j); M=numel(G)/n;
        if strcmp(precision,'mixed'), cutoff=rp_mixed_svd_switch_ratio(n,policy);
        else, cutoff=rp_svd_switch_ratio(n,policy); end
        if M/n<=cutoff
            clock=tic; C=double(tens2mat(G,j,[1:j-1 j+1:d]));
            [V,~,~]=svd(C,'econ'); U{j}=V(:,1:r(j));
            info.recovery_s=info.recovery_s+toc(clock); info.methods{j}='svd';
        else
            clock=tic;
            if strcmp(precision,'mixed'), Z=single(G); else, Z=double(G); end
            dims=arrayfun(@(k) size(Z,k),1:d);
            s=rp_probe_subranks(dims,min(2*n,M),false,j);
            Phi=rp_probe_factors(dims,s,family,class(Z));
            other=[1:j-1 j+1:d];
            ratios=s(other)./dims(other); [~,order]=sortrows([ratios(:),-other(:)],[1 2]);
            for k=other(order(:)')
                Z=rp_structured_contract(Z,Phi{k},k);
            end
            Y=tens2mat(Z,j,other);
            info.sketch_s=info.sketch_s+toc(clock);
            C=tucker_unfold_tall(G,j,precision);
            [U{j},detail]=rp_structured_from_sketch(C,Y,r(j),precision,true);
            if strcmp(precision,'mixed') && size(U{j},2)<r(j)
                error('probe:MixedRank', ...
                    'Precision-dependent truncation retained fewer than r directions.');
            end
            info.recovery_s=info.recovery_s+detail.recovery_s;
            info.widths(j)=size(Y,2); info.subranks(j,:)=s;
            info.retained(j)=detail.retained; info.methods{j}='kron-rp';
            clear Z Y Phi
        end
        clear C
        clock=tic;
        if strcmp(precision,'mixed'), G=single(G); W=single(U{j}); else, W=U{j}; end
        G=tucker_mode_product_fast(G,W,j,'auto');
        info.core_s=info.core_s+toc(clock);
    end
else
    clock=tic;
    if strcmp(precision,'mixed'), Twork=single(T); else, Twork=double(T); end
    dims=size(T); targets=min(2*dims,prod(dims)./dims);
    s=rp_probe_subranks(dims,targets,true,[]);
    Phi=rp_probe_factors(dims,s,family,class(Twork));
    Y=rp_structured_sketches(Twork,Phi,useTree,treePolicy);
    info.sketch_s=toc(clock);
    for j=1:d
        C=tucker_unfold_tall(Twork,j,'native');
        [U{j},detail]=rp_structured_from_sketch(C,Y{j},r(j),precision,true);
        clear C
        info.widths(j)=size(Y{j},2); info.subranks(j,:)=s;
        info.retained(j)=detail.retained; info.methods{j}='kron-rp';
        info.recovery_s=info.recovery_s+detail.recovery_s;
    end
    clock=tic;
    W=cellfun(@(V) cast(V,'like',Twork),U,'UniformOutput',false);
    G=tucker_core_fast(Twork,W); info.core_s=toc(clock);
end
end
