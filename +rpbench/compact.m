function [U,G]=compact(C,F,r)
% Native representation -> orthogonal factors -> fixed-rank HOSVD.
% RTSMS author hosvd_trunc_rank: QR absorption, full-core MLSVD, then crop.
% Direct core HOSVD is the same projection; supports orders 3 through 6.
d=numel(r);Q=cell(1,d);R=cell(1,d);
for j=1:d,[Q{j},R{j}]=qr(F{j},0);end
for j=1:d,C=tmprod(C,R{j},j);end
V=cell(1,d);U=cell(1,d);
for j=1:d
    A=tens2mat(C,j,[1:j-1 j+1:d]);[W,~,~]=svd(A,'econ');
    V{j}=W(:,1:min(r(j),size(W,2)));U{j}=Q{j}*V{j};
end
G=tucker_core_fast(C,V,1:d);
end

