function [V,G] = truncateCore(G,r,order,backend)
%TRUNCATECORE Exact ST-HOSVD second stage, using direct svd(C,'econ').
d=numel(r); V=cell(1,d);
for j=order
    C=tens2mat(G,j,[1:j-1 j+1:d]);
    [Q,~,~]=svd(C,'econ');
    assert(size(Q,2)>=r(j),'tuckerbench:Rank','Infeasible core target rank.');
    V{j}=Q(:,1:r(j));
    G=tucker_mode_product_fast(G,V{j},j,backend);
end
end
