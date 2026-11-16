function [U,G,info]=mlb_global_ss(T,r,sequential)
%MLB_GLOBAL_SS Two-stage SS Tucker decomposition with p=10.
% Minster, Li and Ballard (2024); see ../../THIRD_PARTY.md.
if sequential,method='MLB-ST-SS';else,method='MLB-H-SS';end
r=r(:)';d=numel(r);seq=sequential;
C=T;U=cell(1,d);detail=cell(1,d);
for j=1:d
 if seq,X=C;else,X=T;end
 dims=arrayfun(@(k)size(X,k),1:d);other=[1:j-1,j+1:d];A=tens2mat(X,j,other);
 B=10;
 L=min([dims(j),size(A,2),r(j)+B]);S=tuckerbench.sparseSign(L,size(A,2));
 Z=A*S';[Q,R]=qr(Z,0);short=sum(abs(diag(R))>eps*max(size(Z))*norm(R,'fro'))<r(j);detail{j}=struct('width',L,'ordinary_unfolding_SS',true,'rank_shortfall',short);
 U{j}=Q;
 if seq,C=tucker_mode_product_fast(C,Q,j,'auto');end
end
if ~seq,C=tucker_core_fast(T,U,1:d);end
[V,G]=tuckerbench.truncateCore(C,r,1:d,'auto');
for j=1:d,U{j}=U{j}*V{j};end
status='ok';if any(cellfun(@(x)x.rank_shortfall,detail)),status='rank_shortfall';end
info=struct('source','paper reimplementation','method',method,'status',status,'details',{detail},'sequential',seq);
end
