function [U,G,info]=symmetry_baselines(T,r,kind,explicitKron)
% Code sources: see ../../THIRD_PARTY.md.
% HOSVD/STHOSVD variants with compact fixed-rank outputs.
% RTSMS H follows the paper's parallel/nonsequential paragraph: run first
% single-mode step on original T, orthogonalize factors, project original T.
% Stable sequential MLN follows Bucci-Hashemi Alg 2 (sketch) with the original
% Bucci-Robol stable_nystrom_inversion recovery, followed by existing compact
% fixed-rank postprocessing.
if nargin<4,explicitKron=false;end
d=numel(r);dims=arrayfun(@(j)size(T,j),1:d);r=r(:)';
F=cell(1,d);info=struct('kind',kind,'widths',zeros(1,d),'L',[]);
if strcmp(kind,'rtsms-H')
 for j=1:d
  [~,f]=symmetry_rtsms_firstmode(T,4,[j 1:j-1 j+1:d],r,'rank');
  [F{j},~]=qr(f{j},0);
 end
 C=tucker_core_fast(T,F);
elseif startsWith(kind,'smln-')
 L=min(dims-r,max(2,ceil(r/2)));tol=1e-16*norm(T(:));C=T;info.L=L;
 for j=1:d
  current=arrayfun(@(k)size(C,k),1:d);other=[1:j-1 j+1:d];
  if strcmp(kind,'smln-SS')
   X=tuckerbench.sparseSign(r(j),prod(current(other)))';
   Y=full(tuckerbench.sparseSign(r(j)+L(j),current(j))');
   AX=tens2mat(C,j,other)*X;
  elseif strcmp(kind,'smln-KronSS')
   a=tuckerbench.subranks(current,r(j),false,j);Phi=cell(1,d);
   for k=other,Phi{k}=full(tuckerbench.sparseSign(a(k),current(k))');end
   Y=full(tuckerbench.sparseSign(r(j)+L(j),current(j))');
   if explicitKron
    X=1;for k=fliplr(other),X=kron(X,Phi{k});end
    AX=tens2mat(C,j,other)*X;
   else
    Z=tuckerbench.contract(C,Phi,other,'auto');AX=tens2mat(Z,j,other);clear Z
   end
  else,error('symmetry:Method','Unknown sequential MLN kind');end
  F{j}=stable_nystrom_inversion(AX,Y'*AX,tol);
  info.widths(j)=size(AX,2);
  C=tmprod(C,Y,j,'T');clear AX X Y Phi
 end
else,error('symmetry:Method','Unknown baseline');end
[U,G]=compact_fixed_rank(C,F,r);
end

function [U,G]=compact_fixed_rank(C,F,r)
% Same QR absorption + direct core HOSVD truncation as previous literature grid.
d=numel(r);Q=cell(1,d);R=cell(1,d);
for j=1:d,[Q{j},R{j}]=qr(F{j},0);end
for j=1:d,C=tmprod(C,R{j},j);end
V=cell(1,d);U=cell(1,d);
for j=1:d
 A=tens2mat(C,j,[1:j-1 j+1:d]);[W,~,~]=svd(A,'econ');
 V{j}=W(:,1:min(r(j),size(W,2)));U{j}=Q{j}*V{j};
end
G=tucker_core_fast(C,V);
end
