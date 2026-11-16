function [U,G,info]=fair_kron_hosvd(T,r,p,kind,sequential,useTree)
% Code sources: see ../../THIRD_PARTY.md.
% Rank-sized KronSS variants. Shared H factors; fresh ST stage factors.
if nargin<7,useTree=true;end
[r,p,dims,opts,stream]=tuckerbench.settings(T,r,p,struct('Sequential',sequential));d=numel(r);
info=struct('kind',kind,'sequential',sequential,'used_tree',~sequential&&useTree,'widths',zeros(1,d),'subranks',zeros(d,d),'q',double(strcmp(kind,'shift')));
U=cell(1,d);G=T;
if ~sequential
 targets=min([r+p;dims;prod(dims)./dims],[],1);a=tuckerbench.subranks(dims,targets,true,[]);Phi=cell(1,d);
 for j=1:d,Phi{j}=full(tuckerbench.sparseSign(a(j),dims(j),stream)');end
 sketches=tuckerbench.modeSketches(T,Phi,useTree,'auto');
end
if strcmp(kind,'mln')
 assert(~sequential);L=min(dims-r,max(2,ceil(r/2)));Y=cell(1,d);
 % Independent family: drawn after all shared right factors, never reused as them.
 for j=1:d,Y{j}=full(tuckerbench.sparseSign(r(j)+L(j),dims(j),stream)');end
 G=tmprod(T,Y,1:d,'T');F=cell(1,d);tol=1e-16*norm(T(:));
 for j=1:d
  AX=sketches{j};F{j}=stable_nystrom_inversion(AX,Y{j}'*AX,tol);info.widths(j)=size(AX,2);info.subranks(j,:)=a;
 end
 [U,G]=compact_core(G,F,r);info.L=L;return
end
for j=1:d
 if sequential
  current=arrayfun(@(k)size(G,k),1:d);other=[1:j-1 j+1:d];ell=min([r(j)+p(j),current(j),prod(current(other))]);a=tuckerbench.subranks(current,ell,false,j);Phi=cell(1,d);
  for k=other,Phi{k}=full(tuckerbench.sparseSign(a(k),current(k),stream)');end
  Z=tuckerbench.contract(G,Phi,other,'auto');Yj=tens2mat(Z,j,other);clear Z
 else,Yj=sketches{j};sketches{j}=[];end
 info.widths(j)=size(Yj,2);info.subranks(j,:)=a;
 if sequential,C=tens2mat(G,j,[1:j-1 j+1:d]);else,C=tens2mat(T,j,[1:j-1 j+1:d]);end
 if strcmp(kind,'msk')
  [Q,~]=qr(Yj,0);B=Q'*C;[W,~,~]=svd(B,'econ');U{j}=Q*W(:,1:r(j));clear Q B W
 elseif strcmp(kind,'shift')
  [Q,~,~]=svd(Yj,'econ');ell=size(Q,2);alpha=0;
  % Original q=1 shifted iteration and rank truncation, no extra rSVD stage.
  [Q,D,~]=svd(C*(C'*Q)-alpha*Q,'econ');smallest=D(ell,ell);if smallest>alpha,alpha=(smallest+alpha)/2;end
  U{j}=Q(:,1:r(j));clear Q D
 else,error('fair:Kind','Unknown variant');end
 clear C Yj
 if sequential,G=tucker_mode_product_fast(G,U{j},j,'tensorlab');end
end
if ~sequential,G=tucker_core_fast(T,U);end
end
function [U,G]=compact_core(C,F,r)
d=numel(r);Q=cell(1,d);R=cell(1,d);
for j=1:d,[Q{j},R{j}]=qr(F{j},0);end
for j=1:d,C=tmprod(C,R{j},j);end
V=cell(1,d);U=cell(1,d);
for j=1:d,A=tens2mat(C,j,[1:j-1 j+1:d]);[W,~,~]=svd(A,'econ');V{j}=W(:,1:min(r(j),size(W,2)));U{j}=Q{j}*V{j};end
G=tucker_core_fast(C,V);
end
