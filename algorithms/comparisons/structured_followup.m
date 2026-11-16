function [U,G,info]=structured_followup(T,r,method,explicit)
% Code sources: see ../../THIRD_PARTY.md.
% Structured KRP and RTSMS with compact Tucker outputs.
% KRP-KronSS is a right-Kronecker replacement of the KRP QR rangefinder:
% integer product widths round upwards; retain first r QR columns (p=0).

if nargin<4,explicit=false;end
r=r(:)';d=numel(r);dims=arrayfun(@(j)size(T,j),1:d);
seq=contains(method,'-ST-');info=struct('method',method,'widths',zeros(1,d),'subranks',{cell(1,d)},'status','ok');
if startsWith(method,'KRP-')
 U=cell(1,d);C=T;bank=[];
 if endsWith(method,'-SS') && ~seq
  R=max(r);Phi=cell(1,d);for j=1:d,Phi{j}=full(tuckerbench.sparseSign(R,dims(j))');end
  if explicit
   bank=cell(1,d);for j=1:d,other=[1:j-1 j+1:d];X=khatrirao(Phi(other),'r');bank{j}=tens2mat(T,j,other)*X;end
  else,bank=mttkrps(tensor(T),Phi);end
 end
 for j=1:d
  current=arrayfun(@(q)size(C,q),1:d);other=[1:j-1 j+1:d];
  if endsWith(method,'-SS')
   if ~seq,Z=bank{j}(:,1:r(j));bank{j}=[];
   else
    Phi=cell(1,d);for q=other,Phi{q}=full(tuckerbench.sparseSign(r(j),current(q))');end
    if explicit,X=khatrirao(Phi(other),'r');Z=tens2mat(C,j,other)*X;
    else,Z=mttkrp(tensor(C),Phi,j);end
   end
  else
   a=tuckerbench.subranks(current,r(j),false,j);Phi=cell(1,d);
   for q=other,Phi{q}=full(tuckerbench.sparseSign(a(q),current(q))');end
   if explicit,X=1;for q=fliplr(other),X=kron(X,Phi{q});end;Z=tens2mat(C,j,other)*X;
   else,D=tuckerbench.contract(C,Phi,other,'auto');Z=tens2mat(D,j,other);clear D;end
   info.subranks{j}=a;
  end
  info.widths(j)=size(Z,2);[Q,RR]=qr(Z,0);
  used=min(r(j),size(RR,2));RK=RR(:,1:used);
  numericalRank=sum(abs(diag(RK))>eps*max(size(Z))*norm(RK,'fro'));
  if numericalRank<r(j),info.status='rank_shortfall';end
  U{j}=Q(:,1:min(r(j),size(Q,2)));
  if seq,C=tmprod(C,U{j},j,'T');end
 end
 if seq,G=C;else,G=tucker_core_fast(T,U);end
else
 assert(startsWith(method,'RTSMS-')&&endsWith(method,'-KronSS'));
 if seq
  [C,F,ls]=followup_rtsms_kron(T,4,1:d,r,false,[],explicit);info.ls=ls;
 else
  temp=min(round(1.5*r),dims);targets=min(prod(dims)./dims,4*temp);
  a=tuckerbench.subranks(dims,targets,true,[]);Phi=cell(1,d);
  for q=1:d,Phi{q}=full(tuckerbench.sparseSign(a(q),dims(q))');end
  if explicit
   bank=cell(1,d);for j=1:d,other=[1:j-1 j+1:d];X=1;for q=fliplr(other),X=kron(X,Phi{q});end;bank{j}=tens2mat(T,j,other)*X;end
  else,bank=tuckerbench.modeSketches(T,Phi,true,'auto');end
  F=cell(1,d);info.subranks=a;info.ls=cell(1,d);
  for j=1:d
   [~,f,ls]=followup_rtsms_kron(T,4,[j 1:j-1 j+1:d],r,true,bank{j});bank{j}=[];
   [F{j},~]=qr(f{j},0);info.ls{j}=ls;
  end
  C=tucker_core_fast(T,F);
 end
 [U,G]=compact(C,F,r);
end
end
function [U,G]=compact(C,F,r)
d=numel(r);Q=cell(1,d);R=cell(1,d);V=cell(1,d);U=cell(1,d);
for j=1:d,[Q{j},R{j}]=qr(F{j},0);end
for j=1:d,C=tmprod(C,R{j},j);end
for j=1:d
 [W,~,~]=svd(tens2mat(C,j,[1:j-1 j+1:d]),'econ');V{j}=W(:,1:min(r(j),size(W,2)));U{j}=Q{j}*V{j};
end
G=tucker_core_fast(C,V);
end
