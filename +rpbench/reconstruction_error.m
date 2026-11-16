function e=reconstruction_error(T,U,G,blockBytes)
%RECONSTRUCTION_ERROR Blocked Frobenius reconstruction error.
if nargin<4,blockBytes=536870912;end
d=numel(U);dims=size(T);width=max(1,floor(blockBytes/(8*prod(dims(1:d-1)))));
e=0;idx=repmat({':'},1,d);
for lo=1:width:dims(d)
    hi=min(dims(d),lo+width-1);Z=product(double(G),U{d}(lo:hi,:),d,d);
    for j=1:d-1,Z=product(Z,U{j},j,d);end
    idx{d}=lo:hi;Z=Z-T(idx{:});e=hypot(e,norm(Z(:)));clear Z
end
end
function Z=product(Z,L,j,d)
dims=arrayfun(@(k)size(Z,k),1:d);left=prod(dims(1:j-1));right=prod(dims(j+1:d));
if j==1
    Z=L*reshape(Z,dims(j),[]);
elseif right==1
    Z=reshape(Z,left,dims(j))*L';
else
    Z=pagemtimes(reshape(Z,left,dims(j),right),L');
end
dims(j)=size(L,1);Z=reshape(Z,dims);
end
