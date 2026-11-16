function G = tucker_core_fast(T,U,order)
%TUCKER_CORE_FAST Form a Tucker core without permuting tensor storage.
%   G = TUCKER_CORE_FAST(T,U) contracts each mode j with U{j}'. T and
%   the dense factors must have the same single/double precision. Real and
%   complex arrays are supported. Factors need not be orthogonal.
%   Requires MATLAB R2020b or later (pagemtimes).
%
%   The default order minimizes the scalar multiplication count among
%   sequential mode orders; ties start at the last mode. An optional numeric
%   permutation ORDER overrides it. The output always uses the original
%   mode order. No input conversion or data-dependent timing is performed.
assert(isfloat(T) && ~issparse(T),'tucker_core_fast:Input',...
    'T must be a dense single or double array.');
assert(iscell(U) && numel(U)>=2 && ndims(T)<=numel(U),...
    'tucker_core_fast:Factors','Provide one factor per tensor mode.');
d=numel(U); dims=arrayfun(@(j) size(T,j),1:d); r=zeros(1,d);
for j=1:d
    assert(ismatrix(U{j}) && ~issparse(U{j}) && ...
        strcmp(class(U{j}),class(T)) && size(U{j},1)==dims(j),...
        'tucker_core_fast:FactorType','Factors must match the input size and precision.');
    r(j)=size(U{j},2);
end
assert(all(r>=0 & r<=dims),'tucker_core_fast:Rank',...
    'Each factor must have between zero and n_j columns.');
if any(r==0)
    G=zeros(r,'like',T);
    return;
end
if nargin<3 || isempty(order)
    % Interchanging adjacent modes gives the key r_j/(1-r_j/n_j).
    % Use rightmost-first ties to favor tall matrix products on this layout.
    key=r./(1-r./dims);
    [~,order]=sortrows([key(:),-(1:d)'],[1 2]);
else
    assert(isnumeric(order) && isvector(order) && ...
        isequal(sort(order(:))',1:d),'tucker_core_fast:Order',...
        'Order must be a permutation of 1:numel(U).');
end
G=T;
for j=order(:)'
    left=prod(dims(1:j-1)); right=prod(dims(j+1:d));
    if j==1
        G=U{j}'*reshape(G,dims(j),[]);
    elseif right==1
        G=reshape(G,left,dims(j))*conj(U{j});
    else
        G=pagemtimes(reshape(G,left,dims(j),right),conj(U{j}));
    end
    dims(j)=r(j);
end
G=reshape(G,dims);
end
