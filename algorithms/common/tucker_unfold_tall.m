function At=tucker_unfold_tall(T,j,precision)
% Same entries as tens2mat(T,j,other)' in the required working precision.
% Cast before any large permutation, bypassing double(single(T)) round trips.
assert(any(strcmp(precision,{'native','double','mixed'})),'Unknown unfolding precision.');
if strcmp(precision,'mixed'), T=single(T);
elseif strcmp(precision,'double'), T=double(T); end
d=ndims(T); other=[1:j-1 j+1:d];
At=tens2mat(T,other,j);
if ~isreal(T), At=conj(At); end
end
