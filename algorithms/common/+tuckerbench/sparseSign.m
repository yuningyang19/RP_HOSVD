function S=sparseSign(s,M,stream)
%SPARSESIGN Sparse sign matrix using the native generator.
% Each column has min(8,s) signed nonzeros; s=1 gives a sign row.
if nargin>2, assert(isequal(stream,RandStream.getGlobalStream),'Use the global random stream.'); end
if s==1
    S=sparse(ones(1,M),1:M,2*randi(2,1,M)-3,1,M,M);
else
    S=sparsesign(s,M,min(8,s));
end
end
