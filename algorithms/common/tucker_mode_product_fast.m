function [G,backend] = tucker_mode_product_fast(T,U,mode,backend)
%TUCKER_MODE_PRODUCT_FAST Contract mode with U' without permuting storage.
% T and U have the same single/double precision; real/complex are supported.
% U has size size(T,mode)-by-r. Other modes keep their original order.
% backend: fast (default), tensorlab, or an empirical shape-based auto policy.
if nargin<4, backend='fast'; end
assert(any(strcmp(backend,{'fast','tensorlab','auto'})), ...
    'tucker_mode_product_fast:Backend','Unknown contraction backend.');
validateattributes(mode,{'numeric'},{'scalar','integer','positive','finite'});
assert(isfloat(T) && ~issparse(T) && ismatrix(U) && ...
    ~issparse(U) && strcmp(class(T),class(U)), ...
    'tucker_mode_product_fast:Type','T and U must have matching floating types.');
d = max([ndims(T),mode,2]);
dims = arrayfun(@(j) size(T,j),1:d);
assert(size(U,1)==dims(mode) && size(U,2)<=dims(mode), ...
    'tucker_mode_product_fast:Size','Invalid factor dimensions.');
left = prod(dims(1:mode-1));
right = prod(dims(mode+1:d));
if strcmp(backend,'auto')
    % Tiny page matrices can be slower than a permuted BLAS call. Keep the
    % legacy path there; use pages for substantial intermediate left blocks.
    useFast = mode==1 || (right>1 && left>=16 && ...
        (dims(mode)>=40 || left>=32));
    if useFast, backend='fast'; else, backend='tensorlab'; end
end
if strcmp(backend,'tensorlab')
    G = tmprod(T,U,mode,'H');
    return;
end
if mode==1
    G = U'*reshape(T,dims(mode),[]);
elseif right==1
    G = reshape(T,left,dims(mode))*conj(U);
else
    G = pagemtimes(reshape(T,left,dims(mode),right),conj(U));
end
dims(mode) = size(U,2);
G = reshape(G,dims);
end
