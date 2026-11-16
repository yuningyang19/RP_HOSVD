function hash = array_hash(A)
%ARRAY_HASH SHA-256 of the numeric type, dimensions and array bytes.
assert(isfloat(A) && isreal(A) && ~issparse(A));
md=java.security.MessageDigest.getInstance('SHA-256');
md.update(unicode2native(jsonencode(struct('class',class(A),'size',size(A),'endian','little')),'UTF-8'));
for lo=1:2^20:numel(A)
    md.update(typecast(A(lo:min(numel(A),lo+2^20-1)),'uint8'));
end
hash=lower(reshape(dec2hex(typecast(md.digest(),'uint8'),2)',1,[]));
end
