function hex=file_sha256(file)
%FILE_SHA256 Streaming SHA-256 of an archive, without loading it into memory.
digest=java.security.MessageDigest.getInstance('SHA-256');f=fopen(file,'rb');assert(f>=0);c=onCleanup(@()fclose(f));
while ~feof(f),b=fread(f,4*2^20,'*uint8');digest.update(b);end
h=typecast(digest.digest(),'uint8');hex=lower(reshape(dec2hex(h,2).',1,[]));
end
