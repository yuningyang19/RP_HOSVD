function root=setup_rp_hosvd(varargin)
%SETUP_RP_HOSVD Add only this checkout to the path and build native sources.
p=inputParser;p.addParameter('BuildMex',true,@islogical);p.parse(varargin{:});
root=fileparts(mfilename('fullpath'));
addpath(root,genpath(fullfile(root,'algorithms')),fullfile(root,'native'),fullfile(root,'third_party/tensor_toolbox'));
for family={'msk','rtsms','mln'},addpath(fullfile(root,'third_party',family{1}));end
if p.Results.BuildMex
 for name={'sparsesign','pilot_srand'}
  target=fullfile(root,'native',[name{1} '.' mexext]);
  if ~isfile(target),mex('-R2017b','-outdir',fullfile(root,'native'),fullfile(root,'native',[name{1} '.c']));end
 end
end
assert(exist('sparsesign','file')==3 && exist('pilot_srand','file')==3,'RP_HOSVD:Mex','Run setup_rp_hosvd with a configured C compiler (mex -setup C).');
end
