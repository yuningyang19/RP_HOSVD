function download_real_data(whichData,varargin)
%DOWNLOAD_REAL_DATA Fetch original source data into an ignored local directory.
% No raw data or measured results are committed to this repository.
root=fileparts(mfilename('fullpath'));if nargin<1,whichData='all';end
p=inputParser;p.addParameter('DataRoot',fullfile(root,'data'),@(x)ischar(x)||isstring(x));p.parse(varargin{:});dest=char(p.Results.DataRoot);if ~isfolder(dest),mkdir(dest);end
ids={'dc_mall','miranda','cave'};
urls={'https://engineering.purdue.edu/~biehl/Hyperspectral_Project.zip', ...
 'https://gitlab.com/tensors/tensor_data_miranda_sim/-/raw/main/density.mat', ...
 'https://www.cs.columbia.edu/CAVE/databases/multispectral/zip/complete_ms_data.zip'};
names={'Hyperspectral_Project.zip','density.mat','complete_ms_data.zip'};
hashes={'19c3210145afffc3293a2d62a3af43741323f9be867b80c20abdd1afa2e629a4','558189aa602310c7d3229a779c89eb8d8d6451d0baa9d2cc3b7f646a5d019e57','c22839ae5750e0f88451da40cc574b7c7de48f39fbfe0df44179f252afb91810'};
for j=1:3
 if ~strcmp(whichData,'all') && ~strcmp(whichData,ids{j}),continue;end
 f=fullfile(dest,names{j});
 if ~isfile(f),fprintf('Downloading %s from %s\n',ids{j},urls{j});websave(f,urls{j},weboptions('Timeout',600));end
 assert(strcmp(rpbench.file_sha256(f),hashes{j}),'Source checksum mismatch for %s; existing file left unchanged.',ids{j});
 if endsWith(f,'.zip'),target=fullfile(dest,ids{j});if ~isfolder(target),unzip(f,target);end;end
end
assert(strcmp(whichData,'all')||ismember(whichData,ids),'Unknown dataset name.');
end
