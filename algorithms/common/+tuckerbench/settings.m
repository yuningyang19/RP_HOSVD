function [r,p,dims,opts,stream] = settings(T,r,p,opts)
%SETTINGS Shared validation for literature SS implementations (FP64 real).
assert(isa(T,'double') && isreal(T) && ~issparse(T) && ~isempty(T), ...
    'tuckerbench:Input','Provide a nonempty dense real double tensor.');
if isscalar(r), r=repmat(r,1,ndims(T)); else, r=r(:)'; end
d=numel(r); dims=arrayfun(@(j) size(T,j),1:d);
assert(d>=ndims(T) && d>=2 && all(r>=1 & r==floor(r) & r<=dims), ...
    'tuckerbench:Rank','Invalid target Tucker ranks.');
if isscalar(p), p=repmat(p,1,d); else, p=p(:)'; end
assert(numel(p)==d && all(p>=0 & p==floor(p) & isfinite(p)), ...
    'tuckerbench:Oversampling','p must be a nonnegative integer scalar/vector.');
defaults=struct('Seed',[],'Sequential',false,'Order',1:d, ...
    'Backend','auto','UseTree',true,'CaptureSketches',false);
names=fieldnames(defaults);
assert(isstruct(opts) && isscalar(opts),'tuckerbench:Options','Use scalar opts.');
assert(all(ismember(fieldnames(opts),names)),'tuckerbench:Options','Unknown option.');
for k=1:numel(names)
    if ~isfield(opts,names{k}), opts.(names{k})=defaults.(names{k}); end
end
assert(isequal(sort(opts.Order(:))',1:d),'tuckerbench:Order','Invalid mode order.');
opts.Order=opts.Order(:)';
assert(ismember(opts.Backend,{'auto','fast','tensorlab'}), ...
    'tuckerbench:Backend','Invalid contraction backend.');
assert(isscalar(opts.Sequential) && isscalar(opts.UseTree) && ...
    isscalar(opts.CaptureSketches),'tuckerbench:Options','Flags must be scalar.');
if isempty(opts.Seed)
    stream=RandStream.getGlobalStream;
else
    validateattributes(opts.Seed,{'numeric'}, ...
        {'scalar','integer','nonnegative','finite','<=',2^32-1});
    stream=RandStream('mt19937ar','Seed',opts.Seed);
end
end
