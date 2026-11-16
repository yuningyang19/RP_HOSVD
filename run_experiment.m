function records=run_experiment(group,varargin)
%RUN_EXPERIMENT Execute one paper category and draw H/ST time/error figures.
% Example: run_experiment('dimensions'); run_experiment('spectra','Profile','smoke');
root=setup_rp_hosvd();p=inputParser;
p.addParameter('Profile','paper',@(x)ismember(x,{'paper','smoke'}));
p.addParameter('Frameworks',{'H','ST'},@iscell);p.addParameter('Methods',{},@iscell);
p.addParameter('InputIds',{},@iscell);p.addParameter('MaxInputs',inf,@isnumeric);
p.addParameter('DataRoot',fullfile(root,'data'),@(x)ischar(x)||isstring(x));
p.addParameter('OutputRoot',fullfile(root,'results'),@(x)ischar(x)||isstring(x));
p.addParameter('DownloadData',true,@islogical);p.addParameter('Threads',32,@isnumeric);
p.addParameter('VerifyInput',true,@islogical);p.addParameter('Plot',true,@islogical);p.addParameter('Resume',true,@islogical);p.addParameter('Visible','off',@ischar);
p.parse(varargin{:});o=p.Results;assert(ismember(group,{'dimensions','spectra','shapes','real'}));
assert(all(ismember(o.Frameworks,{'H','ST'})));maxNumCompThreads(o.Threads);
items=rpbench.specs(group,o.Profile,root);
if ~isempty(o.InputIds),items=items(cellfun(@(x)ismember(x.id,o.InputIds),items));end
if strcmp(group,'real')&&strcmp(o.Profile,'smoke'),error('RP_HOSVD:Smoke','Use tests/run_smoke_tests for real-loader checks; real experiments always use original data.');end
items=items(1:min(numel(items),o.MaxInputs));assert(~isempty(items),'No matching inputs.');
methods=rpbench.methods();if ~isempty(o.Methods),methods=methods(ismember({methods.name},o.Methods));assert(numel(methods)==numel(o.Methods));end
out=fullfile(char(o.OutputRoot),[group '_' o.Profile]);recordDir=fullfile(out,'records');if ~isfolder(recordDir),mkdir(recordDir);end
for i=1:numel(items)
 spec=items{i};
 if strcmp(group,'real')&&o.DownloadData
  dataset=erase(spec.id,'real-');if strcmp(dataset,'dc-mall'),dataset='dc_mall';elseif strcmp(dataset,'cave32'),dataset='cave';end
  download_real_data(dataset,'DataRoot',o.DataRoot);
 end
 fprintf('Input %d/%d: %s\n',i,numel(items),spec.id);T=rpbench.input_tensor(spec,char(o.DataRoot),root);inputNorm=norm(T(:));inputHash='';
 if strcmp(o.Profile,'paper')&&o.VerifyInput
  inputHash=rpbench.array_hash(T);assert(strcmp(inputHash,spec.expected_input_sha256),'Original input SHA mismatch: %s.',spec.id);
 end
 % Warm up each selected method; reset the seeds before timed calls.
 rng(6321);warmDims=min(12,max(4,spec.dims(:)'));warm=randn(warmDims);warmRanks=2*ones(size(warmDims));
 for wf=1:numel(o.Frameworks)
  for wm=1:numel(methods)
   rng(6322);pilot_srand(6322);[warmU,warmG]=rpbench.dispatch(warm,warmRanks,methods(wm).name,o.Frameworks{wf}); %#ok<ASGLU>
  end
 end
 clear warm warmU warmG
 settings=spec.settings;if iscell(settings),settings=[settings{:}];end
 for si=1:numel(settings)
  setting=settings(si);r=setting.ranks(:)';
  for fi=1:numel(o.Frameworks)
   frame=o.Frameworks{fi};
   for mi=1:numel(methods)
    method=methods(mi);trials=5;if strcmp(group,'real'),trials=2;if method.classical||method.proposed,trials=1;end;end
    if strcmp(o.Profile,'smoke'),trials=1;end
    for trial=1:trials
     if strcmp(o.Profile,'paper')&&strcmp(group,'dimensions')&&numel(spec.dims)==6&&strcmp(frame,'H')&&strcmp(method.name,'MSK-SS')&&((spec.dims(1)==37&&trial>1)||spec.dims(1)==40),continue;end
     key=[setting.id '__' frame '__' method.name '__' num2str(trial)];file=fullfile(recordDir,[key '.mat']);
     if o.Resume && isfile(file),continue;end
     seed=spec.factor_seed_base+spec.seed_index*10000+si*100+trial;native=spec.native_seed_base+spec.seed_index*10000+si*100+trial;
     rng(seed,'twister');pilot_srand(double(native));
     row=struct('input_id',spec.id,'setting_id',setting.id,'group',group,'framework',frame,'method',method.name,'trial',trial,'ranks',r,'seconds',NaN,'error',NaN,'normalized_error',NaN,'status','error','message','','factor_seed',seed,'native_seed',native,'actual_ranks',[],'input_sha256',inputHash,'matlab',version,'blas',version('-blas'),'threads',maxNumCompThreads);
     % Save the measurement and method status.
     clock=tic;
     try
      [U,G,detail]=rpbench.dispatch(T,r,method.name,frame);row.seconds=toc(clock);
      row.actual_ranks=cellfun(@(Q)size(Q,2),U);row.status='ok';
      if any(row.actual_ranks~=r),row.status='rank_shortfall';end
      if isstruct(detail)&&isfield(detail,'status')&&~strcmp(detail.status,'ok'),row.status=detail.status;end
      row.error=rpbench.reconstruction_error(T,U,G);row.normalized_error=row.error/inputNorm;
      clear U G detail
     catch err
      row.seconds=toc(clock);row.message=err.message;
     end
     save(file,'row');fprintf('  %s %s trial %d: %s, %.3g s\n',frame,method.name,trial,row.status,row.seconds);
    end
   end
  end
 end
 clear T
end
files=dir(fullfile(recordDir,'*.mat'));records=struct([]);
for i=1:numel(files),q=load(fullfile(files(i).folder,files(i).name),'row');records=[records q.row];end %#ok<AGROW>
if ~isempty(records),writetable(struct2table(records,'AsArray',true),fullfile(out,'measurements.csv'));end
if o.Plot,plot_experiment(group,'Profile',o.Profile,'OutputRoot',o.OutputRoot,'Visible',o.Visible);end
end
