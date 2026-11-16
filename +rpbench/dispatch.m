function [U,G,info]=dispatch(T,r,name,framework)
%DISPATCH Run a method with the experiment parameters.
seq=strcmp(framework,'ST');info=struct('status','ok');d=numel(r);p=10*ones(1,d);
if strcmp(name,'SVD')
 if seq,[U,G]=hosvd_seq(T,r,'tensorlab');else,[U,G]=hosvd_classical(T,r,@trunSVD);end
elseif startsWith(name,'RP-')||startsWith(name,'MP-RP-')
 precision='double';if startsWith(name,'MP-'),precision='mixed';end
 if contains(name,'KronSS'),[U,G,info]=rp_structured_hosvd(T,r,precision,seq,'ss',true,[],'balanced');
 elseif seq
  if strcmp(precision,'double'),[U,G,info]=hosvd_seq_randprecond(T,r,[],'auto','prepared-tall');
  else,[U,G,info]=hosvd_seq_randprecond_mixed(T,r,'mixed',[],'auto','prepared-tall');end
 elseif strcmp(precision,'double'),[U,G]=hosvd_randprecond(T,r,[],'fast','prepared-tall');
 else,[U,G,info]=hosvd_randprecond_mixed(T,r,'mixed',[],'fast','prepared-tall');end
elseif strcmp(name,'MSK-SS')
 if seq,[G,U]=lit_msk_st(T,r,1:d,10,0);else,[G,U]=lit_msk_h(T,r,10,0,1:d);end
elseif startsWith(name,'MLB-')
 if endsWith(name,'KronSS')
  if seq,[U,G,info]=hosvd_seq_mlb_ss(T,r,p,struct());else,[U,G,info]=hosvd_mlb_ss(T,r,p,struct('UseTree',true));end
 else,[U,G,info]=mlb_global_ss(T,r,seq);end
elseif startsWith(name,'Shift-')
 if endsWith(name,'KronSS'),[U,G,info]=fair_kron_hosvd(T,r,p,'shift',seq,true);
 elseif seq,[U,G,info]=hosvd_seq_shift_ss(T,r,p,1,struct());else,[U,G,info]=hosvd_shift_ss(T,r,p,1,struct());end
elseif startsWith(name,'KRP-')||strcmp(name,'RTSMS-KronSS')
 parts=strsplit(name,'-');family=parts{1};suffix=parts{end};id=[family '-' framework '-' suffix];
 [U,G,info]=structured_followup(T,r,id);
elseif strcmp(name,'RTSMS-SS')
 if seq,[C,F]=lit_rtsms(T,4,1:d,r,'rank');[U,G]=rpbench.compact(C,F,r);
 else,[U,G,info]=symmetry_baselines(T,r,'rtsms-H');end
elseif startsWith(name,'Stable-MLN-')
 if seq
  kind='smln-SS';if endsWith(name,'KronSS'),kind='smln-KronSS';end
  [U,G,info]=symmetry_baselines(T,r,kind);
 elseif endsWith(name,'KronSS'),[U,G,info]=fair_kron_hosvd(T,r,zeros(1,d),'mln',false,true);
 else
  dims=arrayfun(@(j)size(T,j),1:d);L=min(dims-r,max(2,ceil(r/2)));
  [C,F]=lit_mln(tensor(T),r,L,1);[U,G]=rpbench.compact(double(C),F,r);
 end
else,error('RP_HOSVD:Method','Unknown method %s.',name);end
U=reshape(U,1,[]);
end
