% Replot existing Figure 2 data without recomputing matrices.
root=fileparts(fileparts(fileparts(mfilename('fullpath'))));addpath(root);
out=fullfile(root,'results','gram_accuracy_ss');q=load(fullfile(out,'gram_accuracy_data.mat'),'data');
f=plot_gram_accuracy(q.data);exportgraphics(f,fullfile(out,'gram_rp_accuracy.pdf'),'ContentType','vector');
exportgraphics(f,fullfile(out,'gram_rp_accuracy.png'),'Resolution',220);
