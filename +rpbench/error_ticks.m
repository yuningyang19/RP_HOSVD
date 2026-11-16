function error_ticks(ax,y)
%ERROR_TICKS Label transformed coordinates with the original error values.
v=y(isfinite(y));if isempty(v),v=0;end
hi=max(0,max(v));top=max(-5,ceil(log10(max(hi,1e-6))));values=[0 10.^(-6:top)];
if min(v)<-1e-6,values=[-fliplr(10.^(-6:ceil(log10(abs(min(v)))))) values];end
set(ax,'YTick',rpbench.error_scale(values));labels=cell(size(values));
for k=1:numel(values)
 if values(k)==0,labels{k}='0';else,labels{k}=sprintf('%s10^{%d}',repmat('-',1,values(k)<0),round(log10(abs(values(k)))));end
end
set(ax,'YTickLabel',labels);ylim(ax,[min(-.12,min(rpbench.error_scale(v))-.1),max(.4,max(rpbench.error_scale(v))+.2)]);
end
