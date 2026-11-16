function s=styles()
%STYLES Fixed paper colors, paired SS/KronSS symbols and thick proposed lines.
colors={'#57616E','#0072B2','#009E73','#D55E00','#AA3377','#D9A441','#826A00','#CC99BB','#CC79A7','#A7B8C7','#7B6D8D','#795548','#6F4B39','#56B4E9','#B7BD78','#92953A'};
markers={'^','o','d','s','v','>','<','*','x','<','h','>','p','x','+','+'};
lines={'--','-','-','-','-',':','-.','--','--',':','-.','--','--',':','--','-.'};
s=struct('color',[],'marker','','line','');s=repmat(s,1,16);
for k=1:16,s(k).color=sscanf(colors{k}(2:end),'%2x%2x%2x',[1 3])/255;s(k).marker=markers{k};s(k).line=lines{k};end
end
