function [ratio,table] = rp_svd_switch_ratio(n,policy)
%RP_SVD_SWITCH_RATIO Lookup the direct econ-SVD / RP aspect-ratio cutoff.
% Default calibration: Apple M3 Ultra, MATLAB R2025a, max threads 32,
% full-numerical-rank double inputs, n=50:50:3000, and default sparse-sign RP
% (8 nonzeros, s=min(2n,M)).
% Calibration: MATLAB R2025a, Apple M3 Ultra, 32 threads; see docs/EXPERIMENTS.md.
% Table column 1 is an upper short-side dimension; column 2 is the largest
% aspect ratio assigned to direct SVD. Intermediate n uses the next larger
% calibrated dimension. Above the last row, use the last cutoff as a default.
% A scalar policy overrides lookup; a two-column policy replaces the table.
% These are configurable performance choices, not embedding/error thresholds.
%
% Copyright (c) 2026 Yiying Chen and Yuning Yang.
% Contact: yyang@gxu.edu.cn
% SPDX-License-Identifier: MIT
% See the LICENSE file in the repository root for the license terms.

validateattributes(n,{'numeric'},{'real','scalar','integer','positive','finite'});
if nargin < 2 || isempty(policy)
    table = [
        50 32;
        100 32;
        150 48;
        200 32;
        250 24;
        300 24;
        350 32;
        400 32;
        450 24;
        500 16;
        550 32;
        600 24;
        650 32;
        700 32;
        750 32;
        800 16;
        850 32;
        900 24;
        950 24;
        1000 16;
        1050 16;
        1100 24;
        1150 64;
        1200 32;
        1250 24;
        1300 24;
        1350 64;
        1400 64;
        1450 64;
        1500 48;
        1550 48;
        1600 48;
        1650 96;
        1700 32;
        1750 64;
        1800 48;
        1850 64;
        1900 64;
        1950 64;
        2000 64;
        2050 48;
        2100 48;
        2150 64;
        2200 48;
        2250 48;
        2300 48;
        2350 48;
        2400 48;
        2450 48;
        2500 48;
        2550 32;
        2600 32;
        2650 48;
        2700 48;
        2750 64;
        2800 64;
        2850 64;
        2900 48;
        2950 48;
        3000 48;
    ];
else
    validateattributes(policy,{'numeric'},{'real','nonempty','nonnan'});
    if isscalar(policy)
        validateattributes(policy,{'numeric'},{'nonnegative'});
        ratio = policy;
        table = [];
        return;
    end
    if ~ismatrix(policy) || size(policy,2)~=2 || any(~isfinite(policy(:,1))) || ...
            any(policy(:,1)<=0) || any(diff(policy(:,1))<=0) || any(policy(:,2)<0)
        error('randPrecond:InvalidSwitchTable', ...
            'The switch table must have increasing positive dimensions and nonnegative ratios.');
    end
    table = policy;
end
k = find(n <= table(:,1),1);
if isempty(k)
    k = size(table,1);
end
ratio = table(k,2);
end
