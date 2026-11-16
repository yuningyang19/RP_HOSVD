#include <stdlib.h>
#include "mex.h"

/* Control the libc stream used by the unchanged native sparse-sign MEX.
 * Called outside the timed region; verify stream reset in the runner. */
void mexFunction(int nlhs, mxArray **plhs, int nrhs, const mxArray **prhs) {
    if (nrhs != 1 || nlhs != 0 || !mxIsDouble(prhs[0]) ||
        mxIsComplex(prhs[0]) || mxGetNumberOfElements(prhs[0]) != 1)
        mexErrMsgIdAndTxt("pilot:Seed", "Expected one real double scalar.");
    double seed = mxGetScalar(prhs[0]);
    if (seed < 0 || seed > 4294967295.0 || seed != (unsigned int)seed)
        mexErrMsgIdAndTxt("pilot:Seed", "Expected an unsigned integer seed.");
    srand((unsigned int)seed);
}
