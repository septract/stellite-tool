This directory contains the optimisations that can be expressed for the tool (so excluding RMWs, non-atomics, release-acquire fences and relaxed) described in the POPL'15 paper of Vafeidis et al. SC tests are faked up with an SC fence after the given access.

The elimination optimisations are already covered by exising tests in the examples directory, so we list reordering optimisations here.

Pass and fail categorisation matches the claims of Vafeidis et al.
