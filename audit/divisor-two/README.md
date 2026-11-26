# Fixed-shape and noncoprime optima

Run `lake build Shellsort` from the P01 repository root. The unconditional roots `Shellsort.F09.verified_divisor_two_dominates` and `Shellsort.F09.verified_noncoprime_minimizers_divisor_two` compare the actual costs. The former produces one divisor-two table at each sufficiently large size that beats every table with divisor at least three on both counters.

Lean uses a trial below 0.6431 and a lower bound of 0.646 for all larger divisors. The [rational verifier](check_divisor_two.py) improves the trial to below 0.63837 by bounding the cross-class integral and reading the signed integral enclosure at shape one. Run `python audit/divisor-two/check_divisor_two.py`. The [integer generator](shell_constant_integer_certificate.py) regenerates the thirteen quadratures when run from a separate copy of this directory.

The [Lean kernel record](divisor_two_kernel.json) lists the four divisor-two roots. The [independent replay](scale_penalty_kernel.json) covers the two scale-penalty roots. With Python 3.11+, lean4export and Nanoda on the Lake path, use `lake env python audit/divisor-two/replay.py Shellsort/F09ScalePenalty.lean` to regenerate that export.
