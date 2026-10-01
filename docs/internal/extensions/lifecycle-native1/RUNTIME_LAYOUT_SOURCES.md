# Loaded integer layout correction

The earlier `RUNTIME_LAYOUT_SOURCES.json` selected the non-GMP source branch
before loaded-runtime validation. That selection was incorrect for the pinned
Windows binary. Its native-verification field was still pending; the failed
production startup correctly prevented graph measurements under that assumption.

The pinned runtime exports `lean::mpz::set(__mpz_struct*)`
(`_ZNK4lean3mpz3setEP12__mpz_struct`), present only in the `LEAN_USE_GMP`
branch of the recorded `mpz.h`/`mpz.cpp`. The installed `lean_gmp.h` also names
the GMP integration API. The runtime DLL SHA256 is
`5300B06EA3A45146C22996B0591CC6475ACB5B6B77802EDBECD65BAAD6485386`.

The successful bounded diagnostic is
`.lake/lifecycle-native1/runs/init-probe-20260923T091504228/RESULT.json`.
It compiled the committed `init_probe.c` supplement and linked a separate
diagnostic DLL using the original production shim object and the exact original
generated-object response file. It added one diagnostic export; it did not
replace canonical artifacts, relax initialization, or introduce another Lean
runtime. An SDK loader explicitly loaded the pinned runtime DLL, then this
augmented diagnostic DLL. Compilation, link, and execution returned zero;
stderr was empty, all 816 integrity pins passed, and the shared mutex was released.
The original initialization still returned status 5 during this diagnostic.

Both actual decoded values, `+(2^130+7)` and `-(2^130+7)`, had tag 250 and
runtime-reported outer object size 24. The diagnostic copied only bytes within
that runtime-reported bound, without dereferencing private limb pointers. At
offsets 8 and 12 the positive object held allocated count 3 and signed used
count 3; the negative object held allocated count 3 and signed used count -3.
Both values' absolute magnitudes serialized exactly to
`0700000000000000000000000000000004` through the compiled codec.

The bundled `libgmp.a` has SHA256
`50C6C0F596274B87A7DCE9AB1FB7844C4ACE58A1AE0BC9DADCE860EC080D77F5`.
Its `mp_bpl.o` member defines `__gmp_bits_per_limb` at read-only-data offset 0;
the data bytes begin `40000000`, establishing 64 bits for this bundled GMP.
The extracted member SHA256 is
`C193A5F8319C7E26C8587C1B6939F262C15E105C6F3B8B09667C8821A2DE92E1`.
This is reproducible with the pinned archive and `llvm-nm -A`, followed by
extracting `mp_bpl.o` and running `llvm-objdump -s` on that member. The archive
was pinned in the successful diagnostic receipt before this read-only inspection.

GMP documents that `_mp_alloc` measures allocated limbs, while the sign and
used limb count are encoded together in `_mp_size`; both fields are `int`.
The pointer references little-endian limbs. Consequently, requested external
backing is `_mp_alloc * 8`, independently of the 24-byte runtime-reported
outer object. It is not `abs(_mp_size) * 8`, allocator usable size, or RSS.
[GMP integer internals](https://gmplib.org/manual/Integer-Internals).

The repaired production verifier checks outer size, allocation/used-field
bounds, both signs, the three actual 64-bit limbs `[7, 0, 4]`, and exact byte
serialization before enabling graph traversal. This remains a pinned native
layout/ABI assumption tested against actual values, not a Lean kernel theorem.
Production startup after rebuilding the repaired shim is a separate required
validation result; this diagnostic alone does not discharge it.

That rebuilt production startup subsequently passed with ordinary exit zero in
2.965348 seconds, at
`.lake/lifecycle-native1/replay/20260923T092251667-1857c5c9/RESULT.json`.
The actual fixed-global traversal completed under the GMP check. This is a
development startup receipt, separate from the still-pending complete native
campaign and final producing-source certification.

Earlier probe attempts are diagnostic development records, not semantic
lifecycle test failures: the first executable statically linked a second Lean
runtime and was discarded; a subsequent SDK attempt exposed that internal
compiled functions were not public DLL exports. The final supplement binds
those internal functions at link time against the verified objects instead.
