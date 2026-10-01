# Scalar implementation plan for Triple DES ECB

The specification follows FIPS 46-3 directly. Implementation representation
and performance choices belong in the subsequent architecture PRs.

## Source review

Reviewed OpenSSL at `00e2ed640baa4c8a8f234e8fef9d7688a6cdc002`:

* [Build selection](https://github.com/openssl/openssl/blob/00e2ed640baa4c8a8f234e8fef9d7688a6cdc002/crypto/des/build.info)
  uses `des-586.pl` on x86 and `des_enc.c` on x86-64, AArch64 and ARMv7.
* [Round code](https://github.com/openssl/openssl/blob/00e2ed640baa4c8a8f234e8fef9d7688a6cdc002/crypto/des/des_local.h)
  uses 32-bit halves, rotated round inputs and eight fused S-box/P tables.
  IP and FP use five masked exchanges instead of moving individual bits.
* [Triple-DES composition](https://github.com/openssl/openssl/blob/00e2ed640baa4c8a8f234e8fef9d7688a6cdc002/crypto/des/des_enc.c)
  applies IP and FP once per triple operation; its inner DES operation omits
  them. Encryption uses forward/reverse/forward round-key order.
* [Key expansion](https://github.com/openssl/openssl/blob/00e2ed640baa4c8a8f234e8fef9d7688a6cdc002/crypto/des/set_key.c)
  uses masked exchanges for PC-1 and tables for PC-2.
* [x86 assembly generator](https://github.com/openssl/openssl/blob/00e2ed640baa4c8a8f234e8fef9d7688a6cdc002/crypto/des/asm/des-586.pl)
  retains the fused-table approach and manages register pressure explicitly.

Reviewed AWS-LC at `81593218a606b7ef5230bcbe4d9ed456336d2abc`:

* [DES implementation](https://github.com/aws/aws-lc/blob/81593218a606b7ef5230bcbe4d9ed456336d2abc/crypto/des/des.c)
  uses the same masked permutations, fused S/P table strategy and unrolled
  alternating-half rounds. Triple DES similarly shares IP/FP across passes.
  Both the round tables and key-expansion tables have secret indices.

The useful structural choices are the masked permutation networks, sharing
IP/FP across all three passes, and keeping the two Feistel halves in
registers. Secret-indexed memory accesses cannot be used here.

## Initial scalar candidates

* **x86-64:** 32-bit Feistel halves in general-purpose registers. Compare
  Boolean S-box circuits with four 64-bit truth-table constants per S-box,
  selecting output bits with register shifts. The latter requires separately
  reviewed variable-shift ISA modeling; the present model has immediate
  shifts only. Share IP/FP across the three passes.
* **AArch64:** the same two-half structure, with its larger register file
  helping Boolean circuits. Compare 64-bit truth-table register lookup only
  after adding and reviewing LSRV semantics and its timing requirements.
* **ARMv7:** Boolean S-box circuits with fixed memory locations for spills,
  avoiding 64-bit variable shifts. Use masked exchanges for IP/FP and public
  round-key addresses. Measure circuit register pressure on this target.
* **x86:** Boolean S-box circuits with fixed spills and 32-bit halves.
  OpenSSL's assembly is useful for register allocation and IP/FP structure,
  but its secret table addresses cannot be retained.

Boolean circuits use existing scalar instructions and can provide a common
baseline without TCB additions. Batched scalar bitslicing is a further
candidate for ECB throughput: 32 lanes on 32-bit targets, 64 on 64-bit
ones, with measured handling of short messages and tails. Do not select a
winner from source inspection alone; compare complete APIs, including key
setup and short inputs, against OpenSSL in each architecture PR.

Key expansion must also be constant time. PC-1, 28-bit rotations and PC-2
are fixed bit operations; use fixed permutations rather than the upstream
secret-indexed key tables. The specification's canonical round-key layout
allows implementation-specific representations only when proved equivalent.
