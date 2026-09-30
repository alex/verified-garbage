import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for the x86-64 `mulx` (BMI2), `adcx` and `adox` (ADX)

Each expected value was computed on an x86-64 CPU (an Emerald Rapids Xeon), by the
same instruction in inline assembly, with RFLAGS set by `popfq` before it
and read by `pushfq` after it, and is compared with the model's result on
the same inputs: `mulx r64, r64, r64` with every flag preset and none
changed, `mulx r, r, r64` with both destinations the same register (which
gets the high half), and `adcx r64, r64` and `adox r64, r64` with each
carry in, and the other flags preset to values they keep; and each with a
memory source. This tests the transcription of the SDM's pseudocode (which
destination gets which half, which flag each addition reads and writes,
and which flags are left alone), which review of the TCB would otherwise
have to catch by eye.
-/

namespace VG.Test.X86_64Adx

open X86_64

/-- A state with `a` in `rdx`, `b` in `rcx`, `0xcccccccccccccccc` in every
other register, the given flags, and the 8 bytes at `0x1000`, all `0xff`,
readable. -/
def s (a b : BitVec 64) (cf zf sf of : Bool) : State where
  gpr r := if r = .rdx then a else if r = .rcx then b else if r = .rsi then 0x1000
    else 0xcccccccccccccccc
  cf := some cf
  zf := some zf
  sf := some sf
  of := some of
  mem _ := 0xff
  rd := [⟨0x1000, 8⟩]
  wr := []

/-! ## `mulx` -/

/-- Whether `mulx r8, r9, rcx` with `a` in `rdx` and `b` in `rcx` leaves the
high half `hi` in `r8` and the low half `lo` in `r9`, and the flags (CF and
SF set, ZF and OF clear) unchanged. -/
def mulx (a b hi lo : BitVec 64) : Bool :=
  (exec (.mulx .r8 .r9 (.reg .rcx)) (s a b true false true false)).map
      (fun t => (t.gpr .r8, t.gpr .r9, t.cf, t.zf, t.sf, t.of)) ==
    some (hi, lo, some true, some false, some true, some false)

#guard mulx 0x0 0x0 0x0 0x0
#guard mulx 0x0 0x3 0x0 0x0
#guard mulx 0x0 0x7fffffffffffffff 0x0 0x0
#guard mulx 0x0 0xfedcba9876543210 0x0 0x0
#guard mulx 0x1 0x8000000000000000 0x0 0x8000000000000000
#guard mulx 0x1 0x123456789abcdef0 0x0 0x123456789abcdef0
#guard mulx 0x1 0x26 0x0 0x26
#guard mulx 0x1 0x2 0x0 0x2
#guard mulx 0x2 0xdeadbeefcafebabe 0x1 0xbd5b7ddf95fd757c
#guard mulx 0x2 0x1 0x0 0x2
#guard mulx 0x2 0xffffffffffffffff 0x1 0xfffffffffffffffe
#guard mulx 0x2 0xfffffffffffffffe 0x1 0xfffffffffffffffc
#guard mulx 0x3 0x3 0x0 0x9
#guard mulx 0x3 0x7fffffffffffffff 0x1 0x7ffffffffffffffd
#guard mulx 0x3 0xfedcba9876543210 0x2 0xfc962fc962fc9630
#guard mulx 0x3 0x0 0x0 0x0
#guard mulx 0xffffffffffffffff 0x123456789abcdef0 0x123456789abcdeef 0xedcba98765432110
#guard mulx 0xffffffffffffffff 0x26 0x25 0xffffffffffffffda
#guard mulx 0xffffffffffffffff 0x2 0x1 0xfffffffffffffffe
#guard mulx 0xffffffffffffffff 0x8000000000000000 0x7fffffffffffffff 0x8000000000000000
#guard mulx 0x8000000000000000 0x1 0x0 0x8000000000000000
#guard mulx 0x8000000000000000 0xffffffffffffffff 0x7fffffffffffffff 0x8000000000000000
#guard mulx 0x8000000000000000 0xfffffffffffffffe 0x7fffffffffffffff 0x0
#guard mulx 0x8000000000000000 0xdeadbeefcafebabe 0x6f56df77e57f5d5f 0x0
#guard mulx 0x7fffffffffffffff 0x7fffffffffffffff 0x3fffffffffffffff 0x1
#guard mulx 0x7fffffffffffffff 0xfedcba9876543210 0x7f6e5d4c3b2a1907 0x123456789abcdf0
#guard mulx 0x7fffffffffffffff 0x0 0x0 0x0
#guard mulx 0x7fffffffffffffff 0x3 0x1 0x7ffffffffffffffd
#guard mulx 0xfffffffffffffffe 0x26 0x25 0xffffffffffffffb4
#guard mulx 0xfffffffffffffffe 0x2 0x1 0xfffffffffffffffc
#guard mulx 0xfffffffffffffffe 0x8000000000000000 0x7fffffffffffffff 0x0
#guard mulx 0xfffffffffffffffe 0x123456789abcdef0 0x123456789abcdeef 0xdb97530eca864220
#guard mulx 0x123456789abcdef0 0xffffffffffffffff 0x123456789abcdeef 0xedcba98765432110
#guard mulx 0x123456789abcdef0 0xfffffffffffffffe 0x123456789abcdeef 0xdb97530eca864220
#guard mulx 0x123456789abcdef0 0xdeadbeefcafebabe 0xfd5bdeeeb2a01d7 0xeb689f4ea447d620
#guard mulx 0x123456789abcdef0 0x1 0x0 0x123456789abcdef0
#guard mulx 0xfedcba9876543210 0xfedcba9876543210 0xfdbac097c8dc5acc 0xdeec6cd7a44a4100
#guard mulx 0xfedcba9876543210 0x0 0x0 0x0
#guard mulx 0xfedcba9876543210 0x3 0x2 0xfc962fc962fc9630
#guard mulx 0xfedcba9876543210 0x7fffffffffffffff 0x7f6e5d4c3b2a1907 0x123456789abcdf0
#guard mulx 0xdeadbeefcafebabe 0x2 0x1 0xbd5b7ddf95fd757c
#guard mulx 0xdeadbeefcafebabe 0x8000000000000000 0x6f56df77e57f5d5f 0x0
#guard mulx 0xdeadbeefcafebabe 0x123456789abcdef0 0xfd5bdeeeb2a01d7 0xeb689f4ea447d620
#guard mulx 0xdeadbeefcafebabe 0x26 0x21 0xdca579821cfb834
#guard mulx 0x26 0xfffffffffffffffe 0x25 0xffffffffffffffb4
#guard mulx 0x26 0xdeadbeefcafebabe 0x21 0xdca579821cfb834
#guard mulx 0x26 0x1 0x0 0x26
#guard mulx 0x26 0xffffffffffffffff 0x25 0xffffffffffffffda

/-- `mulx r8, r8, rcx`: with both destinations the same, the high half. -/
def mulxSame (a b hi : BitVec 64) : Bool :=
  (exec (.mulx .r8 .r8 (.reg .rcx)) (s a b true false true false)).map (fun t => t.gpr .r8) ==
    some hi

#guard mulxSame 0x0 0x3 0x0
#guard mulxSame 0x2 0x8000000000000000 0x1
#guard mulxSame 0xffffffffffffffff 0xfffffffffffffffe 0xfffffffffffffffd
#guard mulxSame 0x7fffffffffffffff 0xfedcba9876543210 0x7f6e5d4c3b2a1907
#guard mulxSame 0x123456789abcdef0 0x26 0x2
#guard mulxSame 0xdeadbeefcafebabe 0x1 0x0

-- Only the destinations change; a source in memory; the source may be a
-- destination, read before it is written.
#guard (exec (.mulx .r8 .r9 (.reg .rcx)) (s 3 5 false false false false)).map
  (fun t => (t.gpr .rdx, t.gpr .rcx, t.gpr .rax, t.gpr .r10)) ==
    some (3, 5, 0xcccccccccccccccc, 0xcccccccccccccccc)
#guard (exec (.mulx .r8 .r9 (.mem { base := .rsi })) (s 0xdeadbeefcafebabe 0 false false false false)).map
  (fun t => (t.gpr .r8, t.gpr .r9)) == some (0xdeadbeefcafebabd, 0x2152411035014542)
#guard (exec (.mulx .rcx .r9 (.reg .rcx)) (s 0xdeadbeefcafebabe 0xffffffffffffffff false false false false)).map
  (fun t => (t.gpr .rcx, t.gpr .r9)) == some (0xdeadbeefcafebabd, 0x2152411035014542)
#guard (exec (.mulx .r8 .rdx (.reg .rcx)) (s 0xdeadbeefcafebabe 0xffffffffffffffff false false false false)).map
  (fun t => (t.gpr .r8, t.gpr .rdx)) == some (0xdeadbeefcafebabd, 0x2152411035014542)
-- An immediate source does not exist, and a memory source outside the
-- readable regions faults.
#guard (exec (.mulx .r8 .r9 (.imm 3)) (s 3 5 false false false false)).isNone
#guard (exec (.mulx .r8 .r9 (.mem { base := .rsi, disp := 8 })) (s 3 5 false false false false)).isNone

/-! ## `adcx` and `adox` -/

/-- `t` with `a` in `r8`. -/
def withR8 (a : BitVec 64) (t : State) : State :=
  { t with gpr := fun r => if r = .r8 then a else t.gpr r }

/-- `r8` and CF, OF, ZF and SF after `adcx r8, rcx` with `a` in `r8`, `b` in
`rcx` and the carry `c` in CF, and OF, ZF and SF preset to `!c`, `c`, `!c`. -/
def adcx (a b : BitVec 64) (c : Bool) :
    Option (BitVec 64 × Option Bool × Option Bool × Option Bool × Option Bool) :=
  (exec (.adcx .r8 (.reg .rcx)) (withR8 a (s 0 b c c (!c) (!c)))).map
    fun t => (t.gpr .r8, t.cf, t.of, t.zf, t.sf)

#guard adcx 0x0 0x3 false == some (0x3, some false, some true, some false, some true)
#guard adcx 0x0 0x3 true == some (0x4, some false, some false, some true, some false)
#guard adcx 0x1 0xdeadbeefcafebabe false == some (0xdeadbeefcafebabf, some false, some true, some false, some true)
#guard adcx 0x1 0xdeadbeefcafebabe true == some (0xdeadbeefcafebac0, some false, some false, some true, some false)
#guard adcx 0x2 0x8000000000000000 false == some (0x8000000000000002, some false, some true, some false, some true)
#guard adcx 0x2 0x8000000000000000 true == some (0x8000000000000003, some false, some false, some true, some false)
#guard adcx 0x3 0x0 false == some (0x3, some false, some true, some false, some true)
#guard adcx 0x3 0x0 true == some (0x4, some false, some false, some true, some false)
#guard adcx 0xffffffffffffffff 0xfffffffffffffffe false == some (0xfffffffffffffffd, some true, some true, some false, some true)
#guard adcx 0xffffffffffffffff 0xfffffffffffffffe true == some (0xfffffffffffffffe, some true, some false, some true, some false)
#guard adcx 0x8000000000000000 0x2 false == some (0x8000000000000002, some false, some true, some false, some true)
#guard adcx 0x8000000000000000 0x2 true == some (0x8000000000000003, some false, some false, some true, some false)
#guard adcx 0x7fffffffffffffff 0xfedcba9876543210 false == some (0x7edcba987654320f, some true, some true, some false, some true)
#guard adcx 0x7fffffffffffffff 0xfedcba9876543210 true == some (0x7edcba9876543210, some true, some false, some true, some false)
#guard adcx 0xfffffffffffffffe 0xffffffffffffffff false == some (0xfffffffffffffffd, some true, some true, some false, some true)
#guard adcx 0xfffffffffffffffe 0xffffffffffffffff true == some (0xfffffffffffffffe, some true, some false, some true, some false)
#guard adcx 0x123456789abcdef0 0x26 false == some (0x123456789abcdf16, some false, some true, some false, some true)
#guard adcx 0x123456789abcdef0 0x26 true == some (0x123456789abcdf17, some false, some false, some true, some false)
#guard adcx 0xfedcba9876543210 0x7fffffffffffffff false == some (0x7edcba987654320f, some true, some true, some false, some true)
#guard adcx 0xfedcba9876543210 0x7fffffffffffffff true == some (0x7edcba9876543210, some true, some false, some true, some false)
#guard adcx 0xdeadbeefcafebabe 0x1 false == some (0xdeadbeefcafebabf, some false, some true, some false, some true)
#guard adcx 0xdeadbeefcafebabe 0x1 true == some (0xdeadbeefcafebac0, some false, some false, some true, some false)
#guard adcx 0x26 0x123456789abcdef0 false == some (0x123456789abcdf16, some false, some true, some false, some true)
#guard adcx 0x26 0x123456789abcdef0 true == some (0x123456789abcdf17, some false, some false, some true, some false)

/-- `r8` and CF, OF, ZF and SF after `adox r8, rcx` with `a` in `r8`, `b` in
`rcx` and the carry `c` in OF, and CF, ZF and SF preset to `!c`, `c`, `!c`. -/
def adox (a b : BitVec 64) (c : Bool) :
    Option (BitVec 64 × Option Bool × Option Bool × Option Bool × Option Bool) :=
  (exec (.adox .r8 (.reg .rcx)) (withR8 a (s 0 b (!c) c (!c) c))).map
    fun t => (t.gpr .r8, t.cf, t.of, t.zf, t.sf)

#guard adox 0x0 0x3 false == some (0x3, some true, some false, some false, some true)
#guard adox 0x0 0x3 true == some (0x4, some false, some false, some true, some false)
#guard adox 0x1 0xdeadbeefcafebabe false == some (0xdeadbeefcafebabf, some true, some false, some false, some true)
#guard adox 0x1 0xdeadbeefcafebabe true == some (0xdeadbeefcafebac0, some false, some false, some true, some false)
#guard adox 0x2 0x8000000000000000 false == some (0x8000000000000002, some true, some false, some false, some true)
#guard adox 0x2 0x8000000000000000 true == some (0x8000000000000003, some false, some false, some true, some false)
#guard adox 0x3 0x0 false == some (0x3, some true, some false, some false, some true)
#guard adox 0x3 0x0 true == some (0x4, some false, some false, some true, some false)
#guard adox 0xffffffffffffffff 0xfffffffffffffffe false == some (0xfffffffffffffffd, some true, some true, some false, some true)
#guard adox 0xffffffffffffffff 0xfffffffffffffffe true == some (0xfffffffffffffffe, some false, some true, some true, some false)
#guard adox 0x8000000000000000 0x2 false == some (0x8000000000000002, some true, some false, some false, some true)
#guard adox 0x8000000000000000 0x2 true == some (0x8000000000000003, some false, some false, some true, some false)
#guard adox 0x7fffffffffffffff 0xfedcba9876543210 false == some (0x7edcba987654320f, some true, some true, some false, some true)
#guard adox 0x7fffffffffffffff 0xfedcba9876543210 true == some (0x7edcba9876543210, some false, some true, some true, some false)
#guard adox 0xfffffffffffffffe 0xffffffffffffffff false == some (0xfffffffffffffffd, some true, some true, some false, some true)
#guard adox 0xfffffffffffffffe 0xffffffffffffffff true == some (0xfffffffffffffffe, some false, some true, some true, some false)
#guard adox 0x123456789abcdef0 0x26 false == some (0x123456789abcdf16, some true, some false, some false, some true)
#guard adox 0x123456789abcdef0 0x26 true == some (0x123456789abcdf17, some false, some false, some true, some false)
#guard adox 0xfedcba9876543210 0x7fffffffffffffff false == some (0x7edcba987654320f, some true, some true, some false, some true)
#guard adox 0xfedcba9876543210 0x7fffffffffffffff true == some (0x7edcba9876543210, some false, some true, some true, some false)
#guard adox 0xdeadbeefcafebabe 0x1 false == some (0xdeadbeefcafebabf, some true, some false, some false, some true)
#guard adox 0xdeadbeefcafebabe 0x1 true == some (0xdeadbeefcafebac0, some false, some false, some true, some false)
#guard adox 0x26 0x123456789abcdef0 false == some (0x123456789abcdf16, some true, some false, some false, some true)
#guard adox 0x26 0x123456789abcdef0 true == some (0x123456789abcdf17, some false, some false, some true, some false)

-- A source in memory (all ones, with the carry in set: the sum wraps to
-- the destination, carrying out).
#guard (exec (.adcx .r8 (.mem { base := .rsi })) (withR8 0xdeadbeefcafebabe (s 0 0 true false false false))).map
  (fun t => (t.gpr .r8, t.cf)) == some (0xdeadbeefcafebabe, some true)
#guard (exec (.adox .r8 (.mem { base := .rsi })) (withR8 0xdeadbeefcafebabe (s 0 0 false false false true))).map
  (fun t => (t.gpr .r8, t.of)) == some (0xdeadbeefcafebabe, some true)
-- Only the destination changes.
#guard (exec (.adcx .r8 (.reg .rcx)) (s 3 5 false false false false)).map
  (fun t => (t.gpr .rdx, t.gpr .rcx, t.gpr .rax)) == some (3, 5, 0xcccccccccccccccc)
#guard (exec (.adox .r8 (.reg .rcx)) (s 3 5 false false false false)).map
  (fun t => (t.gpr .rdx, t.gpr .rcx, t.gpr .rax)) == some (3, 5, 0xcccccccccccccccc)
-- An undefined carry in faults (as for `adc`), and so do an immediate
-- source and a memory source outside the readable regions.
#guard (exec (.adcx .r8 (.reg .rcx)) { (s 3 5 false false false false) with cf := none }).isNone
#guard (exec (.adox .r8 (.reg .rcx)) { (s 3 5 false false false false) with of := none }).isNone
#guard (exec (.adcx .r8 (.reg .rcx)) { (s 3 5 false false false false) with of := none }).isSome
#guard (exec (.adox .r8 (.reg .rcx)) { (s 3 5 false false false false) with cf := none }).isSome
#guard (exec (.adcx .r8 (.imm 1)) (s 3 5 false false false false)).isNone
#guard (exec (.adox .r8 (.imm 1)) (s 3 5 false false false false)).isNone
#guard (exec (.adcx .r8 (.mem { base := .rsi, disp := 1 })) (s 3 5 false false false false)).isNone

/-! ## Printing -/

#guard printer.instr (.mulx .r9 .r8 (.reg .rcx)) == ["mulx r9, r8, rcx"]
#guard printer.instr (.mulx .rax .r15 (.mem { base := .rdi, disp := 24 })) ==
  ["mulx rax, r15, QWORD PTR [rdi+24]"]
#guard printer.instr (.adcx .r8 (.reg .rax)) == ["adcx r8, rax"]
#guard printer.instr (.adox .r13 (.mem { base := .rsi, disp := 8 })) ==
  ["adox r13, QWORD PTR [rsi+8]"]

-- Their CPU features (the SDM's "CPUID Feature Flag"); `mulx` writes `rsp`
-- if either destination is `rsp`, `adcx` and `adox` if theirs is.
#guard isa.requires (.mulx .rax .rbx (.reg .rcx)) == ["bmi2"]
#guard isa.requires (.adcx .rax (.reg .rbx)) == ["adx"]
#guard isa.requires (.adox .rax (.reg .rbx)) == ["adx"]
#guard isa.writesSp (.mulx .rsp .rax (.reg .rcx))
#guard isa.writesSp (.mulx .rax .rsp (.reg .rcx))
#guard !isa.writesSp (.mulx .rax .rbx (.reg .rsp))
#guard isa.writesSp (.adcx .rsp (.reg .rax))
#guard !isa.writesSp (.adox .rax (.reg .rsp))

end VG.Test.X86_64Adx
