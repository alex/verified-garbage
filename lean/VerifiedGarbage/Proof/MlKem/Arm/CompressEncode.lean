import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.Framework.Range

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_compress_encode`

A loop for each width `d`, over the output. A byte of several fields is built
in the output: its first field stored, each next one added (`addB`). The body
is symbolically executed once for any pointers (`body4_ok`, `body10_ok`; for
`d = 1`, each of the eight bits once for any bit, `bit_ok`). The values are
`compress_eq`, with the product in 32 bits (`cmpV_toNat`), and the bytes
`compressEncode1`, `compressEncode4` and `compressEncode10_0`–`_4`.
-/

namespace VG.Proof.MlKem.Arm.CompressEncode

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Add (ptr_succ reduced_zero)

/-! ## The values -/

/-- `(x · M + 2¹⁸ - 64) >> 19`, as `compressAt` computes it. -/
def cmpV (M x : BitVec 32) : BitVec 32 := (x * M + 0x40000 - 0x40) >>> 19

/-- The multipliers, as `movw` (and `movt`) build them. -/
def m1 : BitVec 32 := (315 : BitVec 16).setWidth 32
def m4 : BitVec 32 := (2520 : BitVec 16).setWidth 32
def m10 : BitVec 32 := (0x2 : BitVec 16) ++ ((0x75F7 : BitVec 16).setWidth 32).extractLsb' 0 16

theorem m1_toNat : m1.toNat = compressMul 1 := by decide
theorem m4_toNat : m4.toNat = compressMul 4 := by decide
theorem m10_toNat : m10.toNat = compressMul 10 := by decide

theorem cmpV_toNat {d : Nat} (hd : d ∈ compressWidths) {M : BitVec 32} (hM : M.toNat = compressMul d)
    (x : Zq) : (cmpV M (BitVec.ofNat 32 x.val)).toNat = (x.val * compressMul d + compressAdd) / 2 ^ 19 := by
  have hx := val_lt x
  have ha := compress_arg_lt hd x
  have hp : (BitVec.ofNat 32 x.val * M).toNat = x.val * compressMul d := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, hM, Nat.mod_eq_of_lt (a := x.val) (by omega)]
    exact Nat.mod_eq_of_lt (by unfold compressAdd at ha; omega)
  unfold compressAdd at ha ⊢
  unfold cmpV
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  refine congrArg (· / 2 ^ 19) ?_
  have e1 : (0x40000 : BitVec 32).toNat = 262144 := rfl
  have e2 : (0x40 : BitVec 32).toNat = 64 := rfl
  rw [BitVec.toNat_sub, BitVec.toNat_add, hp, e1, e2]
  omega

/-! ## The loop bodies -/

/-- A byte `p` of the output, loaded, with `v` added, and stored back. -/
def addB (p : Byte) (v : BitVec 32) : Byte := (p.setWidth 32 + v).setWidth 8

section
variable {s : State} {x y c : BitVec 32}

/-- The start of a byte of `ByteEncode₁(Compress₁)`: 0. -/
def head1 : List Instr := [.mov .r12 (.imm 0), .strb .r12 .r2 0]

/-- The end of an iteration of the loop for `d = 1`. -/
def tail1 : List Instr := [.dp .add .r0 .r0 (.imm 32), .dp .add .r2 .r2 (.imm 1), .subs .r3 .r3 (.imm 1)]

theorem ce1Body_eq : ce1Body = head1 ++ (List.range 8).flatMap ce1Bit ++ tail1 := rfl

theorem head1_ok (o : InRegions s.wr (State.addr (s.gpr .r2 + BitVec.ofNat 32 0)) 1) :
    WP isa (.block head1) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r2 = s.gpr .r2 ∧ s'.gpr .r3 = s.gpr .r3 ∧
      s'.mem = s.mem.writeW (State.addr (s.gpr .r2 + BitVec.ofNat 32 0)) ((0 : BitVec 32).setWidth 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [head1, o, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

theorem bit_ok {j : Nat} (hj : j < 8) (h0 : s.gpr .r0 = x) (h2 : s.gpr .r2 = y)
    (i0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (4 * j))) 4)
    (ib : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 1)
    (ob : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 1) :
    WP isa (.block (ce1Bit j)) s fun s' =>
      s'.gpr .r0 = x ∧ s'.gpr .r2 = y ∧ s'.gpr .r3 = s.gpr .r3 ∧
      s'.mem = s.mem.writeW (State.addr (y + BitVec.ofNat 32 0)) (addB (s.mem (State.addr (y + BitVec.ofNat 32 0)))
        ((cmpV m1 (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * j))) 32) <<< 31) >>> (31 - j))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  have hsh : 1 ≤ 31 - j ∧ 31 - j ≤ 31 := by omega
  have ho : 4 * j < 4096 := by omega
  run_block [ce1Bit, compressAt, cmpV, m1, addB, h0, h2, i0, ib, ob, hsh, ho, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

theorem tail1_ok (h0 : s.gpr .r0 = x) (h2 : s.gpr .r2 = y) (h3 : s.gpr .r3 = c) :
    WP isa (.block tail1) s fun s' =>
      s'.gpr .r0 = x + 32 ∧ s'.gpr .r2 = y + 1 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [tail1, h0, h2, h3, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

theorem body4_ok (h0 : s.gpr .r0 = x) (h2 : s.gpr .r2 = y) (h3 : s.gpr .r3 = c)
    (i0 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
    (i1 : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 4)) 4)
    (ib : InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 0)) 1)
    (ob : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 1)
    (hsep : ∀ (m : Mem) (v : Byte),
      (m.writeW (State.addr (y + BitVec.ofNat 32 0)) v).readW (State.addr (x + BitVec.ofNat 32 4)) 32 =
        m.readW (State.addr (x + BitVec.ofNat 32 4)) 32) :
    WP isa (.block ce4Body) s fun s' =>
      s'.gpr .r0 = x + 8 ∧ s'.gpr .r2 = y + 1 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = (s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
          (((cmpV m4 (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32) <<< 28) >>> 28).setWidth 8)).writeW
        (State.addr (y + BitVec.ofNat 32 0))
        (addB (((cmpV m4 (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32) <<< 28) >>> 28).setWidth 8)
          ((cmpV m4 (s.mem.readW (State.addr (x + BitVec.ofNat 32 4)) 32) <<< 28) >>> 24)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [ce4Body, compressAt, cmpV, m4, addB, writeW8_apply, h0, h2, h3, i0, i1, ib, ob, hsep, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

/-- `Compress₁₀` of a coefficient, as `ce10Coeff` computes it. -/
def c10 (x : BitVec 32) : BitVec 32 := (cmpV m10 x <<< 22) >>> 22

theorem body10_ok (h0 : s.gpr .r0 = x) (h2 : s.gpr .r2 = y) (h3 : s.gpr .r3 = c)
    (ic : ∀ k < 4, InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (4 * k))) 4)
    (ib : ∀ k < 5, InRegions (s.rd ++ s.wr) (State.addr (y + BitVec.ofNat 32 k)) 1)
    (o : ∀ k < 5, InRegions s.wr (State.addr (y + BitVec.ofNat 32 k)) 1)
    (hsep : ∀ (m : Mem) (o : Nat) (v : Byte) (k : Nat), o < 5 → k < 4 →
      (m.writeW (State.addr (y + BitVec.ofNat 32 o)) v).readW (State.addr (x + BitVec.ofNat 32 (4 * k))) 32 =
        m.readW (State.addr (x + BitVec.ofNat 32 (4 * k))) 32) :
    WP isa (.block ce10Body) s fun s' =>
      s'.gpr .r0 = x + 16 ∧ s'.gpr .r2 = y + 5 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = (((((((s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
          ((c10 (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * 0))) 32)).setWidth 8)).writeW
        (State.addr (y + BitVec.ofNat 32 1))
          ((c10 (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * 0))) 32) >>> 8).setWidth 8)).writeW
        (State.addr (y + BitVec.ofNat 32 1))
          (addB ((c10 (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * 0))) 32) >>> 8).setWidth 8)
            (c10 (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * 1))) 32) <<< (2 * 1)))).writeW
        (State.addr (y + BitVec.ofNat 32 (1 + 1)))
          ((c10 (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * 1))) 32) >>> (8 - 2 * 1)).setWidth 8)).writeW
        (State.addr (y + BitVec.ofNat 32 2))
          (addB ((c10 (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * 1))) 32) >>> (8 - 2 * 1)).setWidth 8)
            (c10 (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * 2))) 32) <<< (2 * 2)))).writeW
        (State.addr (y + BitVec.ofNat 32 (2 + 1)))
          ((c10 (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * 2))) 32) >>> (8 - 2 * 2)).setWidth 8)).writeW
        (State.addr (y + BitVec.ofNat 32 3))
          (addB ((c10 (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * 2))) 32) >>> (8 - 2 * 2)).setWidth 8)
            (c10 (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * 3))) 32) <<< (2 * 3)))).writeW
        (State.addr (y + BitVec.ofNat 32 (3 + 1)))
          ((c10 (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * 3))) 32) >>> (8 - 2 * 3)).setWidth 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  have i0 := ic 0 (by omega)
  have i1 := ic 1 (by omega)
  have i2 := ic 2 (by omega)
  have i3 := ic 3 (by omega)
  have b1 := ib 1 (by omega)
  have b2 := ib 2 (by omega)
  have b3 := ib 3 (by omega)
  have o0 := o 0 (by omega)
  have o1 := o 1 (by omega)
  have o2 := o 2 (by omega)
  have o3 := o 3 (by omega)
  have o4 := o 4 (by omega)
  run_block [ce10Body, ce10Coeff, ce10Mid, compressAt, c10, cmpV, m10, addB, writeW8_apply, h0, h2, h3,
    i0, i1, i2, i3, b1, b2, b3, o0, o1, o2, o3, o4, hsep, preserved, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

/-! ## Arithmetic -/

theorem addB_toNat (p : Byte) (v : BitVec 32) : (addB p v).toNat = (p.toNat + v.toNat) % 256 := by
  have := p.isLt
  unfold addB
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, setWidth32_toNat]
  omega

theorem byte_eq {b : Byte} {n : Nat} (h : b.toNat = n % 256) : b = BitVec.ofNat 8 n :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat])

theorem bitAt_toNat (w : BitVec 32) {j : Nat} (hj : j < 8) :
    ((w <<< 31) >>> (31 - j)).toNat = w.toNat % 2 * 2 ^ j := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    show 2 ^ 32 = 2 * 2 ^ 31 from rfl, Nat.mul_mod_mul_right,
    show 2 ^ 31 = 2 ^ j * 2 ^ (31 - j) by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)], ← Nat.mul_assoc,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem nib0_toNat (w : BitVec 32) : ((w <<< 28) >>> 28).toNat = w.toNat % 16 := by bv_omega

theorem nib1_toNat (w : BitVec 32) : ((w <<< 28) >>> 24).toNat = w.toNat % 16 * 16 := by bv_omega

theorem c10_toNat (w : BitVec 32) : c10 w = BitVec.ofNat 32 ((cmpV m10 w).toNat % 1024) := by
  unfold c10; bv_omega

/-- A compressed coefficient, from its word. -/
theorem compress_w {d : Nat} (hd : d ∈ compressWidths) {M : BitVec 32} (hM : M.toNat = compressMul d)
    (x : Zq) : compress d x = (cmpV M (BitVec.ofNat 32 x.val)).toNat % 2 ^ d := by
  rw [compress_eq hd, cmpV_toNat hd hM]

/-! ## The loops -/

section
variable (s₀ : State)

abbrev pf : BitVec 32 := s₀.gpr .r0
abbrev dd : Nat := (s₀.gpr .r1).toNat
abbrev po : BitVec 32 := s₀.gpr .r2
abbrev len : Nat := (s₀.gpr .r3).toNat
abbrev F : Addr := State.addr (pf s₀)
abbrev O : Addr := State.addr (po s₀)
abbrev outR : Region := ⟨O s₀, len s₀⟩
abbrev fp : Poly := polyAt s₀.mem (F s₀)
abbrev CE : List Byte := compressEncode (dd s₀) (fp s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (F s₀)]
  wr : s₀.wr = [outR s₀]
  disj : (polyRegion (F s₀)).Disjoint (outR s₀)
  fitF : (pf s₀).toNat + 1024 ≤ 2 ^ 32
  fitO : (po s₀).toNat + len s₀ ≤ 2 ^ 32
  d : dd s₀ ∈ compressWidths
  len : len s₀ = 32 * dd s₀
  red : Reduced s₀.mem (F s₀)

/-- After `i` iterations of the loop that reads `T` bytes of coefficients
and writes `S` bytes each time. -/
structure Inv (S T N : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pf s₀ + BitVec.ofNat 32 (T * i)
  r2 : s.gpr .r2 = po s₀ + BitVec.ofNat 32 (S * i)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (N - i))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [outR s₀] s₀.mem s.mem
  bytes : ∀ k < len s₀, s.mem (O s₀ + BitVec.ofNat 64 k) =
    if k < S * i then (CE s₀)[k]! else s₀.mem (O s₀ + BitVec.ofNat 64 k)

section
variable {s₀ : State} (hp : Pre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
  (hf : Frame [outR s₀] s₀.mem s.mem)
include hp hrd hwr hf

/-- Coefficient `j = K i + k` of the input: its address, that it can be
read, and its value. -/
theorem coeff_at {T K i k : Nat} (hT : T = 4 * K) (hk : K * i + k < 256) :
    State.addr (pf s₀ + BitVec.ofNat 32 (T * i) + BitVec.ofNat 32 (4 * k)) = coeffAddr (F s₀) (K * i + k) ∧
    InRegions (s.rd ++ s.wr) (coeffAddr (F s₀) (K * i + k)) 4 ∧
    s.mem.readW (coeffAddr (F s₀) (K * i + k)) 32 = BitVec.ofNat 32 ((fp s₀)[K * i + k]!).val := by
  have fF := hp.fitF
  have c := coeff_contains (F s₀) (i := K * i + k) (by rw [n_eq]; omega)
  refine ⟨addr_coeff fF (by subst hT; rw [Nat.mul_assoc, ← Nat.mul_add]) (by omega), ?_, ?_⟩
  · rw [hrd, hwr, hp.rd, hp.wr]; exact inRegions_of (by simp) c
  · show coeffAt s.mem (F s₀) (K * i + k) = _
    rw [frame_coeff hf (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.disj)
      (by rw [n_eq]; omega)]
    exact ofNat_val_eq (polyAt_val hp.red (by rw [n_eq]; omega)).symm

omit hf in
/-- Byte `S i + k` of the output: its address, and that it can be read and written. -/
theorem byte_at {S i k : Nat} (hk : S * i + k < len s₀) :
    State.addr (po s₀ + BitVec.ofNat 32 (S * i) + BitVec.ofNat 32 k) = O s₀ + BitVec.ofNat 64 (S * i + k) ∧
    InRegions s.wr (O s₀ + BitVec.ofNat 64 (S * i + k)) 1 ∧
    InRegions (s.rd ++ s.wr) (O s₀ + BitVec.ofNat 64 (S * i + k)) 1 ∧
    (outR s₀).Contains (O s₀ + BitVec.ofNat 64 (S * i + k)) 1 := by
  have fO := hp.fitO
  have c : (outR s₀).Contains (O s₀ + BitVec.ofNat 64 (S * i + k)) 1 := contains_off (by omega) (by omega)
  exact ⟨addr_byte fO rfl hk, by rw [hwr, hp.wr]; exact inRegions_of (by simp) c,
    by rw [hrd, hwr, hp.rd, hp.wr]; exact inRegions_of (by simp) c, c⟩

end

/-- A store to the output leaves the input. -/
theorem sep_at {s₀ : State} (hp : Pre s₀) {S T K i o k : Nat} (hT : T = 4 * K) (ho : S * i + o < len s₀)
    (hk : K * i + k < 256) (m : Mem) (v : Byte) :
    (m.writeW (State.addr (po s₀ + BitVec.ofNat 32 (S * i) + BitVec.ofNat 32 o)) v).readW
      (State.addr (pf s₀ + BitVec.ofNat 32 (T * i) + BitVec.ofNat 32 (4 * k))) 32 =
    m.readW (State.addr (pf s₀ + BitVec.ofNat 32 (T * i) + BitVec.ofNat 32 (4 * k))) 32 := by
  have fO := hp.fitO
  have fF := hp.fitF
  rw [addr_byte fO rfl ho, addr_coeff fF (by subst hT; rw [Nat.mul_assoc, ← Nat.mul_add]) hk]
  exact readW_writeW_disj hp.disj v (contains_off (by omega) (by omega)) (coeff_contains _ (by rw [n_eq]; omega))

/-- The whole loop, from its steps. -/
theorem loop_of {s₀ : State} {S T N : Nat} {body : List Instr} (hN : 0 < N) (hSN : S * N = len s₀)
    (hlen : (CE s₀).length = len s₀)
    (hstep : ∀ i < N, ∀ s, Inv S T N s₀ i s →
      WP isa (.block body) s fun s' => Inv S T N s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = N))
    {s₁ : State} (g0 : s₁.gpr .r0 = s₀.gpr .r0) (g2 : s₁.gpr .r2 = s₀.gpr .r2)
    (g3 : s₁.gpr .r3 = BitVec.ofNat 32 (1 * N)) (gp : ∀ r ∈ preserved, s₁.gpr r = s₀.gpr r)
    (m : s₁.mem = s₀.mem) (rd : s₁.rd = s₀.rd) (wr : s₁.wr = s₀.wr) (sp : s₁.sp = s₀.sp) :
    WP isa (.loop (.block body) .ne) s₁ fun s =>
      (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ bytesAt s.mem (O s₀) (len s₀) = CE s₀ := by
  refine wp_loop_ne (Inv S T N s₀) hN hstep (fun s h => ⟨h.pres, h.sp,
    bytesAt_eq! hlen fun k hk => by rw [h.bytes k hk, ite_eq_left (by rw [hSN]; exact hk)]⟩) ?_
  refine ⟨by rw [g0]; simp, by rw [g2]; simp, by rw [g3, Nat.sub_zero], rd, wr, sp, gp,
    by rw [m]; exact Frame.refl _ _, fun k _ => by rw [m, Nat.mul_zero, ite_eq_right (Nat.not_lt_zero _)]⟩

/-! ## Each width -/

theorem step4 {s₀ : State} (hp : Pre s₀) (hd : dd s₀ = 4) {i : Nat} (hi : i < 128) {s : State}
    (h : Inv 1 8 128 s₀ i s) :
    WP isa (.block ce4Body) s fun s' => Inv 1 8 128 s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 128) := by
  have hl : len s₀ = 128 := by rw [hp.len, hd]
  obtain ⟨e0, i0, v0⟩ := coeff_at hp h.rd h.wr h.frame (T := 8) (K := 2) (i := i) (k := 0) rfl (by omega)
  obtain ⟨e1, i1, v1⟩ := coeff_at hp h.rd h.wr h.frame (T := 8) (K := 2) (i := i) (k := 1) rfl (by omega)
  obtain ⟨eo, oo, io, co⟩ := byte_at hp h.rd h.wr (S := 1) (i := i) (k := 0) (by omega)
  rw [Nat.add_zero] at e0 i0 v0 eo oo io co
  have c0 := compress_w (d := 4) (by decide) m4_toNat (fp s₀)[2 * i]!
  have c1 := compress_w (d := 4) (by decide) m4_toNat (fp s₀)[2 * i + 1]!
  have l0 := compress_lt 4 (fp s₀)[2 * i]!
  have l1 := compress_lt 4 (fp s₀)[2 * i + 1]!
  simp only [Nat.reducePow] at c0 c1 l0 l1
  refine WP.mono (body4_ok h.r0 h.r2 h.r3 (by rw [e0]; exact i0) (by rw [e1]; exact i1)
    (by rw [eo]; exact io) (by rw [eo]; exact oo)
    (fun m v => sep_at hp (S := 1) (T := 8) (K := 2) (i := i) (o := 0) (k := 1) rfl (by omega) (by omega) m v))
    fun s' ⟨r0, r2, r3, z, m, rd, wr, sp, pres⟩ => ?_
  rw [e0, e1, v0, v1, eo, writeW8_writeW8] at m
  refine ⟨⟨?_, ?_, ?_, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
    fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 8 i
  · rw [r2]; exact ptr_succ _ 1 i
  · rw [r3]; exact count_sub (k := 1) hi
  · rw [m]; exact h.frame.writeW (List.mem_singleton_self _) _ co
  · rw [m]
    refine byte_one (a := 1 * i) (by omega) (by omega) h.bytes ?_
    rw [Nat.one_mul, CE, hd, compressEncode4 _ hi]
    refine byte_eq ?_
    rw [addB_toNat, setWidth8, BitVec.toNat_ofNat, nib0_toNat, nib1_toNat, ← c0, ← c1]
    omega
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

theorem step10 {s₀ : State} (hp : Pre s₀) (hd : dd s₀ = 10) {i : Nat} (hi : i < 64) {s : State}
    (h : Inv 5 16 64 s₀ i s) :
    WP isa (.block ce10Body) s fun s' => Inv 5 16 64 s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 64) := by
  have hl : len s₀ = 320 := by rw [hp.len, hd]
  have cat : ∀ k < 4, _ := fun k (hk : k < 4) =>
    coeff_at hp h.rd h.wr h.frame (T := 16) (K := 4) (i := i) (k := k) rfl (by omega)
  have bat : ∀ k < 5, _ := fun k (hk : k < 5) => byte_at hp h.rd h.wr (S := 5) (i := i) (k := k) (by omega)
  -- The compressed coefficients.
  let cc : Nat → BitVec 32 := fun k => BitVec.ofNat 32 (compress 10 (fp s₀)[4 * i + k]!)
  have ccl : ∀ k, compress 10 (fp s₀)[4 * i + k]! < 1024 := fun k => compress_lt 10 _
  have cct : ∀ k, (cc k).toNat = compress 10 (fp s₀)[4 * i + k]! := fun k => by
    show (BitVec.ofNat 32 _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := ccl k; omega)]
  have hc : ∀ k < 4, c10 (s.mem.readW (State.addr (pf s₀ + BitVec.ofNat 32 (16 * i) +
      BitVec.ofNat 32 (4 * k))) 32) = cc k := fun k hk => by
    rw [(cat k hk).1, (cat k hk).2.2, c10_toNat, ← compress_w (d := 10) (by decide) m10_toNat]
  refine WP.mono (body10_ok h.r0 h.r2 h.r3 (fun k hk => by rw [(cat k hk).1]; exact (cat k hk).2.1)
    (fun k hk => by rw [(bat k hk).1]; exact (bat k hk).2.2.1)
    (fun k hk => by rw [(bat k hk).1]; exact (bat k hk).2.1)
    (fun m o v k ho hk => sep_at hp (S := 5) (T := 16) (K := 4) (i := i) rfl (by omega) (by omega) m v))
    fun s' ⟨r0, r2, r3, z, m, rd, wr, sp, pres⟩ => ?_
  rw [hc 0 (by omega), hc 1 (by omega), hc 2 (by omega), hc 3 (by omega), (bat 0 (by omega)).1,
    (bat 1 (by omega)).1, (bat 2 (by omega)).1, (bat 3 (by omega)).1, (bat 4 (by omega)).1,
    writeW8_writeW8, writeW8_writeW8, writeW8_writeW8] at m
  refine ⟨⟨?_, ?_, ?_, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
    fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 16 i
  · rw [r2]; exact ptr_succ _ 5 i
  · rw [r3]; exact count_sub (k := 1) hi
  · rw [m]
    exact ((((h.frame.writeW (List.mem_singleton_self _) _ (bat 0 (by omega)).2.2.2).writeW
      (List.mem_singleton_self _) _ (bat 1 (by omega)).2.2.2).writeW
      (List.mem_singleton_self _) _ (bat 2 (by omega)).2.2.2).writeW
      (List.mem_singleton_self _) _ (bat 3 (by omega)).2.2.2).writeW
      (List.mem_singleton_self _) _ (bat 4 (by omega)).2.2.2
  · rw [m]
    have t0 := cct 0; have t1 := cct 1; have t2 := cct 2; have t3 := cct 3
    have l0 := ccl 0; have l1 := ccl 1; have l2 := ccl 2; have l3 := ccl 3
    rw [Nat.add_zero] at t0 l0
    have e0 : (cc 0).setWidth 8 = (CE s₀)[5 * i]! := by
      rw [CE, hd, compressEncode10_0 _ hi, setWidth8, t0]; exact ofNat8_eq (by omega)
    have e1 : addB ((cc 0 >>> 8).setWidth 8) (cc 1 <<< (2 * 1)) = (CE s₀)[5 * i + 1]! := by
      rw [CE, hd, compressEncode10_1 _ hi]
      refine byte_eq ?_
      rw [addB_toNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, t0, t1,
        Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.add_zero]
      omega
    have e2 : addB ((cc 1 >>> (8 - 2 * 1)).setWidth 8) (cc 2 <<< (2 * 2)) = (CE s₀)[5 * i + 2]! := by
      rw [CE, hd, compressEncode10_2 _ hi]
      refine byte_eq ?_
      rw [addB_toNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, t1, t2,
        Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
      omega
    have e3 : addB ((cc 2 >>> (8 - 2 * 2)).setWidth 8) (cc 3 <<< (2 * 3)) = (CE s₀)[5 * i + 3]! := by
      rw [CE, hd, compressEncode10_3 _ hi]
      refine byte_eq ?_
      rw [addB_toNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, t2, t3,
        Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
      omega
    have e4 : (cc 3 >>> (8 - 2 * 3)).setWidth 8 = (CE s₀)[5 * i + 4]! := by
      rw [CE, hd, compressEncode10_4 _ hi]
      refine byte_eq ?_
      rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, t3, Nat.shiftRight_eq_div_pow]
    exact byte_one (a := 5 * i + 4) (by omega) (by omega) (byte_one (a := 5 * i + 3) (by omega) (by omega)
      (byte_one (a := 5 * i + 2) (by omega) (by omega) (byte_one (a := 5 * i + 1) (by omega) (by omega)
      (byte_one (a := 5 * i + 0) (by omega) (by omega) h.bytes e0) e1) e2) e3) e4
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

/-- The bits of output byte `i` of `ByteEncode₁(Compress₁)` from its first `a` coefficients. -/
def acc1N (s₀ : State) (i : Nat) : Nat → Nat
  | 0 => 0
  | a + 1 => acc1N s₀ i a + compress 1 (fp s₀)[8 * i + a]! * 2 ^ a

theorem acc1N_lt (s₀ : State) (i : Nat) : ∀ a, acc1N s₀ i a < 2 ^ a
  | 0 => by simp [acc1N]
  | a + 1 => by
    have := acc1N_lt s₀ i a
    have h := compress_lt 1 (fp s₀)[8 * i + a]!
    have : compress 1 (fp s₀)[8 * i + a]! * 2 ^ a ≤ 2 ^ a := by
      have : compress 1 (fp s₀)[8 * i + a]! ≤ 1 := by simp only [Nat.pow_one] at h; omega
      simpa using Nat.mul_le_mul_right (2 ^ a) this
    rw [acc1N, Nat.pow_succ]
    omega

theorem acc1N_eight (s₀ : State) (i : Nat) :
    acc1N s₀ i 8 = compress 1 (fp s₀)[8 * i]! + 2 * compress 1 (fp s₀)[8 * i + 1]! +
      4 * compress 1 (fp s₀)[8 * i + 2]! + 8 * compress 1 (fp s₀)[8 * i + 3]! +
      16 * compress 1 (fp s₀)[8 * i + 4]! + 32 * compress 1 (fp s₀)[8 * i + 5]! +
      64 * compress 1 (fp s₀)[8 * i + 6]! + 128 * compress 1 (fp s₀)[8 * i + 7]! := by
  rw [acc1N, acc1N, acc1N, acc1N, acc1N, acc1N, acc1N, acc1N, acc1N]
  simp only [Nat.add_zero, Nat.reducePow]
  omega

/-- Within an iteration of the loop for `d = 1`, after the first `a` bits
of the byte. -/
structure Mid (s₀ : State) (i a : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pf s₀ + BitVec.ofNat 32 (32 * i)
  r2 : s.gpr .r2 = po s₀ + BitVec.ofNat 32 (1 * i)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (32 - i))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [outR s₀] s₀.mem s.mem
  bytes : ∀ k < len s₀, s.mem (O s₀ + BitVec.ofNat 64 k) =
    if k < 1 * i + 1 then (if k < 1 * i then (CE s₀)[k]! else BitVec.ofNat 8 (acc1N s₀ i a))
    else s₀.mem (O s₀ + BitVec.ofNat 64 k)

theorem bit_step {s₀ : State} (hp : Pre s₀) (hd : dd s₀ = 1) {i : Nat} (hi : i < 32) {a : Nat}
    (ha : a < 8) {s : State} (h : Mid s₀ i a s) : WP isa (.block (ce1Bit a)) s (Mid s₀ i (a + 1)) := by
  have hl : len s₀ = 32 := by rw [hp.len, hd]
  obtain ⟨e, ic, v⟩ := coeff_at hp h.rd h.wr h.frame (T := 32) (K := 8) (i := i) (k := a) rfl (by omega)
  obtain ⟨eo, oo, io, co⟩ := byte_at hp h.rd h.wr (S := 1) (i := i) (k := 0) (by omega)
  rw [Nat.add_zero] at eo oo io co
  have c := compress_w (d := 1) (by decide) m1_toNat (fp s₀)[8 * i + a]!
  have lc := compress_lt 1 (fp s₀)[8 * i + a]!
  have lt := acc1N_lt s₀ i a
  have ha' : 2 ^ a ≤ 128 := Nat.pow_le_pow_right (by decide) (by omega : a ≤ 7)
  have hc1 : compress 1 (fp s₀)[8 * i + a]! * 2 ^ a ≤ 2 ^ a := by
    have : compress 1 (fp s₀)[8 * i + a]! ≤ 1 := by simp only [Nat.pow_one] at lc; omega
    simpa using Nat.mul_le_mul_right (2 ^ a) this
  have rb : s.mem (O s₀ + BitVec.ofNat 64 (1 * i)) = BitVec.ofNat 8 (acc1N s₀ i a) := by
    rw [h.bytes _ (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
  refine WP.mono (bit_ok ha h.r0 h.r2 (by rw [e]; exact ic) (by rw [eo]; exact io) (by rw [eo]; exact oo))
    fun s' ⟨r0, r2, r3, m, rd, wr, sp, pres⟩ => ⟨r0, r2, r3.trans h.r3, rd.trans h.rd, wr.trans h.wr,
      sp.trans h.sp, fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩
  · rw [m, eo]; exact h.frame.writeW (List.mem_singleton_self _) _ co
  · have nv : addB (s.mem (O s₀ + BitVec.ofNat 64 (1 * i)))
        ((cmpV m1 (BitVec.ofNat 32 ((fp s₀)[8 * i + a]!).val) <<< 31) >>> (31 - a)) =
        BitVec.ofNat 8 (acc1N s₀ i (a + 1)) := by
      rw [rb]
      refine byte_eq ?_
      rw [addB_toNat, bitAt_toNat _ ha, ← c, BitVec.toNat_ofNat, acc1N]
      omega
    intro k hk
    rw [m, e, v, eo, nv, byte_writeW8 _ _ (by omega) (by omega), h.bytes k hk]
    rcases (by omega : k < 1 * i ∨ k = 1 * i ∨ 1 * i < k) with h' | rfl | h' <;> resolve_ifs

theorem step1 {s₀ : State} (hp : Pre s₀) (hd : dd s₀ = 1) {i : Nat} (hi : i < 32) {s : State}
    (h : Inv 1 32 32 s₀ i s) :
    WP isa (.block ce1Body) s fun s' => Inv 1 32 32 s₀ (i + 1) s' ∧ s'.z = decide (i + 1 = 32) := by
  have hl : len s₀ = 32 := by rw [hp.len, hd]
  rw [ce1Body_eq, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨eo, oo, io, co⟩ := byte_at hp h.rd h.wr (S := 1) (i := i) (k := 0) (by omega)
  rw [Nat.add_zero] at eo oo io co
  refine WP.mono (head1_ok (by rw [h.r2, eo]; exact oo)) fun s₁ ⟨g0, g2, g3, m, rd, wr, sp, pres⟩ => ?_
  have h0 : Mid s₀ i 0 s₁ := by
    refine ⟨g0.trans h.r0, g2.trans h.r2, g3.trans h.r3, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp,
      fun r hr => (pres r hr).trans (h.pres r hr), ?_, fun k hk => ?_⟩
    · rw [m, h.r2, eo]; exact h.frame.writeW (List.mem_singleton_self _) _ co
    · rw [m, h.r2, eo, byte_writeW8 _ _ (by omega) (by omega), h.bytes k hk]
      rcases (by omega : k < 1 * i ∨ k = 1 * i ∨ 1 * i < k) with h' | rfl | h'
      · resolve_ifs
      · resolve_ifs; rfl
      · resolve_ifs
  refine WP.mono (wp_range_flatMap (M := isa) (f := ce1Bit) (N := 8) (Mid s₀ i)
    (fun a s ha hs => bit_step hp hd hi ha hs) 8 (Nat.le_refl _) s₁ h0) fun s₂ h₂ => ?_
  refine WP.mono (tail1_ok h₂.r0 h₂.r2 h₂.r3) fun s' ⟨r0, r2, r3, z, m', rd', wr', sp', pres'⟩ =>
    ⟨⟨?_, ?_, ?_, rd'.trans h₂.rd, wr'.trans h₂.wr, sp'.trans h₂.sp,
      fun r hr => (pres' r hr).trans (h₂.pres r hr), m' ▸ h₂.frame, ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 32 i
  · rw [r2]; exact ptr_succ _ 1 i
  · rw [r3]; exact count_sub (k := 1) hi
  · intro k hk
    rw [m', h₂.bytes k hk]
    have ev : BitVec.ofNat 8 (acc1N s₀ i 8) = (CE s₀)[1 * i]! := by
      rw [Nat.one_mul, CE, hd, compressEncode1 _ hi, acc1N_eight]
    rcases (by omega : k < 1 * i ∨ k = 1 * i ∨ 1 * i < k) with h' | rfl | h'
    · resolve_ifs
    · resolve_ifs; exact ev
    · resolve_ifs
  · rw [z]; exact count_z (k := 1) hi (by decide) (by decide)

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compressEncode s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      bytesAt s.mem (O s₀) (len s₀) = CE s₀ := by
  have hd := mem_compressWidths hp.d
  have hlen : (CE s₀).length = len s₀ := by rw [compressEncode_length, hp.len]
  have gp : ∀ (s : State) (v : BitVec 32), (∀ r ∈ preserved, s.gpr r = s₀.gpr r) →
      ∀ r ∈ preserved, (s.setReg .r3 v).gpr r = s₀.gpr r := fun s v h r hr => by
    simp only [State.setReg]
    rw [ite_eq_right (by intro e; subst e; simp [preserved] at hr)]
    exact h r hr
  unfold Impl.MlKem.Arm.compressEncode
  refine WP.seq (WP.of_runBlock ⟨_, runBlock_cons.trans (by rfl), ?_⟩)
  refine WP.ite (decide (dd s₀ = 1)) (by
    show some (s₀.gpr .r1 - BitVec.ofNat 32 1 == 0) = _
    rw [cmp_z _ _ (by decide)]) (fun e => ?_) (fun e => ?_)
  · have e1 := of_decide_eq_true e
    refine WP.seq (WP.of_runBlock ⟨_, runBlock_cons.trans (by rfl), ?_⟩)
    exact loop_of (N := 32) (by decide) (by rw [hp.len, e1]) hlen
      (fun i hi s h => step1 hp e1 hi h) rfl rfl (by rfl) (gp _ _ fun _ _ => rfl) rfl rfl rfl rfl
  · have e1 : dd s₀ ≠ 1 := of_decide_eq_false e
    refine WP.seq (WP.of_runBlock ⟨_, runBlock_cons.trans (by rfl), ?_⟩)
    refine WP.ite (decide (dd s₀ = 4)) (by
      show some (s₀.gpr .r1 - BitVec.ofNat 32 4 == 0) = _
      rw [cmp_z _ _ (by decide)]) (fun e => ?_) (fun e => ?_)
    · have e4 := of_decide_eq_true e
      refine WP.seq (WP.of_runBlock ⟨_, runBlock_cons.trans (by rfl), ?_⟩)
      exact loop_of (N := 128) (by decide) (by rw [hp.len, e4]) hlen
        (fun i hi s h => step4 hp e4 hi h) rfl rfl (by rfl) (gp _ _ fun _ _ => rfl) rfl rfl rfl rfl
    · have e10 : dd s₀ = 10 := by have := of_decide_eq_false e; omega
      refine WP.seq (WP.of_runBlock ⟨_, runBlock_cons.trans (by rfl), ?_⟩)
      exact loop_of (N := 64) (by decide) (by rw [hp.len, e10]) hlen
        (fun i hi s h => step10 hp e10 hi h) rfl rfl (by rfl) (gp _ _ fun _ _ => rfl) rfl rfl rfl rfl

theorem pre_of {s : State} (h : (Spec.MlKem.compressEncodeContract Arm.abi).pre s) : Pre s := by
  sig_pre [Spec.MlKem.compressEncodeContract, Spec.MlKem.compressEncodeSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x2000 | .r3 => 32 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 32⟩]

theorem verified : Verified Arm.target Impl.MlKem.Arm.compressEncode
    (Spec.MlKem.compressEncodeContract Arm.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.r0, .r1, .r2, .r3] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, hpres, hsp, h⟩ := correct hp
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlKem.compressEncodeContract, Spec.MlKem.compressEncodeSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlKem.compressEncodeContract, Spec.MlKem.compressEncodeSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨-, h0, h1, h2, h3⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.compressEncodeContract, Spec.MlKem.compressEncodeSig, Arm.abi,
        Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact Add.reduced_zero _
        | decide +kernel

end VG.Proof.MlKem.Arm.CompressEncode
