import VerifiedGarbage.Proof.Scrypt.Spec
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Impl.Scrypt.X86.Salsa

/-!
# The Salsa20/8 Core on x86 (32-bit)

Untrusted: everything here is checked by Lean. The contracts the proofs of
this directory are written against, and the proof of `vg_salsa20_8`: as on
32-bit ARM (`Proof/Scrypt/Arm/BlockMixVerified.lean`), the sixteen words live in
`scratch`, word `k` at `4k`, and `b` keeps the input until the final
addition. Each line of the rounds is proved once, for any indices
(`line_ok`), and the lines are composed by induction. The proof is written
against a contract under which the code only reads its arguments (which it
does), and moved to the shared contract with `Verified.narrowTo`.
-/

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.X86 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86 (32-bit) contract for `vg_salsa20_8(b: *mut [u8; 64], scratch: *mut [u32; 16])`,
whose arguments are on the stack (cdecl): replaces the 64 bytes at `b` by
their Salsa20/8 Core.

The code may read the arguments (8 bytes above the return address), and read
and write `b` and `scratch` (64 bytes each, the contents of `scratch` on
exit unspecified), which may not overlap each other, the arguments or the
return address, or wrap around the end of the (32-bit) address space. `esp`
and the pointers are public; the data is secret. -/
def salsaX86 : Contract X86.isa where
  pre s :=
    let b : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let scratch : Region := ⟨(arg s 1).setWidth 64, 64⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [b, scratch] ∧
    b.Disjoint scratch ∧ args.Disjoint b ∧ args.Disjoint scratch ∧ ret.Disjoint b ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' :=
    bytesAt s'.mem ((arg s 0).setWidth 64) 64 = salsa (bytesAt s.mem ((arg s 0).setWidth 64) 64)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

open VG.X86 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86 (32-bit) contract for
`vg_scrypt_blockmix(b: *const [u8; 128], r: usize, y: *mut [u8; 128], ry: usize, scratch: *mut [u32; 32])`,
whose arguments are on the stack (cdecl): if `ry = r > 0`, writes
scryptBlockMix of the `128 r` bytes at `b` to `y`.

The code may read the arguments (20 bytes above the return address) and
`b`, and read and write `y` and `scratch` (128 bytes). The written regions
may not overlap each other, `b`, the arguments or the return address; none
of the buffers may overlap the 12 bytes of stack below the return address
(where the code calls `vg_salsa20_8`); nothing may wrap around the end of
the (32-bit) address space. `esp` and the arguments are public; the data is
secret. -/
def blockMixX86 : Contract X86.isa where
  pre s :=
    let r := (arg s 1).toNat
    let b : Region := ⟨(arg s 0).setWidth 64, r * 128⟩
    let y : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat * 128⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 128⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [b, args] ∧ s.wr = [y, scratch] ∧
    y.Disjoint scratch ∧ b.Disjoint y ∧ b.Disjoint scratch ∧ args.Disjoint y ∧ args.Disjoint scratch ∧
    ret.Disjoint y ∧ ret.Disjoint scratch ∧ stack.Disjoint b ∧ stack.Disjoint y ∧
    stack.Disjoint scratch ∧
    (arg s 0).toNat + r * 128 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat * 128 ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 128 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    arg s 3 = arg s 1 ∧ 0 < r
  post s s' := let r := (arg s 1).toNat
    bytesAt s'.mem ((arg s 2).setWidth 64) (128 * r) =
      blockMix r (bytesAt s.mem ((arg s 0).setWidth 64) (128 * r))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

open VG.X86 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86 (32-bit) contract for
`vg_scrypt_romix(b: *mut [u8; 128], r: usize, v: *mut [u8; 128], vlen: usize, scratch: *mut [u8; 128], slen: usize)`,
whose arguments are on the stack (cdecl): if `r > 0`, `vlen = N r` for a
power of two `N`, and `slen = r + 2`, replaces the `128 r` bytes at `b` by
their scryptROMix.

The code may read the arguments (24 bytes above the return address), and
read and write `b`, `v` and `scratch`, which may not overlap each other, the
arguments, the return address or the 36 bytes of stack below it (where the
code calls `vg_scrypt_blockmix`), or wrap around the end of the (32-bit)
address space. `esp`, the arguments and the indices `j` of step 3 are
public. -/
def roMixX86 : Contract X86.isa where
  pre s :=
    let r := (arg s 1).toNat
    let b : Region := ⟨(arg s 0).setWidth 64, r * 128⟩
    let v : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat * 128⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat * 128⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 36, 36⟩
    s.rd = [args] ∧ s.wr = [b, v, scratch] ∧
    b.Disjoint v ∧ b.Disjoint scratch ∧ v.Disjoint scratch ∧
    args.Disjoint b ∧ args.Disjoint v ∧ args.Disjoint scratch ∧
    ret.Disjoint b ∧ ret.Disjoint v ∧ ret.Disjoint scratch ∧
    stack.Disjoint b ∧ stack.Disjoint v ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + r * 128 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat * 128 ≤ 2 ^ 32 ∧
    (arg s 4).toNat + (arg s 5).toNat * 128 ≤ 2 ^ 32 ∧ 36 ≤ (s.gpr .esp).toNat ∧
    (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    0 < r ∧ (arg s 3).toNat % r = 0 ∧ ((arg s 3).toNat / r).isPowerOfTwo ∧ (arg s 5).toNat = r + 2
  post s s' := let r := (arg s 1).toNat
    bytesAt s'.mem ((arg s 0).setWidth 64) (128 * r) =
      roMix r ((arg s 3).toNat / r) (bytesAt s.mem ((arg s 0).setWidth 64) (128 * r))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 6, arg s₁ i = arg s₂ i) ∧
    roMixIndices (arg s₁ 1).toNat ((arg s₁ 3).toNat / (arg s₁ 1).toNat)
        (bytesAt s₁.mem ((arg s₁ 0).setWidth 64) (128 * (arg s₁ 1).toNat)) =
      roMixIndices (arg s₂ 1).toNat ((arg s₂ 3).toNat / (arg s₂ 1).toNat)
        (bytesAt s₂.mem ((arg s₂ 0).setWidth 64) (128 * (arg s₂ 1).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.X86

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movm wp_store addr_toNat)
open VG.Proof.Scrypt.Memory (contains_off)

/-! ## Instructions with a memory operand -/

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `add d, [m]` -/
theorem wp_addm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d (s.gpr d + s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.mem m) :: is)) s Q := by
  refine Proof.Sha256.X86.Stream.WP.cons
    (s' := (arithFlags s (s.gpr d + s.mem.readW a 32)
      (2 ^ 32 ≤ (s.gpr d).toNat + (s.mem.readW a 32).toNat)
      (addOverflow (s.gpr d) (s.mem.readW a 32) (s.gpr d + s.mem.readW a 32))).setReg d
      (s.gpr d + s.mem.readW a 32)) ?_ (k _ (Upd.flags _ _ _ _ _ _))
  simp [exec, execAlu, readSrc, State.load32, ha, hin]

/-- `xor d, [m]` -/
theorem wp_xorm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem m) :: is)) s Q := by
  refine Proof.Sha256.X86.Stream.WP.cons
    (s' := (arithFlags s (s.gpr d ^^^ s.mem.readW a 32) false false).setReg d (s.gpr d ^^^ s.mem.readW a 32))
    ?_ (k _ (Upd.flags _ _ _ _ _ _))
  simp [exec, execAlu, readSrc, State.load32, ha, hin]

/-- `ror d, n` -/
theorem wp_ror {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Upd s s' d ((s.gpr d).rotateRight n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .ror d n :: is)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl)
    (k _ (Upd.setFlags _ _ _ _ _ _ _))

end

/-! ## The precondition -/

section
variable (s₀ : State)
/-- `b`. -/
abbrev bP : BitVec 32 := arg s₀ 0
/-- `scratch`. -/
abbrev scP : BitVec 32 := arg s₀ 1
abbrev bA : Addr := (bP s₀).setWidth 64
abbrev sA : Addr := (scP s₀).setWidth 64
abbrev bR : Region := ⟨bA s₀, 64⟩
abbrev sR : Region := ⟨sA s₀, 64⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 8⟩
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩
/-- The input words. -/
def V : Vector Word 16 := Vector.ofFn fun j => s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * j.1)) 32
/-- The result of the rounds. -/
abbrev Rs : Vector Word 16 := Nat.repeat Spec.Scrypt.doubleRound 4 (V s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [bR s₀, sR s₀]
  disj : (bR s₀).Disjoint (sR s₀)
  a_b : (argR s₀).Disjoint (bR s₀)
  a_s : (argR s₀).Disjoint (sR s₀)
  ret_b : (retR s₀).Disjoint (bR s₀)
  ret_s : (retR s₀).Disjoint (sR s₀)
  b_fit : (bP s₀).toNat + 64 ≤ 2 ^ 32
  s_fit : (scP s₀).toNat + 64 ≤ 2 ^ 32
  sp_fit : (s₀.gpr .esp).toNat + 12 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Scrypt.salsaX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem V_get (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k] = s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * k)) 32 := by
  simp only [V, Vector.getElem_ofFn]

theorem V_get! (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k]! = s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * k)) 32 := by
  rw [getElem!_pos (V s₀) k hk, V_get _ hk]

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

/-- Word `k` of a 64-byte buffer at `p`, as an address. -/
theorem addr_word {p : BitVec 32} (hp : p.toNat + 64 ≤ 2 ^ 32) {k : Nat} (hk : k < 16) :
    addr p (4 * k) = p.setWidth 64 + BitVec.ofNat 64 (4 * k) :=
  addr_eq (by omega)

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (fun _ _ _ => by bv_omega) (by decide)

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem in_b {k : Nat} (hk : k < 16) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (bA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bR s₀, by simp [hp.wr], contains_off (by omega) (by omega)⟩

theorem in_s {k : Nat} (hk : k < 16) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (sA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨sR s₀, by simp [hp.wr], contains_off (by omega) (by omega)⟩

theorem out_b {k : Nat} (hk : k < 16) : InRegions s₀.wr (bA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bR s₀, by simp [hp.wr], contains_off (by omega) (by omega)⟩

theorem out_s {k : Nat} (hk : k < 16) : InRegions s₀.wr (sA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨sR s₀, by simp [hp.wr], contains_off (by omega) (by omega)⟩

/-- A word of `b` is unchanged by a write to `scratch`. -/
theorem b_scr (m : Mem) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16) :
    (m.writeW (sA s₀ + BitVec.ofNat 64 (4 * k)) v).readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (hp.disj.sep (contains_off (by omega) (by omega))
    (contains_off (by omega) (by omega))) (by decide)

/-- A word of `scratch` is unchanged by a write to `b`. -/
theorem s_b (m : Mem) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16) :
    (m.writeW (bA s₀ + BitVec.ofNat 64 (4 * k)) v).readW (sA s₀ + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (sA s₀ + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (hp.disj.symm.sep (contains_off (by omega) (by omega))
    (contains_off (by omega) (by omega))) (by decide)

end Pre

/-- `eax` is `b`, `ecx` is `scratch`, the registers other than `edx` are
those on entry, and so are the permissions. -/
structure Keep (s₀ s : State) : Prop where
  eax : s.gpr .eax = bP s₀
  ecx : s.gpr .ecx = scP s₀
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Keep.upd {s₀ s s' : State} (h : Keep s₀ s) {v : Word} (u : Upd s s' .edx v) : Keep s₀ s' :=
  ⟨by rw [u.other _ (by decide), h.eax], by rw [u.other _ (by decide), h.ecx],
    fun r h1 h2 h3 => by rw [u.other r h3, h.gpr r h1 h2 h3], u.rd.trans h.rd, u.wr.trans h.wr⟩

theorem Keep.mupd {s₀ s s' : State} (h : Keep s₀ s) {m : Mem} (u : Mupd s s' m) : Keep s₀ s' :=
  ⟨by rw [u.gpr, h.eax], by rw [u.gpr, h.ecx], fun r h1 h2 h3 => by rw [u.gpr, h.gpr r h1 h2 h3],
    u.rd.trans h.rd, u.wr.trans h.wr⟩

section
variable {s₀ : State} (hp : Pre s₀) {s : State} (h : Keep s₀ s)
include hp h

theorem ea_b {k : Nat} (hk : k < 16) : s.ea (at_ .eax (4 * k)) = bA s₀ + BitVec.ofNat 64 (4 * k) := by
  rw [ea_at, h.eax]; exact addr_word hp.b_fit hk

theorem ea_s {k : Nat} (hk : k < 16) : s.ea (at_ .ecx (4 * k)) = sA s₀ + BitVec.ofNat 64 (4 * k) := by
  rw [ea_at, h.ecx]; exact addr_word hp.s_fit hk

theorem ld_b {k : Nat} (hk : k < 16) :
    InRegions (s.rd ++ s.wr) (bA s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
  rw [h.rd, h.wr]; exact hp.in_b hk _

theorem ld_s {k : Nat} (hk : k < 16) :
    InRegions (s.rd ++ s.wr) (sA s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
  rw [h.rd, h.wr]; exact hp.in_s hk _

theorem st_b {k : Nat} (hk : k < 16) : InRegions s.wr (bA s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
  rw [h.wr]; exact hp.out_b hk

theorem st_s {k : Nat} (hk : k < 16) : InRegions s.wr (sA s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
  rw [h.wr]; exact hp.out_s hk

end

/-! ## Loading the pointers and copying the input -/

/-- After copying `n` words: `b` is as on entry, and its first `n` words are
in `scratch`. -/
structure CI (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep s₀ s
  b : ∀ j < 16, s.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 = (V s₀)[j]!
  copied : ∀ j < 16, j < n → s.mem.readW (sA s₀ + BitVec.ofNat 64 (4 * j)) 32 = (V s₀)[j]!

/-- The argument words are in the arguments' region. -/
theorem arg_in {s₀ : State} (hp : Pre s₀) {d : Nat} (h1 : 4 ≤ d) (h2 : d + 4 ≤ 12) :
    InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) d) 4 := by
  have hs := hp.sp_fit
  refine ⟨argR s₀, by simp [hp.rd], ?_⟩
  show (addr (s₀.gpr .esp) d - addr (s₀.gpr .esp) 4).toNat + 4 ≤ 8
  rw [addr_eq (by omega), addr_eq (by omega),
    show (s₀.gpr .esp).setWidth 64 + BitVec.ofNat 64 d - ((s₀.gpr .esp).setWidth 64 + BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (d - 4) by rw [show d = (d - 4) + 4 by omega, BitVec.ofNat_add]; bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The pointers, loaded from the arguments. -/
theorem load_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, Keep s₀ s → s.mem = s₀.mem → WP isa (.block rest) s Q) :
    WP isa (.block (.mov .eax (.mem (at_ .esp 4)) :: .mov .ecx (.mem (at_ .esp 8)) :: rest)) s₀ Q := by
  refine wp_movm (a := addr (s₀.gpr .esp) 4) rfl (arg_in hp (by omega) (by omega)) fun s₁ u₁ => ?_
  refine wp_movm (a := addr (s₀.gpr .esp) 8) (by rw [ea_at, u₁.other _ (by decide)])
    (by rw [u₁.rd, u₁.wr]; exact arg_in hp (by omega) (by omega)) fun s₂ u₂ => k s₂ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_
  · rw [u₂.other _ (by decide), u₁.gpr]; rfl
  · rw [u₂.gpr, u₁.mem]; rfl
  · intro r h1 h2 _; rw [u₂.other r h2, u₁.other r h1]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]
  · rw [u₂.mem, u₁.mem]

theorem copy_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 16) {s : State} (h : CI s₀ n s) :
    WP isa (.block (copyWord n)) s (CI s₀ (n + 1)) := by
  refine wp_movm (ea_b hp h.keep hn) (ld_b hp h.keep hn) fun s₁ u₁ => ?_
  have k₁ := h.keep.upd u₁
  refine wp_store (ea_s hp k₁ hn) (st_s hp k₁ hn) fun s₂ u₂ => WP.block_nil ?_
  have hv : s₁.gpr .edx = (V s₀)[n]! := by rw [u₁.gpr, h.b n hn]
  refine ⟨k₁.mupd u₂, fun j hj => ?_, fun j hj hjn => ?_⟩
  · rw [u₂.mem, hp.b_scr _ _ hj hn, u₁.mem, h.b j hj]
  · rw [u₂.mem, hv, u₁.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · rw [readW_writeW_word _ _ _ hj hn (by omega), h.copied j hj hjn]
    · exact Mem.readW_writeW_self32 _ _ _

/-! ## The rounds -/

/-- The words `v` are in `scratch`, and `b` is as on entry. -/
structure RI (s₀ : State) (v : Vector Word 16) (s : State) : Prop where
  keep : Keep s₀ s
  b : ∀ j < 16, s.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 = (V s₀)[j]!
  holds : ∀ j < 16, s.mem.readW (sA s₀ + BitVec.ofNat 64 (4 * j)) 32 = v[j]!

/-- The side conditions of `line_ok`, decidable for concrete arguments. -/
def LSide (i j k n : Nat) : Bool :=
  decide (i < 16 ∧ j < 16 ∧ k < 16 ∧ 1 ≤ n ∧ n ≤ 31)

theorem stepN_get! (x : Vector Word 16) {i j k : Nat} (n : Nat) (hi : i < 16) (hj : j < 16)
    (hk : k < 16) (m : Nat) (hm : m < 16) :
    (stepN x i j k n)[m]! = if i = m then x[i]! ^^^ (x[j]! + x[k]!).rotateLeft n else x[m]! := by
  rw [getElem!_pos _ m hm, getElem!_pos _ i hi, getElem!_pos _ j hj, getElem!_pos _ k hk,
    getElem!_pos _ m hm, stepN_get x n hi hj hk m hm]

theorem line_ok {i j k n : Nat} (hs : LSide i j k n = true) {s₀ : State} (hp : Pre s₀)
    {v : Vector Word 16} {s : State} (h : RI s₀ v s) :
    WP isa (.block (line i j k n)) s (RI s₀ (stepN v i j k n)) := by
  simp only [LSide, decide_eq_true_eq] at hs
  obtain ⟨hi, hj, hk, h1, h2⟩ := hs
  unfold line
  refine wp_movm (ea_s hp h.keep hj) (ld_s hp h.keep hj) fun s₁ u₁ => ?_
  have k₁ := h.keep.upd u₁
  refine wp_addm (ea_s hp k₁ hk) (ld_s hp k₁ hk) fun s₂ u₂ => ?_
  have k₂ := k₁.upd u₂
  refine wp_ror (by omega) fun s₃ u₃ => ?_
  have k₃ := k₂.upd u₃
  refine wp_xorm (ea_s hp k₃ hi) (ld_s hp k₃ hi) fun s₄ u₄ => ?_
  have k₄ := k₃.upd u₄
  refine wp_store (ea_s hp k₄ hi) (st_s hp k₄ hi) fun s₅ u₅ => WP.block_nil ?_
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have e4 : s₄.gpr .edx = v[i]! ^^^ (v[j]! + v[k]!).rotateLeft n := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₃.mem, u₂.mem, u₁.mem, h.holds j hj, h.holds k hk,
      h.holds i hi, rotateLeft_eq _ (by omega) (by omega), BitVec.xor_comm]
  refine ⟨k₄.mupd u₅, fun m hm => ?_, fun m hm => ?_⟩
  · rw [u₅.mem, hp.b_scr _ _ hm hi, m₄, h.b m hm]
  · rw [u₅.mem, m₄, e4, stepN_get! v n hi hj hk m hm]
    by_cases e : i = m
    · subst e
      rw [ite_pos' rfl]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [ite_neg' e, readW_writeW_word _ _ _ hm hi (Ne.symm e), h.holds m hm]

theorem lines_ok {s₀ : State} (hp : Pre s₀) :
    ∀ (l : List (Nat × Nat × Nat × Nat)), (l.all fun (i, j, k, n) => LSide i j k n) = true →
      ∀ (v : Vector Word 16) (s : State), RI s₀ v s →
      WP isa (.block (l.flatMap fun (i, j, k, n) => line i j k n)) s
        (RI s₀ (l.foldl (fun x (i, j, k, n) => stepN x i j k n) v))
  | [], _, _, _, h => WP.block_nil h
  | (i, j, k, n) :: l, hl, v, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rw [List.flatMap_cons, WP.block_append_iff, List.foldl_cons]
    exact WP.mono (line_ok hl.1 hp h) fun s' h' => lines_ok hp l hl.2 _ s' h'

theorem doubleRound_eq (v : Vector Word 16) : Spec.Scrypt.doubleRound v =
    lines.foldl (fun x (i, j, k, n) => stepN x i j k n) v := rfl

theorem doubleRound_ok {s₀ : State} (hp : Pre s₀) {v : Vector Word 16} {s : State} (h : RI s₀ v s) :
    WP isa doubleRound s (RI s₀ (Spec.Scrypt.doubleRound v)) := by
  rw [doubleRound_eq]
  exact lines_ok hp lines (by decide) v s h

theorem rounds_ok {s₀ : State} (hp : Pre s₀) {v : Vector Word 16} {s : State} (h : RI s₀ v s) :
    ∀ n, WP isa (rounds n) s (RI s₀ (Nat.repeat Spec.Scrypt.doubleRound n v))
  | 0 => WP.block_nil h
  | n + 1 => WP.seq (WP.mono (rounds_ok hp h n) fun _ h' => doubleRound_ok hp h')

/-! ## Adding the input -/

/-- After finishing words `0 … i - 1`: those words of `b` hold the sums,
the others still hold the input, and `scratch` holds the rounds' result. -/
structure FI (s₀ : State) (R : Vector Word 16) (i : Nat) (s : State) : Prop where
  keep : Keep s₀ s
  out : ∀ j < 16, s.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 =
    if j < i then R[j]! + (V s₀)[j]! else (V s₀)[j]!
  scr : ∀ j < 16, s.mem.readW (sA s₀ + BitVec.ofNat 64 (4 * j)) 32 = R[j]!

theorem finish_step {s₀ : State} (hp : Pre s₀) {R : Vector Word 16} {i : Nat} (hi : i < 16)
    {s : State} (h : FI s₀ R i s) : WP isa (.block (finishWord i)) s (FI s₀ R (i + 1)) := by
  unfold finishWord
  refine wp_movm (ea_s hp h.keep hi) (ld_s hp h.keep hi) fun s₁ u₁ => ?_
  have k₁ := h.keep.upd u₁
  refine wp_addm (ea_b hp k₁ hi) (ld_b hp k₁ hi) fun s₂ u₂ => ?_
  have k₂ := k₁.upd u₂
  refine wp_store (ea_b hp k₂ hi) (st_b hp k₂ hi) fun s₃ u₃ => WP.block_nil ?_
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have e2 : s₂.gpr .edx = R[i]! + (V s₀)[i]! := by
    rw [u₂.gpr, u₁.gpr, u₁.mem, h.scr i hi, h.out i hi, ite_neg' (Nat.lt_irrefl i)]
  refine ⟨k₂.mupd u₃, fun j hj => ?_, fun j hj => ?_⟩
  · rw [u₃.mem, m₂, e2]
    by_cases e : j = i
    · subst e
      rw [Mem.readW_writeW_self32, ite_pos' (Nat.lt_succ_self j)]
    · rw [readW_writeW_word _ _ _ hj hi e, h.out j hj]
      by_cases hji : j < i
      · rw [ite_pos' hji, ite_pos' (by omega)]
      · rw [ite_neg' hji, ite_neg' (by omega)]
  · rw [u₃.mem, m₂, hp.s_b _ _ hj hi, h.scr j hj]

/-! ## The whole function -/

/-- The input words are those the specification reads from the bytes. -/
theorem input_eq (s₀ : State) :
    (Vector.ofFn fun j : Fin 16 => Spec.Scrypt.wordLE (Spec.Scrypt.bytesAt s₀.mem (bA s₀) 64) j.1) =
      V s₀ := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, V_get _ hj, wordLE_bytesAt _ _ (by omega)]

/-- The result words are where the specification writes its bytes. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ j < 16, m.readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₀)[j]! + (V s₀)[j]!) :
    Spec.Scrypt.bytesAt m (bA s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bA s₀) 64) := by
  rw [Spec.Scrypt.salsa, input_eq]
  refine bytesAt_eq_serialize _ _ _ fun j hj => ?_
  rw [Spec.Scrypt.core, Vector.getElem_zipWith, h j hj, getElem!_pos _ j hj, getElem!_pos _ j hj]

theorem copy_eq : copy = .mov .eax (.mem (at_ .esp 4)) :: .mov .ecx (.mem (at_ .esp 8)) ::
    (List.range 16).flatMap copyWord := rfl

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa salsa s₀ fun s' => Keep s₀ s' ∧ Proof.Scrypt.salsaX86.post s₀ s' := by
  refine WP.seq ?_
  rw [copy_eq]
  refine load_ok hp fun s₁ k₁ m₁ => ?_
  have hc₁ : CI s₀ 0 s₁ :=
    ⟨k₁, fun j hj => by rw [m₁, V_get! _ hj], fun _ _ h => absurd h (by omega)⟩
  refine WP.mono (wp_range_flatMap (M := isa) (CI s₀) (fun k s hk h => copy_step hp hk h) 16
    (Nat.le_refl _) s₁ hc₁) fun s₂ h₂ => ?_
  have hr₂ : RI s₀ (V s₀) s₂ := ⟨h₂.keep, h₂.b, fun j hj => h₂.copied j hj hj⟩
  refine WP.seq (WP.mono (rounds_ok hp hr₂ 4) fun s₃ h₃ => ?_)
  have hF₀ : FI s₀ (Rs s₀) 0 s₃ :=
    ⟨h₃.keep, fun j hj => by rw [ite_neg' (Nat.not_lt_zero j), h₃.b j hj], h₃.holds⟩
  unfold finish
  refine WP.mono (wp_range_flatMap (M := isa) (FI s₀ (Rs s₀)) (fun i s hi h => finish_step hp hi h)
    16 (Nat.le_refl _) s₃ hF₀) fun s' hF => ⟨hF.keep, ?_⟩
  show Spec.Scrypt.bytesAt s'.mem (bA s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bA s₀) 64)
  exact post_of fun j hj => by rw [hF.out j hj, ite_pos' hj]

theorem salsa_correct (s : State) (hs : Proof.Scrypt.salsaX86.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86.salsa s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.salsaX86.post s s' := by
  have hp := pre_of s hs
  obtain ⟨t, s', he, hk, h₂⟩ := correct hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, ?_⟩, h₂⟩
  · refine hk.gpr r ?_ ?_ ?_ <;> rintro rfl <;> simp [calleeSaved] at hr
  · obtain ⟨-, -, hf⟩ := Exec.regions he (by decide)
    rw [hp.wr] at hf
    refine hf.readW (r := retR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hp.ret_b, hp.ret_s]

/-! ## Constant time -/

/-- The taint analysis starts with `esp` public, and the words holding `b`
and `scratch` known to be the base addresses of the writable regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [64, 64], argLen := 12,
    argBases := [(4, 0), (8, 1)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hb := hp.b_fit; have hsc := hp.s_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.disj, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 8) (by omega) hp.ret_b hp.a_b
    · exact VG.X86.Taint.frame_disjoint (n := 8) (by omega) hp.ret_s hp.a_s
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Scrypt.salsaX86.pre s₁)
    (h₂ : Proof.Scrypt.salsaX86.pre s₂) (hpub : Proof.Scrypt.salsaX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [bR, sR, bA, sA, bP, scP, a0, a1]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.sp_fit h4 hk, VG.X86.Taint.argByte_eq hp₂.sp_fit h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

theorem salsa_ct : ConstantTime isa Proof.Scrypt.salsaX86.pre Proof.Scrypt.salsaX86.pub
    Impl.Scrypt.X86.salsa :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub)
    (by taint_decide)

/-- Memory holding the arguments `0x1000, 0x2000` at `0x4004`. -/
def satMem : Mem := fun a => if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x4004, 8⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩]

theorem sat_pre : Proof.Scrypt.salsaX86.pre satState := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 0x2000 := by decide
  have e : argAddr satState 0 = 0x4004 := by decide
  simp only [Proof.Scrypt.salsaX86, a0, a1, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, satState] at h₁ h₂
    bv_omega

/-! ## The shared contract -/

/-- `salsaX86` with its arguments writable, as the shared contract lets them be. -/
def salsaWide : Contract isa :=
  { Proof.Scrypt.salsaX86 with
    pre := fun s =>
      let b : Region := ⟨(arg s 0).setWidth 64, 64⟩
      let scratch : Region := ⟨(arg s 1).setWidth 64, 64⟩
      let args : Region := ⟨argAddr s 0, 8⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [] ∧ s.wr = [b, scratch, args] ∧
      b.Disjoint scratch ∧ args.Disjoint b ∧ args.Disjoint scratch ∧ ret.Disjoint b ∧
      ret.Disjoint scratch ∧
      (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 12 ≤ 2 ^ 32 }

/-- The regions `salsaX86` lets the code read and write. -/
def narrowRd (s : State) : List Region := [⟨argAddr s 0, 8⟩]
def narrowWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 64⟩, ⟨(arg s 1).setWidth 64, 64⟩]

/-- Rewrites the contracts at a narrowed state (`arg` does not unfold
cheaply). -/
local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Scrypt.salsaX86, VG.Proof.Scrypt.X86.salsaWide,
    VG.Proof.Scrypt.X86.narrowRd, VG.Proof.Scrypt.X86.narrowWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem salsaWide_pre (s : State) (h : salsaWide.pre s) :
    Proof.Scrypt.salsaX86.pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ := h
  narrow
  exact ⟨trivial, trivial, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩

/-- A state satisfying `salsaWide.pre`. -/
def wideSat : State := { satState with rd := [], wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x4004, 8⟩] }

theorem salsaWide_implies : salsaWide.Implies (Spec.Scrypt.salsaContract X86.abi) := by
  have a0 : arg wideSat 0 = 0x1000 := by decide
  have a1 : arg wideSat 1 = 0x2000 := by decide
  have e : argAddr wideSat 0 = 0x4004 := by decide
  have esp : wideSat.gpr .esp = 0x4000 := rfl
  sig_implies [Spec.Scrypt.salsaContract, Spec.Scrypt.salsaSig, salsaWide, Proof.Scrypt.salsaX86,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, e, esp] using wideSat

/-- The proof is written against `salsaX86`, widened to writable arguments. -/
theorem salsa_verified :
    Verified X86.target Impl.Scrypt.X86.salsa (Spec.Scrypt.salsaContract X86.abi) :=
  have hsat := salsaWide_implies.sat_left
  (Verified.narrowTo (Verified.of_correct salsa_correct salsa_ct (.refl ⟨satState, sat_pre⟩))
    narrowRd narrowWr salsaWide_pre
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat).of_implies salsaWide_implies

end VG.Proof.Scrypt.X86
