import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Sha3.X86_64
import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Impl.Sha3.X86_64.Stream
import VerifiedGarbage.Proof.Sha3.X86_64.Round

section

section

/-!
# SHA-3 on x86-64: one instruction at a time

Weakest-precondition rules for the instruction forms the SHA-3 code uses,
exposing only what changes, so that proofs about a block stay small.
-/

namespace VG.Proof.Sha3.X86_64

open VG VG.X86_64

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

/-- `s'` is `s` with register `d` set to `v` (flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.withFlags (s : State) (cf o zf sf : Option Bool) (d : Reg) (v : BitVec 64) :
    Upd s ((s.setFlags cf o zf sf).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) {w : Nat} (d : Reg) (x : BitVec w) (c o : Bool) (v : BitVec 64) :
    Upd s ((arithFlags s x c o).setReg d v) d v :=
  Upd.withFlags _ _ _ _ _ _ _

theorem Upd.trans {s₁ s₂ s₃ : State} {d : Reg} {v w : BitVec 64} (h₁ : Upd s₁ s₂ d v)
    (h₂ : Upd s₂ s₃ d w) : Upd s₁ s₃ d w :=
  ⟨h₂.gpr, fun r h => (h₂.other r h).trans (h₁.other r h), h₂.mem.trans h₁.mem,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' d (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d (s.mem.readW a 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, readSrc, State.load64, ha, hin]

theorem wp_movi64 {d : Reg} {v : BitVec 64} (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) :
    WP isa (.block (.movImm64 d v :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_xor {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_and {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d &&& s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_xori {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_xorm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := (arithFlags s (s.gpr d ^^^ s.mem.readW a 64) false false).setReg d
    (s.gpr d ^^^ s.mem.readW a 64)) ?_ (k _ (Upd.flags _ _ _ _ _ _))
  simp [exec, execAlu, readSrc, State.load64, ha, hin]

theorem wp_ror {d : Reg} {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 63)
    (k : ∀ s', Upd s s' d ((s.gpr d).rotateRight n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .ror d n :: is)) s Q := by
  have e : exec (.shift .ror d n) s = some ((s.setFlags (some ((s.gpr d).rotateRight n).msb)
      (if n = 1 then some (((s.gpr d).rotateRight n).msb ^^ ((s.gpr d).rotateRight n).getMsbD 1)
        else none) s.zf s.sf).setReg d ((s.gpr d).rotateRight n)) := by
    simp only [exec, execShift, h₁, h₂, and_self, ite_true]
  exact WP.cons e (k _ (Upd.withFlags _ _ _ _ _ _ _))

theorem wp_addi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_cmp {d r : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      s'.zf = some (s.gpr d - s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

theorem wp_store {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a (s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store64, ha, hout]

theorem wp_mov32i {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (v.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d - v.signExtend 64) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_addi_zf {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v.signExtend 64) →
      s'.zf = some (s.gpr d + v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_test {d : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl)

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' d ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem a).setWidth 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, State.load8, ha, hin]

theorem wp_store8 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth 8) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 8) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store8, ha, hout]

end

theorem wp_nil {s : State} {Q : State → Prop} (h : Q s) : WP isa (.block []) s Q := WP.block_nil h

end VG.Proof.Sha3.X86_64

end

/-!
# Keccak-f[1600] on x86-64: addresses

(A round is proven by evaluation, in `Round.lean`.)
-/

namespace VG.Proof.Sha3.X86_64

open VG VG.X86_64 VG.Impl.Sha3.X86_64

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]; rw [ofInt_natCast]

theorem ea_lane (s : State) (b : Reg) (i : Nat) :
    s.ea (lane b i) = s.gpr b + BitVec.ofNat 64 (8 * i) := ea_at s b (8 * i)

end VG.Proof.Sha3.X86_64

end

/-!
# Keccak-f[1600] on x86-64: the whole function
-/

namespace VG.Proof.Sha3

open Spec.Sha3

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for
`vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut [u64; 64])`: applies
Keccak-f[1600] to the state at `state`.

The code may read and write `state` (200 bytes) and `scratch` (512 bytes,
whose contents on exit are unspecified). These may not overlap each other,
nor the return address on the stack. The pointers are public; the state is
secret. It returns with `rdi` and `rsi` as they were, which callers rely
on. -/
def permuteX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let scratch : Region := ⟨s.gpr .rsi, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch
  post s s' := stateAt s'.mem (s.gpr .rdi) = keccakF (stateAt s.mem (s.gpr .rdi)) ∧
    s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rsi = s.gpr .rsi
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for `vg_keccak_absorb(state = rdi, rate = rsi, pos = rdx,
data = rcx, len = r8, scratch = r9) -> rax`: absorbs `data` into the
streaming state (`Repr`) and returns the new position in the block.

The code may read `data`, read and write `state` (200 bytes) and `scratch`
(640 bytes), and store a return address in the 8 bytes below `rsp`, none of
which overlap each other or the return address. `rate` is one of `rates`,
and `pos < rate`. -/
def absorbX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scratch : Region := ⟨s.gpr .r9, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (s.gpr .rsi).toNat ∈ rates ∧ (s.gpr .rdx).toNat < (s.gpr .rsi).toNat
  post s s' :=
    (∀ msg, Repr s.mem (s.gpr .rdi) (s.gpr .rsi).toNat msg →
      (s.gpr .rdx).toNat = msg.length % (s.gpr .rsi).toNat →
      Repr s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat
        (msg ++ bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)) ∧
    (s'.gpr .rax).toNat = ((s.gpr .rdx).toNat + (s.gpr .r8).toNat) % (s.gpr .rsi).toNat
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for `vg_keccak_pad(state = rdi, rate = rsi, pos = rdx,
suffix = rcx, scratch = r8)`: absorbs the padding (with the low byte of
`suffix`) into the streaming state.

The code may read and write `state` (200 bytes) and `scratch` (640 bytes),
and store a return address in the 8 bytes below `rsp`, none of which overlap
each other or the return address. `rate` is one of `rates`, and
`pos < rate`. -/
def padX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let scratch : Region := ⟨s.gpr .r8, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint scratch ∧
    (s.gpr .rsi).toNat ∈ rates ∧ (s.gpr .rdx).toNat < (s.gpr .rsi).toNat
  post s s' := ∀ msg, Repr s.mem (s.gpr .rdi) (s.gpr .rsi).toNat msg →
    (s.gpr .rdx).toNat = msg.length % (s.gpr .rsi).toNat →
    stateAt s'.mem (s.gpr .rdi) =
      absorb (s.gpr .rsi).toNat (pad (s.gpr .rsi).toNat ((s.gpr .rcx).setWidth 8) msg)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for `vg_keccak_squeeze(state = rdi, rate = rsi, pos = rdx,
out = rcx, outlen = r8, scratch = r9) -> rax`: writes `outlen` bytes of
output from byte `pos` on to `out`, and returns the position after them,
leaving a state from which the output continues.

The code may read and write `state` (200 bytes), `out` (`outlen` bytes) and
`scratch` (640 bytes), and store a return address in the 8 bytes below
`rsp`, none of which overlap each other or the return address. `rate` is
one of `rates`, and `pos ≤ rate`. -/
def squeezeX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 200⟩
    let out : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scratch : Region := ⟨s.gpr .r9, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .rsi).toNat ∈ rates ∧ (s.gpr .rdx).toNat ≤ (s.gpr .rsi).toNat
  post s s' :=
    bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
      squeezeFrom (s.gpr .rsi).toNat (stateAt s.mem (s.gpr .rdi)) (s.gpr .rdx).toNat (s.gpr .r8).toNat ∧
    (s'.gpr .rax).toNat ≤ (s.gpr .rsi).toNat ∧
    ∀ d, squeezeFrom (s.gpr .rsi).toNat (stateAt s'.mem (s.gpr .rdi)) (s'.gpr .rax).toNat d =
      squeezeFrom (s.gpr .rsi).toNat (stateAt s.mem (s.gpr .rdi))
        ((s.gpr .rdx).toNat + (s.gpr .r8).toNat) d
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Sha3

namespace VG.Proof.Sha3.X86_64

open VG VG.X86_64 VG.Impl.Sha3.X86_64
open VG.Spec.Sha3 (stateAt keccakF rnd RC)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev scr : Addr := s₀.gpr .rsi
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev scrR : Region := ⟨scr s₀, 512⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev A₀ : KState := stateAt s₀.mem (st s₀)

/-- The state the rounds read from before round `r`, and the one they write. -/
def cur (r : Nat) : Addr := if r % 2 = 0 then st s₀ else scr s₀
def oth (r : Nat) : Addr := if r % 2 = 0 then scr s₀ else st s₀

/-- Scratch offset `d`. -/
abbrev off (d : Nat) : Addr := scr s₀ + BitVec.ofNat 64 d

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha3.permuteX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem cur_succ (s₀ : State) (r : Nat) : cur s₀ (r + 1) = oth s₀ r := by
  simp only [cur, oth]; split <;> split <;> first | rfl | omega

theorem oth_succ (s₀ : State) (r : Nat) : oth s₀ (r + 1) = cur s₀ r := by
  simp only [cur, oth]; split <;> split <;> first | rfl | omega

theorem cur_cases (s₀ : State) (r : Nat) :
    (cur s₀ r = st s₀ ∧ oth s₀ r = scr s₀) ∨ (cur s₀ r = scr s₀ ∧ oth s₀ r = st s₀) := by
  simp only [cur, oth]; split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem in_wr {R : Region} (hR : R = stR s₀ ∨ R = scrR s₀) {a : Addr} {n : Nat}
    (hc : R.Contains a n) : InRegions s₀.wr a n := by
  rw [h.wr]; rcases hR with rfl | rfl
  · exact ⟨_, by simp, hc⟩
  · exact ⟨_, by simp, hc⟩

theorem in_all {a : Addr} {n : Nat} (hw : InRegions s₀.wr a n) : InRegions (s₀.rd ++ s₀.wr) a n := by
  rw [h.rd]; exact hw

theorem lane_in {p : Addr} (hp : p = st s₀ ∨ p = scr s₀) {i : Nat} (hi : i < 25) :
    InRegions s₀.wr (laneAddr p i) 8 := by
  rcases hp with rfl | rfl
  · exact h.in_wr (.inl rfl) (lane_contains _ hi)
  · exact h.in_wr (.inr rfl) (contains_offset (by omega) (by omega))

theorem off_in {d : Nat} (hd : d + 8 ≤ 512) : InRegions s₀.wr (off s₀ d) 8 :=
  h.in_wr (.inr rfl) (contains_offset hd (by omega))

/-- The first 200 bytes of the scratch space are disjoint from the state. -/
theorem st_scr200 : (stR s₀).Disjoint ⟨scr s₀, 200⟩ :=
  h.st_scr.sub_right (Region.sub_prefix (by omega))

/-- The state and the second state are disjoint from every later scratch offset. -/
theorem region_off {p : Addr} (hp : p = st s₀ ∨ p = scr s₀) {d n : Nat} (hd : 200 ≤ d)
    (hn : d + n ≤ 512) : Region.Disjoint ⟨p, 200⟩ ⟨off s₀ d, n⟩ := by
  rcases hp with rfl | rfl
  · exact h.st_scr.sub_right (sub_offset hn (by omega))
  · have := off_disjoint (scr s₀) (a := 0) (n := 200) (b := d) (k := n) (by omega) (by omega)
      (.inl hd)
    rwa [add_zero'] at this

theorem env (r : Nat) (hr : r < 24) :
    Env s₀.rd s₀.wr (cur s₀ r) (oth s₀ r) (off s₀ (200 + 8 * r)) := by
  have hc := cur_cases s₀ r
  have hcur : cur s₀ r = st s₀ ∨ cur s₀ r = scr s₀ := hc.imp (·.1) (·.1)
  have hoth : oth s₀ r = st s₀ ∨ oth s₀ r = scr s₀ := hc.symm.imp (·.2) (·.2)
  refine ⟨fun i hi => h.in_all (h.lane_in hcur hi), fun i hi => h.lane_in hoth hi,
    h.in_all (h.off_in (by omega)), ?_, h.region_off hoth (by omega) (by omega)⟩
  rcases hc with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rw [e₁, e₂]
  · exact h.st_scr200.symm
  · exact h.st_scr200

end Pre

/-! ## The scratch space -/

/-- The saved registers, and the round constants. -/
def Aux (s₀ : State) (m : Mem) : Prop :=
  (∀ k < 6, m.readW (off s₀ (392 + 8 * k)) 64 = s₀.gpr ((saved.getD k (.rax, 0)).1)) ∧
  ∀ j < 24, m.readW (off s₀ (200 + 8 * j)) 64 = RC j

/-- Writes outside the constants and the saved registers keep them. -/
theorem Aux.frame {s₀ : State} {m m' : Mem} (h : Aux s₀ m) {R : Region}
    (hR : ∀ d, 200 ≤ d → d + 8 ≤ 440 → Region.Disjoint ⟨off s₀ d, 8⟩ R) (hf : Frame [R] m m') :
    Aux s₀ m' := by
  refine ⟨fun k hk => ?_, fun j hj => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (by simpa using hR _ (by omega) (by omega)) (by decide)]
    exact h.1 k hk
  · rw [hf.readW (Region.contains_self _ _) (by simpa using hR _ (by omega) (by omega)) (by decide)]
    exact h.2 j hj

/-! ## The prologue -/

theorem save_eq : saved.map (fun (r, d) => Instr.store (at_ .rsi d) r) =
    (List.range 6).flatMap fun k =>
      [.store (at_ .rsi (392 + 8 * k)) ((saved.getD k (.rax, 0)).1)] := by decide

theorem setup_eq : setup = (List.range 6).flatMap (fun k =>
      ([.store (at_ .rsi (392 + 8 * k)) ((saved.getD k (.rax, 0)).1)] : List Instr)) ++
    (List.range 24).flatMap (fun k =>
      ([.movImm64 .rax (RC k), .store (at_ .rsi (200 + 8 * k)) .rax] : List Instr)) ++
    ([.mov .r15 (.imm (-192))] : List Instr) := by
  rw [setup, save_eq]

/-- During the saves. -/
def SaveInv (s₀ : State) (k : Nat) (s : State) : Prop :=
  s.gpr = s₀.gpr ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ Frame [⟨off s₀ 392, 48⟩] s₀.mem s.mem ∧
    ∀ j < k, s.mem.readW (off s₀ (392 + 8 * j)) 64 = s₀.gpr ((saved.getD j (.rax, 0)).1)

theorem saves_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block ((List.range 6).flatMap fun k =>
      [.store (at_ .rsi (392 + 8 * k)) ((saved.getD k (.rax, 0)).1)])) s₀ (SaveInv s₀ 6) := by
  refine wp_range_flatMap (M := isa) (SaveInv s₀) (fun k s hk ⟨hg, hrd, hwr, hf, hv⟩ => ?_) 6 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  refine wp_store (a := off s₀ (392 + 8 * k)) (by rw [ea_at, hg])
    (by rw [hwr]; exact hp.off_in (by omega)) fun s' g' m' r' w' => wp_nil ?_
  refine ⟨g'.trans hg, r'.trans hrd, w'.trans hwr, ?_, fun j hj => ?_⟩
  · rw [m']
    refine hf.writeW (List.mem_singleton_self _) _ ?_
    rw [show off s₀ (392 + 8 * k) = off s₀ 392 + BitVec.ofNat 64 (8 * k) by
      simp only [off]; rw [BitVec.ofNat_add]; ac_rfl]
    exact contains_offset (by omega) (by omega)
  · rw [m', hg]
    by_cases e : j = k
    · subst e; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep ?_ (by decide)]
      · exact hv j (by omega)
      · have := off_disjoint (scr s₀) (a := 392 + 8 * j) (n := 8) (b := 392 + 8 * k) (k := 8)
          (by omega) (by omega) (by omega)
        exact this.sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- During the stores of the round constants, from memory `m₁`. -/
def RcInv (s₀ : State) (m₁ : Mem) (k : Nat) (s : State) : Prop :=
  s.gpr .rdi = st s₀ ∧ s.gpr .rsi = scr s₀ ∧ s.gpr .rsp = s₀.gpr .rsp ∧
    s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ Frame [⟨off s₀ 200, 192⟩] m₁ s.mem ∧
    ∀ j < k, s.mem.readW (off s₀ (200 + 8 * j)) 64 = RC j

theorem rcs_ok {s₀ : State} (hp : Pre s₀) (s : State) (hs : RcInv s₀ s.mem 0 s) :
    WP isa (.block ((List.range 24).flatMap fun k =>
      [.movImm64 .rax (RC k), .store (at_ .rsi (200 + 8 * k)) .rax])) s (RcInv s₀ s.mem 24) := by
  refine wp_range_flatMap (M := isa) (RcInv s₀ s.mem) (fun k s hk ⟨hdi, hsi, hsp, hrd, hwr, hf, hv⟩ => ?_)
    24 (Nat.le_refl _) s hs
  refine wp_movi64 fun s₁ h₁ => wp_store (a := off s₀ (200 + 8 * k))
    (by rw [ea_at, h₁.other _ (by decide), hsi])
    (by rw [h₁.wr, hwr]; exact hp.off_in (by omega)) fun s' g' m' r' w' => wp_nil ?_
  refine ⟨by rw [g', h₁.other _ (by decide), hdi], by rw [g', h₁.other _ (by decide), hsi],
    by rw [g', h₁.other _ (by decide), hsp], by rw [r', h₁.rd, hrd], by rw [w', h₁.wr, hwr], ?_,
    fun j hj => ?_⟩
  · rw [m', h₁.mem]
    refine hf.writeW (List.mem_singleton_self _) _ ?_
    rw [show off s₀ (200 + 8 * k) = off s₀ 200 + BitVec.ofNat 64 (8 * k) by
      simp only [off]; rw [BitVec.ofNat_add]; ac_rfl]
    exact contains_offset (by omega) (by omega)
  · rw [m', h₁.mem, h₁.gpr]
    by_cases e : j = k
    · subst e; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep ?_ (by decide)]
      · exact hv j (by omega)
      · have := off_disjoint (scr s₀) (a := 200 + 8 * j) (n := 8) (b := 200 + 8 * k) (k := 8)
          (by omega) (by omega) (by omega)
        exact this.sep (Region.contains_self _ _) (Region.contains_self _ _)

open VG.Proof.Sha3.X86_64.Round (rowReg kept round_ok check₀ check₁ keeps₀ keeps₁ slots_ok
  complement_check complementRow_check complement_writes complement_writes' rows_of cmpl_cmpl)
open VG.Proof.Sha3.Compl (cmpl)

/-- `r15` before iteration `j` of the loop. -/
def r15At (j : Nat) : BitVec 64 := BitVec.ofNat 64 (16 * j) - 192

/-- The rounds' invariant, before iteration `j` (round `2j`): the state,
with the lanes `complLanes` complemented, at `state`, and its row 4 in
`rowReg`. -/
structure LInv (s₀ : State) (j : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rsi : s.gpr .rsi = scr s₀
  r15 : s.gpr .r15 = r15At j
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : Lanes s.mem (st s₀) (cmpl ((List.range (2 * j)).foldl rnd (A₀ s₀)))
  row : ∀ x (hx : x < 5), s.gpr (rowReg x) = (cmpl ((List.range (2 * j)).foldl rnd (A₀ s₀)))[20 + x]
  aux : Aux s₀ s.mem
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem

theorem lanes₀ (s₀ : State) : Lanes s₀.mem (st s₀) (A₀ s₀) := by
  intro i hi; simp [Spec.Sha3.stateAt, laneAddr]

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (setup ++ complement ++ loadRow)) s₀ (LInv s₀ 0) := by
  rw [setup_eq, List.append_assoc, List.append_assoc, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saves_ok hp) fun s₁ ⟨g₁, rd₁, wr₁, f₁, v₁⟩ => ?_
  refine WP.mono (rcs_ok hp s₁ ⟨by rw [g₁], by rw [g₁], by rw [g₁], rd₁, wr₁, Frame.refl _ _,
    fun _ h => absurd h (by omega)⟩) fun s₂ ⟨di₂, si₂, sp₂, rd₂, wr₂, f₂, v₂⟩ => ?_
  rw [List.singleton_append]
  refine WP.cons rfl ?_
  -- The prologue writes only scratch offsets 200 to 440 before complementing.
  have hf : Frame [⟨off s₀ 200, 240⟩] s₀.mem s₂.mem := by
    refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;>
      exact ⟨_, List.mem_singleton_self _, off_sub _ (by omega) (by omega) (by omega)⟩
  have hd₂ : Region.Disjoint (stR s₀) ⟨off s₀ 200, 240⟩ := hp.region_off (.inl rfl) (by omega) (by omega)
  have hA : Lanes s₂.mem (st s₀) (A₀ s₀) := fun i hi => by
    rw [hf.readW (lane_contains _ hi) (by simpa using hd₂) (by decide)]; exact lanes₀ s₀ i hi
  have haux : Aux s₀ s₂.mem := by
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [f₂.readW (Region.contains_self _ _) ?_ (by decide)]
      · exact v₁ j hj
      · simpa using off_disjoint (scr s₀) (a := 392 + 8 * j) (n := 8) (b := 200) (k := 192)
          (by omega) (by omega) (by omega)
    · exact v₂ j hj
  let s₃ := s₂.setReg .r15 ((-192 : BitVec 32).signExtend 64)
  have hwr : (stR s₀) ∈ s₃.wr := by
    show stR s₀ ∈ s₂.wr; rw [wr₂, hp.wr]; simp
  obtain ⟨s₄, e₄, hs₄, hp₄, hr₄, hl₄, hf₄, rd₄, wr₄, k₄⟩ := slots_ok complementRow_check
    (fun e h => by simp only [Round.rPost, Bool.and_eq_true] at h; exact h.1) complement_writes
    (s := s₃) (show s₂.gpr .rdi = st s₀ from di₂) hwr hA
  refine WP.of_runBlock ⟨s₄, hs₄, ?_⟩
  have hsk : Frame [stR s₀, scrR s₀] s₀.mem s₂.mem :=
    hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, sub_offset (by omega) (by omega)⟩
  refine ⟨by rw [k₄ .rdi (by decide)]; exact di₂, by rw [k₄ .rsi (by decide)]; exact si₂,
    by rw [k₄ .r15 (by decide)]; rfl, by rw [k₄ .rsp (by decide)]; exact sp₂,
    by rw [rd₄]; exact rd₂, by rw [wr₄]; exact wr₂, by simpa using hl₄, fun x hx => ?_, ?_, ?_⟩
  · simpa using rows_of hr₄ hp₄ x hx
  · exact haux.frame (fun d hd hd' => (hp.region_off (.inl rfl) hd (by omega)).symm) hf₄
  · exact hsk.trans (hf₄.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, fun _ h => h⟩)

/-! ## The rounds -/

theorem r15At_succ : ∀ j < 12, r15At j + BitVec.signExtend 64 (16 : BitVec 32) = r15At (j + 1) := by
  decide

theorem r15At_zero : ∀ j < 12, (r15At (j + 1) == 0) = decide (j + 1 = 12) := by decide

theorem rcOff : ∀ j < 12, ∀ k : Nat, k < 2 →
    r15At j * BitVec.ofNat 64 1 + BitVec.ofInt 64 (392 + 8 * (k : Int)) = BitVec.ofNat 64 (200 + 8 * (2 * j + k)) := by
  decide

theorem ea_rcOp {s : State} {j k : Nat} (hj : j < 12) (hk : k < 2) {b : Addr} (hsi : s.gpr .rsi = b)
    (h15 : s.gpr .r15 = r15At j) : s.ea (rcOp k) = b + BitVec.ofNat 64 (200 + 8 * (2 * j + k)) := by
  simp only [State.ea, rcOp, hsi, h15]
  rw [BitVec.add_assoc, rcOff j hj k hk]

theorem cur_even (s₀ : State) (j : Nat) : cur s₀ (2 * j) = st s₀ ∧ oth s₀ (2 * j) = scr s₀ := by
  simp [cur, oth]

theorem cur_odd (s₀ : State) (j : Nat) : cur s₀ (2 * j + 1) = scr s₀ ∧ oth s₀ (2 * j + 1) = st s₀ := by
  simp [cur, oth, Nat.add_mod]

theorem foldl_two (A : KState) (j : Nat) :
    (List.range (2 * (j + 1))).foldl rnd A = rnd (rnd ((List.range (2 * j)).foldl rnd A) (2 * j)) (2 * j + 1) := by
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, foldl_succ, foldl_succ]

/-- Two rounds, from iteration `j`. -/
theorem body_ok {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : j < 12) {s : State} (hL : LInv s₀ j s) :
    WP isa (.block body) s fun s' =>
      eval .ne s' = some (!decide (j + 1 = 12)) ∧ LInv s₀ (j + 1) s' := by
  unfold body
  rw [WP.block_append_iff, WP.block_append_iff]
  have ⟨c₀, o₀⟩ := cur_even s₀ j
  have ⟨c₁, o₁⟩ := cur_odd s₀ j
  have he₀ := hp.env (2 * j) (by omega)
  have he₁ := hp.env (2 * j + 1) (by omega)
  rw [c₀, o₀] at he₀
  rw [c₁, o₁] at he₁
  have hea₀ := ea_rcOp (k := 0) hj (by omega) hL.rsi hL.r15
  have hd₀ : Region.Disjoint ⟨scr s₀, 200⟩ ⟨off s₀ (200 + 8 * (2 * j + 1)), 8⟩ :=
    hp.region_off (.inr rfl) (by omega) (by omega)
  refine WP.mono (round_ok check₀ keeps₀ (by decide) (by decide) 0 (rc := RC (2 * j))
    (src := st s₀) (dst := scr s₀) hL.rdi hL.rsi
    (by rw [hL.rd, hL.wr, hea₀]; exact he₀) hL.state hL.row
    (by rw [hea₀]; exact hL.aux.2 (2 * j) (by omega))) fun s₁ ⟨l₁, w₁, f₁, rd₁, wr₁, k₁⟩ => ?_
  have aux₁ : Aux s₀ s₁.mem := hL.aux.frame (fun d hd hd' => (hp.region_off (.inr rfl) hd (by omega)).symm) f₁
  have hea₁ := ea_rcOp (k := 1) (b := scr s₀) hj (by omega) (by rw [k₁ .rsi (by decide)]; exact hL.rsi)
    (by rw [k₁ .r15 (by decide)]; exact hL.r15)
  refine WP.mono (round_ok check₁ keeps₁ (by decide) (by decide) 1 (rc := RC (2 * j + 1))
    (src := scr s₀) (dst := st s₀)
    (by rw [k₁ .rsi (by decide)]; exact hL.rsi) (by rw [k₁ .rdi (by decide)]; exact hL.rdi)
    (by rw [rd₁, wr₁, hL.rd, hL.wr, hea₁]; exact he₁) l₁ w₁
    (by rw [hea₁]; exact aux₁.2 (2 * j + 1) (by omega))) fun s₂ ⟨l₂, w₂, f₂, rd₂, wr₂, k₂⟩ => ?_
  have h15 : s₂.gpr .r15 = r15At j := by rw [k₂ .r15 (by decide), k₁ .r15 (by decide), hL.r15]
  refine wp_addi_zf fun s₃ u₃ z₃ => wp_nil ⟨?_, ?_⟩
  · simp only [eval, z₃, h15, r15At_succ j hj, r15At_zero j hj, Option.map_some]
  · have keep : ∀ r ∈ kept, r ≠ .r15 → s₃.gpr r = s.gpr r := fun r hr h => by
      rw [u₃.other r h, k₂ r hr, k₁ r hr]
    have hst : cmpl (Proof.Sha3.outState (Proof.Sha3.outState ((List.range (2 * j)).foldl rnd (A₀ s₀))
        (RC (2 * j))) (RC (2 * j + 1))) = cmpl ((List.range (2 * (j + 1))).foldl rnd (A₀ s₀)) := by
      rw [Proof.Sha3.outState_eq, Proof.Sha3.outState_eq, foldl_two]
    rw [hst] at l₂ w₂
    have hrow : ∀ x < 5, rowReg x ≠ .r15 := by decide
    exact ⟨by rw [keep .rdi (by decide) (by decide), hL.rdi], by rw [keep .rsi (by decide) (by decide), hL.rsi],
      by rw [u₃.gpr, h15, r15At_succ j hj], by rw [keep .rsp (by decide) (by decide), hL.rsp],
      by rw [u₃.rd, rd₂, rd₁, hL.rd], by rw [u₃.wr, wr₂, wr₁, hL.wr], by rw [u₃.mem]; exact l₂,
      fun x hx => by rw [u₃.other _ (hrow x hx), w₂ x hx],
      by rw [u₃.mem]; exact aux₁.frame (fun d hd hd' => (hp.region_off (.inl rfl) hd (by omega)).symm) f₂,
      by
        rw [u₃.mem]
        refine (hL.frame.trans (f₁.sub fun r hr => ?_)).trans (f₂.sub fun r hr => ?_) <;>
          simp only [List.mem_singleton] at hr <;> subst hr
        · exact ⟨scrR s₀, by simp, Region.sub_prefix (by omega)⟩
        · exact ⟨stR s₀, by simp, fun _ h => h⟩⟩

/-! ## The epilogue -/

theorem restore_eq : restore = (List.range 6).flatMap fun k =>
    [.mov ((saved.getD k (.rax, 0)).1) (.mem (at_ .rsi (392 + 8 * k)))] := by decide

theorem saved_ne : ∀ j < 6, ∀ k < 6, j ≠ k → (saved.getD j (.rax, 0)).1 ≠ (saved.getD k (.rax, 0)).1 := by
  decide

theorem saved_ne_rsi : ∀ k < 6, (saved.getD k (.rax, 0)).1 ≠ .rsi ∧ (saved.getD k (.rax, 0)).1 ≠ .rsp ∧
    (saved.getD k (.rax, 0)).1 ≠ .rdi := by
  decide

/-- After the rounds and the complementing back. -/
structure EInv (s₀ s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rsi : s.gpr .rsi = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : Lanes s.mem (st s₀) (keccakF (A₀ s₀))
  aux : Aux s₀ s.mem
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem

/-- During the restores. -/
def ResInv (s₀ s₁ : State) (k : Nat) (s : State) : Prop :=
  s.gpr .rsi = scr s₀ ∧ s.gpr .rdi = st s₀ ∧ s.gpr .rsp = s₀.gpr .rsp ∧ s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧
    ∀ j < k, s.gpr ((saved.getD j (.rax, 0)).1) = s₀.gpr ((saved.getD j (.rax, 0)).1)

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hE : EInv s₀ s) :
    WP isa (.block restore) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha3.permuteX86_64.post s₀ s' := by
  rw [restore_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (ResInv s₀ s) (fun k s' hk ⟨si, di, sp, m, rd, wr, v⟩ => ?_) 6
    (Nat.le_refl _) s ⟨hE.rsi, hE.rdi, hE.rsp, rfl, rfl, rfl, fun _ h => absurd h (by omega)⟩)
    fun s' ⟨si, di, sp, m, _, _, v⟩ => ?_
  · refine wp_movm (a := off s₀ (392 + 8 * k)) (by rw [ea_at, si])
      (by rw [rd, wr, hE.rd, hE.wr]; exact hp.in_all (hp.off_in (by omega))) fun s'' h => wp_nil ?_
    have ne := saved_ne_rsi k hk
    refine ⟨by rw [h.other _ (Ne.symm ne.1), si], by rw [h.other _ (Ne.symm ne.2.2), di],
      by rw [h.other _ (Ne.symm ne.2.1), sp],
      by rw [h.mem, m], by rw [h.rd, rd], by rw [h.wr, wr], fun j hj => ?_⟩
    by_cases e : j = k
    · subst e; rw [h.gpr, m]; exact hE.aux.1 j hk
    · rw [h.other _ (saved_ne j (by omega) k hk e), v j (by omega)]
  · refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact v 0 (by omega)
      · exact v 1 (by omega)
      · exact sp
      · exact v 2 (by omega)
      · exact v 3 (by omega)
      · exact v 4 (by omega)
      · exact v 5 (by omega)
    · rw [m]
      exact hE.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
    · refine ⟨?_, di, si⟩
      apply Vector.ext
      intro i hi
      simp only [Spec.Sha3.stateAt, Vector.getElem_ofFn, m]
      exact hE.state i hi

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hL : LInv s₀ 12 s) :
    WP isa (.block (complement ++ restore)) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha3.permuteX86_64.post s₀ s' := by
  rw [WP.block_append_iff]
  have hwr : stR s₀ ∈ s.wr := by rw [hL.wr, hp.wr]; simp
  obtain ⟨s₁, -, hs₁, -, -, hl₁, hf₁, rd₁, wr₁, k₁⟩ :=
    slots_ok complement_check (fun _ h => h) complement_writes' hL.rdi hwr hL.state
  refine WP.of_runBlock ⟨s₁, hs₁, restore_ok hp ⟨by rw [k₁ .rdi (by decide), hL.rdi],
    by rw [k₁ .rsi (by decide), hL.rsi], by rw [k₁ .rsp (by decide), hL.rsp], by rw [rd₁, hL.rd],
    by rw [wr₁, hL.wr], ?_, ?_, ?_⟩⟩
  · rw [cmpl_cmpl] at hl₁; exact hl₁
  · exact hL.aux.frame (fun d hd hd' => (hp.region_off (.inl rfl) hd (by omega)).symm) hf₁
  · exact hL.frame.trans (hf₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, fun _ h => h⟩)

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha3.permuteX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := LInv s₀ 12) ?_ fun s₂ h₂ => epilogue_ok hp h₂)
  let Inv : Nat → State → Prop := fun n s => ∃ j, n = 12 - j ∧ j < 12 ∧ LInv s₀ j s
  refine WP.loop (M := isa) Inv (fun n s ⟨j, hn, hj, hL⟩ => ?_) 12 s₁ ⟨0, rfl, by omega, h₁⟩
  refine WP.mono (body_ok hp hj hL) fun s' ⟨he, hl⟩ => ?_
  by_cases hlast : j + 1 = 12
  · exact .inl ⟨by show eval .ne s' = _; rw [he, hlast]; rfl, hlast ▸ hl⟩
  · exact .inr ⟨by show eval .ne s' = _; rw [he]; simp [hlast], 12 - (j + 1), by omega, j + 1, rfl, by omega, hl⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 512⟩]

theorem permute_correct (s : State) (hs : Proof.Sha3.permuteX86_64.pre s) :
    ∃ t s', Exec isa Impl.Sha3.X86_64.permute s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.permuteX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

/-- The constant-time analysis's taint without the round constants that the
prologue stores at `[200, 392)` of the scratch space: public, but no
address or branch depends on them, and the kernel checks the analysis much
faster without them (`taint_decide_weak`). -/
def dropRC (τ : VG.X86_64.Taint.T) : VG.X86_64.Taint.T :=
  { τ with slots := τ.slots.filter fun sl => !(200 ≤ sl.2.1 && sl.2.1 < 392) }

theorem permute_ct : ConstantTime isa Proof.Sha3.permuteX86_64.pre Proof.Sha3.permuteX86_64.pub
    Impl.Sha3.X86_64.permute := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi]) ?_ (by taint_decide_weak dropRC)
  intro s₁ s₂ _ _ ⟨h1, h2⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> assumption

theorem permute_verified :
    Verified X86_64.target Impl.Sha3.X86_64.permute (Spec.Sha3.permuteContract X86_64.abi) :=
  -- `permuteX86_64` also says that `rdi` and `rsi` are returned unchanged,
  -- which the shared contract leaves out.
  Verified.of_correct permute_correct permute_ct
    { pre := by
        sig_implies_pre [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig,
          Proof.Sha3.permuteX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig, Proof.Sha3.permuteX86_64,
          X86_64.abi, X86_64.argRegs]
        exact h.1
      pub := by
        sig_implies_pub [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig,
          Proof.Sha3.permuteX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        sig_implies_sat [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig,
          Proof.Sha3.permuteX86_64, X86_64.abi, X86_64.argRegs]
          [Proof.Sha3.X86_64.satState] using Proof.Sha3.X86_64.satState }

end VG.Proof.Sha3.X86_64

section

/-!
# SHA-3 on x86-64: calling the permutation
-/

namespace VG.Proof.Sha3.X86_64

open VG VG.X86_64 VG.Impl.Sha3.X86_64
open VG.Spec.Sha3 (stateAt keccakF)

theorem permute_keeps : ((instrs permute).all fun i => !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem permute_nosp : NoSp permute := by
  intro i hi
  simpa using List.all_eq_true.mp permute_keeps i hi

theorem permute_depth : permute.depth = 0 := by decide +kernel

/-- A region disjoint from the return address of a call reads the same on
entry to the callee. -/
theorem callEntry_byte (s : State) {R : Region} (hd : (below (s.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    s.callEntry.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (s.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using hd.symm) hR hi

/-- Calling `vg_keccak_f1600` on the state at `rdi`, with scratch space at
`rsi`. -/
theorem call_ok {s : State} {st scr : Addr} (hdi : s.gpr .rdi = st) (hsi : s.gpr .rsi = scr)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩) (d₂ : (below (s.gpr .rsp) 8).Disjoint ⟨st, 200⟩)
    (d₃ : (below (s.gpr .rsp) 8).Disjoint ⟨scr, 512⟩)
    (hw : Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) →
      s'.gpr .rdi = st → s'.gpr .rsi = scr → Q s') :
    WP isa (.call "vg_keccak_f1600" permute) s Q := by
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  refine WP.call (k := Proof.Sha3.permuteX86_64) permute_correct permute_nosp
    (by rw [permute_depth]; decide) (rd := []) (wr := [⟨st, 200⟩, ⟨scr, 512⟩]) ?_ ?_ hw ?_
  · simp only [Proof.Sha3.permuteX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hdi, hsi]
    exact ⟨trivial, trivial, d₁, d₂, d₃⟩
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hw a n (by simpa using h)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost, hdi₂, hsi₂⟩
    simp only [State.withRegions_gpr, State.withRegions_mem, hne _ (by decide : Reg.rdi ≠ .rsp), hdi,
      hm₂] at hpost hdi₂
    simp only [State.withRegions_gpr, hne _ (by decide : Reg.rsi ≠ .rsp), hsi] at hsi₂
    have hst : stateAt s.callEntry.mem st = stateAt s.mem st :=
      Proof.Sha3.stateAt_congr fun i hi => callEntry_byte s (R := ⟨st, 200⟩) d₂ (by simp) hi
    refine hQ s' hrd hwr hcs (by rw [permute_depth] at hf; simpa using hf) (by rw [hpost, hst])
      (by rw [← hg₂ _ (by decide), hdi₂]) (by rw [← hg₂ _ (by decide), hsi₂])

/-- `permuteAt`: calling `vg_keccak_f1600` on the state at `rbx`, with
scratch space at `r15`. -/
theorem permuteAt_ok {s : State} {st scr : Addr} (hbx : s.gpr .rbx = st) (h15 : s.gpr .r15 = scr)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩) (d₂ : (below (s.gpr .rsp) 8).Disjoint ⟨st, 200⟩)
    (d₃ : (below (s.gpr .rsp) 8).Disjoint ⟨scr, 512⟩)
    (hw : Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa Impl.Sha3.X86_64.Stream.permuteAt s Q := by
  unfold Impl.Sha3.X86_64.Stream.permuteAt
  refine WP.seq (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_nil ?_)
  have sp₂ : s₂.gpr .rsp = s.gpr .rsp := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have cs₂ : ∀ r ∈ calleeSaved, s₂.gpr r = s.gpr r := fun r hr => by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [u₂.other _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      u₁.other _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  refine WP.seq (call_ok (st := st) (scr := scr)
    (by rw [u₂.other _ (by decide), u₁.gpr, hbx]) (by rw [u₂.gpr, u₁.other _ (by decide), h15])
    d₁ (by rw [sp₂]; exact d₂) (by rw [sp₂]; exact d₃) (by rw [u₂.wr, u₁.wr]; exact hw)
    fun s₃ rd₃ wr₃ cs₃ f₃ e₃ di₃ si₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ => wp_nil ?_)
  refine hQ s₅ (by rw [u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr])
    (fun r hr => ?_) (by rw [u₅.mem, u₄.mem, ← u₁.mem, ← u₂.mem, ← sp₂]; exact f₃)
    (by rw [u₅.mem, u₄.mem, e₃, u₂.mem, u₁.mem])
  by_cases h1 : r = .r15
  · subst h1; rw [u₅.gpr, u₄.other _ (by decide), si₃, h15]
  · by_cases h2 : r = .rbx
    · subst h2; rw [u₅.other _ (by decide), u₄.gpr, di₃, hbx]
    · rw [u₅.other _ h1, u₄.other _ h2, cs₃ r hr, cs₂ r hr]

end VG.Proof.Sha3.X86_64

end
