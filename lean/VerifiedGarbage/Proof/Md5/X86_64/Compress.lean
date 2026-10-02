import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Md5.Spec
import VerifiedGarbage.Impl.Md5.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Md5
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Md5.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Offset

/-!
# MD5 compression function on x86-64: the 64 operations

Each operation is the auxiliary function of its round, symbolically executed
once per round (`fn_ok`), followed by the additions and the rotation,
symbolically executed once for all operations (`tail_ok`).
-/

namespace VG.Proof.Md5.X86_64

open VG VG.X86_64 VG.Impl.Md5.X86_64
open VG.Spec.Md5 (HashValue Word Block ks Ts roundFn F G H I)

/-- The words `v` are in the registers of operation `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0].setWidth 64 ∧ s.gpr (var t 1) = v[1].setWidth 64 ∧
  s.gpr (var t 2) = v[2].setWidth 64 ∧ s.gpr (var t 3) = v[3].setWidth 64

/-- The registers that hold pointers and the count, and `rsp`: never written by the operations. -/
def pubRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .rsp]

/-- The words move one register along each operation. -/
theorem var_succ (t k : Nat) (hk : k < 3) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 3 := by
  simp only [var]; congr 1; omega

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 4 - t % 4) % 4]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T0 ∧ ∀ p ∈ pubRegs, r ≠ p := by
  simp only [work, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem var_ne_T0 (t k : Nat) : var t k ≠ T0 := (work_ne (var_mem t k)).1

theorem var_ne_pub (t k : Nat) {p : Reg} (hp : p ∈ pubRegs) : var t k ≠ p :=
  (work_ne (var_mem t k)).2 p hp

theorem var_ne_aux : ∀ c < 4, ∀ i < 4, ∀ j < 4, i ≠ j →
    work.getD ((i + 4 - c) % 4) .rax ≠ work.getD ((j + 4 - c) % 4) .rax := by decide

/-- The registers of an operation are all different. -/
theorem var_ne (t : Nat) {i j : Nat} (hi : i < 4) (hj : j < 4) (h : i ≠ j) : var t i ≠ var t j :=
  var_ne_aux (t % 4) (Nat.mod_lt _ (by omega)) i hi j hj h

/-! ## The auxiliary functions -/

theorem fn_ok (r : Nat) (hr : r < 4) (b c d : Reg) (hb : b ≠ T0) (hc : c ≠ T0) (hd : d ≠ T0)
    (s : State) (vb vc vd : Word) (h₁ : s.gpr b = vb.setWidth 64) (h₂ : s.gpr c = vc.setWidth 64)
    (h₃ : s.gpr d = vd.setWidth 64) :
    WP isa (.block (fn r b c d)) s fun s' =>
      s'.gpr T0 = (roundFn r vb vc vd).setWidth 64 ∧ (∀ x, x ≠ T0 → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [T0] at hb hc hd ⊢
  apply WP.of_runBlock
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [fn, T0, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, readSrc32,
    isa, State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, ite_true, ite_false, hb, hc, hd,
    h₁, h₂, h₃, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨?_, fun x hx => by simp [hx], trivial⟩
  · rw [show roundFn 0 = F from rfl, F_eq]
  · rw [show roundFn 1 = G from rfl, G_eq]
  · rfl
  · rw [show roundFn 3 = I from rfl, I_eq]

/-! ## The rest of an operation -/

/-- The instructions of an operation after the auxiliary function. -/
def tailI (a b : Reg) (k : Nat) (T : Word) (n : Nat) : List Instr := [
  .alu32 .add a (.reg T0),
  .alu32 .add a (.mem (at_ .rsi (4 * k))),
  .alu32 .add a (.imm T),
  .shift32 .ror a n,
  .alu32 .add a (.reg b)]

theorem step_split (t : Nat) :
    step t = fn (t / 16) (var t 1) (var t 2) (var t 3) ++
      tailI (var t 0) (var t 1) (ks.getD t 0) (Ts.getD t 0) (32 - Proof.Md5.rot t) := rfl

theorem tail_ok (a b : Reg) (k : Nat) (T : Word) (n : Nat) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 31)
    (hab : a ≠ b) (hsi : a ≠ .rsi)
    (s : State) (va vb f x : Word) (bp : Addr)
    (h₁ : s.gpr a = va.setWidth 64) (h₂ : s.gpr b = vb.setWidth 64) (h₃ : s.gpr T0 = f.setWidth 64)
    (hrsi : s.gpr .rsi = bp) (hin : InRegions (s.rd ++ s.wr) (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4)
    (hx : s.mem.readW (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = x) :
    WP isa (.block (tailI a b k T n)) s fun s' =>
      s'.gpr a = ((va + f + x + T).rotateRight n + vb).setWidth 64 ∧
      (∀ r, r ≠ a → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsi' : Reg.rsi ≠ a := fun h => hsi h.symm
  have hba : b ≠ a := fun h => hab h.symm
  simp only [T0] at h₃
  apply WP.of_runBlock
  simp (config := {decide := true}) only [tailI, T0, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, execShift32, readSrc32, State.ea, State.load32, at_,
    isa, State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, ite_true, ite_false, hsi', hba,
    hn₁, hn₂, and_self, h₁, h₂, h₃, hrsi, hin, hx, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp [hr], trivial⟩

/-! ## One operation -/

/-- The operation is symbolically executed once per round for the auxiliary
function and once for the rest, for any registers `a … d`. -/
theorem step_ok (t : Nat) (ht : t < 64) (s : State) (v : HashValue) (X : Block) (bp : Addr)
    (hv : Vars t s v) (hrsi : s.gpr .rsi = bp)
    (hin : ∀ k < 16, InRegions (s.rd ++ s.wr) (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4)
    (hX : ∀ k (hk : k < 16), s.mem.readW (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = X ⟨k, hk⟩) :
    WP isa (.block (step t)) s fun s' =>
      Vars (t + 1) s' (Spec.Md5.step X v t) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3⟩ := hv
  have hk := ks_lt t ht
  have hr := rot_range t ht
  rw [step_split, WP.block_append_iff]
  refine WP.mono (fn_ok (t / 16) (by omega) _ _ _ (var_ne_T0 t 1) (var_ne_T0 t 2) (var_ne_T0 t 3) s
    v[1] v[2] v[3] h1 h2 h3) fun s₁ ⟨f₁, e₁, m₁, rd₁, wr₁⟩ => ?_
  have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k => e₁ _ (var_ne_T0 t k)
  refine WP.mono (tail_ok (var t 0) (var t 1) (ks.getD t 0) (Ts.getD t 0) (32 - rot t) (by omega)
    (by omega) (var_ne t (by omega) (by omega) (by omega))
    (var_ne_pub t 0 (by simp [pubRegs])) s₁ v[0] v[1] (roundFn (t / 16) v[1] v[2] v[3]) (X ⟨ks.getD t 0, hk⟩) bp
    (by rw [e]; exact h0) (by rw [e]; exact h1) f₁ (by rw [e₁ _ (by decide)]; exact hrsi)
    (by rw [rd₁, wr₁]; exact hin _ hk) (by rw [m₁]; exact hX _ hk))
    fun s₂ ⟨a₂, e₂, m₂, rd₂, wr₂⟩ => ?_
  have g : ∀ r, r ≠ var t 0 → r ≠ T0 → s₂.gpr r = s.gpr r := fun r h h' => by rw [e₂ r h, e₁ r h']
  refine ⟨?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun r hr =>
    g r (fun h => var_ne_pub t 0 hr h.symm) (fun h => by subst h; simp [pubRegs, T0] at hr)⟩
  rw [step_eq X v ht]
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 3 by omega),
    var_succ t _ (show 1 < 3 by omega), var_succ t _ (show 2 < 3 by omega), stepKX,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 3), h3]
  · rw [a₂, rotateLeft_eq _ hr.1 hr.2, BitVec.add_comm (v[1])]
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 1), h1]
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 2), h2]

/-! ## The 64 operations -/

/-- Invariant, relative to the state `sB` at the start of the operations. -/
structure RInv (H : HashValue) (X : Block) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (Spec.Md5.steps H X t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  mem : s.mem = sB.mem

theorem steps_ok (H : HashValue) (X : Block) (bp : Addr) (sB : State) (hrsi : sB.gpr .rsi = bp)
    (hin : ∀ k < 16, InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4)
    (hX : ∀ k (hk : k < 16), sB.mem.readW (bp + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = X ⟨k, hk⟩)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (steps t) sB (RInv H X sB t) := by
  intro t ht
  induction t with
  | zero => exact WP.block_nil (M := isa) ⟨h0, fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    have hs_rsi : s.gpr .rsi = bp := (hs.pub .rsi (by decide)).trans hrsi
    refine WP.mono (step_ok t (by omega) s _ X bp hs.vars hs_rsi (by rw [hs.rd, hs.wr]; exact hin)
      (by rw [hs.mem]; exact hX)) fun s' ⟨hv, hm, hrd, hwr, hp⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hp r hr, hs.pub r hr], by rw [hrd, hs.rd], by rw [hwr, hs.wr],
      by rw [hm, hs.mem]⟩
    rw [Proof.Md5.steps_succ]; exact hv

end VG.Proof.Md5.X86_64

/-!
# MD5 compression function on x86-64: the whole function
-/

/-!
## MD5: the x86-64 contract

**Untrusted**: the contracts the proofs are written against; the artifacts are emitted with the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The contracts of the x86-64
implementations of the compression function and the streaming interface, in
terms of `Spec/Md5.lean`.
-/

namespace VG.Proof.Md5

open Spec.Md5

open VG.X86_64 in
/-- x86-64 contract for
`vg_md5_compress(state: *mut [u32; 4], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 8])`:
updates the MD buffer at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(16 bytes) and `scratch` (64 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the return address on the stack.
The pointers and `n` are public; the MD buffer and the blocks are secret. -/
def compressX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 16⟩
    let blocks : Region := ⟨s.gpr .rsi, 64 * (s.gpr .rdx).toNat⟩
    let scratch : Region := ⟨s.gpr .rcx, 64⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .rdi) =
      compressBlocks (stateAt s.mem (s.gpr .rdi)) s.mem (s.gpr .rsi) (s.gpr .rdx).toNat
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

open VG.X86_64 in
/-- x86-64 contract for `vg_md5_init(state: *mut [u8; 80])`: makes the
streaming state at `state` represent the empty message.

The code may write `state` (80 bytes), which may not overlap the return
address on the stack. The pointer is public. -/
def initX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 80⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [state] ∧ ret.Disjoint state
  post s s' := Repr s'.mem (s.gpr .rdi) []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi

open VG.X86_64 in
/-- x86-64 contract for
`vg_md5_update(state: *mut [u8; 80], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 14])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), then afterwards it represents `m` followed by the `len` bytes at
`data`.

The code may read `data` (`len` bytes) and read and write `state` (80
bytes) and `scratch` (112 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the return address on the stack, nor
the 8 bytes below it (where the call of `vg_md5_compress` stores its
return address).
The pointers, `count` and `len` are public; the state and the data are
secret. -/
def updateX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 80⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 112⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ m, Repr s.mem (s.gpr .rdi) m → s.gpr .rsi = BitVec.ofNat 64 m.length →
    Repr s'.mem (s.gpr .rdi) (m ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

open VG.X86_64 in
/-- x86-64 contract for
`vg_md5_finalize(state: *mut [u8; 80], count: u64, out: *mut [u8; 16], scratch: *mut [u64; 14])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), writes the MD5 digest of `m` to `out`.

The code may read and write `state` (80 bytes, whose contents on exit are
unspecified), `out` (16 bytes) and `scratch` (112 bytes, whose contents on
exit are unspecified). These may not overlap each other, nor the return
address on the stack, nor the 8 bytes below it (where the call of
`vg_md5_compress` stores its return address). The pointers and `count`
are public; the state is secret. -/
def finalizeX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 80⟩
    let out : Region := ⟨s.gpr .rdx, 16⟩
    let scratch : Region := ⟨s.gpr .rcx, 112⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, Repr s.mem (s.gpr .rdi) m → s.gpr .rsi = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (s.gpr .rdx) 16 = Spec.Md5.hash m
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Md5


namespace VG.Proof.Md5.X86_64

open VG VG.X86_64 VG.Impl.Md5.X86_64
open VG.Spec.Md5 (HashValue Word Block stateAt blockAt compressBlocks compress parseBlock)

/-! ## Addresses and regions -/

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem contains_offset' {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofInt 64 (off : Int)) n := by
  rw [ofInt_natCast]; exact contains_offset h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 4) (hk : k < 4) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofInt 64 ((4 * j : Nat) : Int)) 4 (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
  rw [ofInt_natCast, ofInt_natCast]
  exact Offset.sep p (by omega) (by omega) (by omega)

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 4) (hk : k < 4)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) v).readW
      (p + BitVec.ofInt 64 ((4 * j : Nat) : Int)) 32 =
    m.readW (p + BitVec.ofInt 64 ((4 * j : Nat) : Int)) 32 :=
  Mem.readW_writeW_sep (word_sep p hj hk h) (by decide)

theorem save_sep (p : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    Mem.Sep (p + BitVec.ofInt 64 (d : Int)) 8 (p + BitVec.ofInt 64 (e : Int)) 8 := by
  rw [ofInt_natCast, ofInt_natCast]
  exact Offset.sep p h (by omega) (by omega)

/-- Distinct 8-byte slots (where the streaming functions save registers). -/
theorem readW_writeW_save (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofInt 64 (e : Int)) v).readW (p + BitVec.ofInt 64 (d : Int)) 64 =
    m.readW (p + BitVec.ofInt 64 (d : Int)) 64 :=
  Mem.readW_writeW_sep (save_sep p hd he h) (by decide)

theorem stateAt_eq {m : Mem} {p : Addr} {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 4) → m.readW (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = v[k]) :
    stateAt m p = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← ofInt_natCast]; exact h k hk

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 4) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, ofInt_natCast]

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev bp : Addr := s₀.gpr .rsi
abbrev nb : Nat := (s₀.gpr .rdx).toNat
abbrev scr : Addr := s₀.gpr .rcx
abbrev stR : Region := ⟨st s₀, 16⟩
abbrev blR : Region := ⟨bp s₀, 64 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 64⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Md5.compressX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from the state). -/
theorem nb_lt : 64 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega

theorem in_state {k : Nat} (hk : k < 4) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem out_state {k : Nat} (hk : k < 4) :
    InRegions s₀.wr (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 4 := by
  have := h.nb_lt
  rw [ofInt_natCast, show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) from Offset.add_ofNat_add_ofNat _ _ _]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)

/-! ## One block -/

theorem load_eq : load = [
    .mov32 .rax (.mem (at_ .rdi (4 * 0))), .mov32 .r8 (.mem (at_ .rdi (4 * 1))),
    .mov32 .r9 (.mem (at_ .rdi (4 * 2))), .mov32 .r10 (.mem (at_ .rdi (4 * 3)))] := by
  decide

theorem update_eq : update ++ advance = [
    .alu32 .add .rax (.mem (at_ .rdi (4 * 0))), .alu32 .add .r8 (.mem (at_ .rdi (4 * 1))),
    .alu32 .add .r9 (.mem (at_ .rdi (4 * 2))), .alu32 .add .r10 (.mem (at_ .rdi (4 * 3))),
    .store32 (at_ .rdi (4 * 0)) .rax, .store32 (at_ .rdi (4 * 1)) .r8,
    .store32 (at_ .rdi (4 * 2)) .r9, .store32 (at_ .rdi (4 * 3)) .r10,
    .alu .add .rsi (.imm 64), .alu .sub .rdx (.imm 1)] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .rax = v[0].setWidth 64 ∧ s.gpr .r8 = v[1].setWidth 64 ∧
    s.gpr .r9 = v[2].setWidth 64 ∧ s.gpr .r10 = v[3].setWidth 64 := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrdi : s.gpr .rdi = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 4 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  apply WP.of_runBlock
  rw [load_eq]
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide)
  simp (config := {decide := true}) only [vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc32, isa, ea_at,
    State.load32, State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, hrdi, h0, h1, h2, h3, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [stateAt_get _ _ (show 0 < 4 by decide), stateAt_get _ _ (show 1 < 4 by decide),
    stateAt_get _ _ (show 2 < 4 by decide), stateAt_get _ _ (show 3 < 4 by decide)]
  simp (config := {decide := true}) [pubRegs]

/-- Four 32-bit words written to consecutive addresses. -/
def writeState (m : Mem) (p : Addr) (v : HashValue) : Mem :=
  ((((m.writeW (p + BitVec.ofInt 64 ((4 * 0 : Nat) : Int)) v[0]).writeW
    (p + BitVec.ofInt 64 ((4 * 1 : Nat) : Int)) v[1]).writeW
    (p + BitVec.ofInt 64 ((4 * 2 : Nat) : Int)) v[2]).writeW
    (p + BitVec.ofInt 64 ((4 * 3 : Nat) : Int)) v[3])

set_option simprocs false in
theorem stateAt_writeState (m : Mem) (p : Addr) (v : HashValue) : stateAt (writeState m p v) p = v := by
  apply stateAt_eq
  intro k hk
  simp only [writeState]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_word]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  have c : ∀ k, k < 4 → (stR s₀).Contains (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) (32 / 8) :=
    fun k hk => contains_offset' (by omega) (by omega)
  simp only [writeState]
  refine (((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _ (c 3 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hrdi : s.gpr .rdi = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 4) →
      s.mem.readW (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .rsi = s.gpr .rsi + 64 ∧ s'.gpr .rdx = s.gpr .rdx - 1 ∧
      s'.zf = some (s.gpr .rdx - 1 == 0) ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 4 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 4 →
      InRegions s.wr (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, execAlu, readSrc32, readSrc,
    isa, ea_at, State.load32, State.store32, State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.cf_setReg, RegUpd.xmm_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.cf_arithFlags, RegUpd.xmm_arithFlags,
    hrdi, i0, i1, i2, i3, o0, o1, o2, o3,
    m0, m1, m2, m3, v0, v1, v2, v3, ite_true, ite_false,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  refine ⟨?_, by rw [e64], by rw [e1], by rw [e1], trivial⟩
  simp only [writeState, Vector.getElem_zipWith]

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i k : Nat) (hk : k < 16) :
    s₀.mem.readW (blkAddr s₀ i + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = blk s₀ i ⟨k, hk⟩ := by
  rw [readW_bytes, ofInt_natCast]
  simp only [blk, blockAt, parseBlock, Offset.add_ofNat_add_one, Nat.add_assoc, Nat.reduceAdd]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.rdi hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hX : ∀ k (hk : k < 16),
      s₁.mem.readW (blkAddr s₀ i + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = blk s₀ i ⟨k, hk⟩ := by
    intro k hk
    rw [hm₁, hL.frame.readW (hp.blk_contains hi hk) (by simpa using hp.blk_st) (by decide)]
    exact blk_word i k hk
  have hrsi₁ : s₁.gpr .rsi = blkAddr s₀ i := (hpub₁ .rsi (by decide)).trans hL.rsi
  refine WP.seq (WP.mono (steps_ok _ (blk s₀ i) _ s₁ hrsi₁
    (fun k hk => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi hk) hX hv₁ 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hrdi₂ : s₂.gpr .rdi = st s₀ := by
    rw [hR.pub .rdi (by decide), hpub₁ .rdi (by decide), hL.rdi]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hrdi₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.mem, hm₁, stateAt_get _ _ hk]
  obtain ⟨hm₃, hrsi₃, hrdx₃, hzf₃, hrdi₃, hrd₃, hwr₃⟩ := h₃
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hrdx : s₂.gpr .rdx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [pub₂ .rdx (by decide), hL.rdx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hframe : Frame [stR s₀] s₀.mem s₃.mem := by
    rw [hm₃, hR.mem, hm₁]
    exact frame_writeState hL.frame _
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hrdi₃, hrdi₂], by rw [hrd₃, hR.rd, hrd₁, hL.rd],
      by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_⟩
    rw [hm₃, stateAt_writeState, compressBlocks_succ, ← hL.state]
    rfl
  have hev : eval .ne s₃ = some (!(s₂.gpr .rdx - 1 == 0)) := by
    simp [eval, hzf₃]
  rw [hrdx] at hev
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    refine ⟨?_, by omega, { hcommon _ rfl with rsi := ?_, rdx := ?_ }⟩
    · rw [hev]
      have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
        exact hne h'
      simpa using h0
    · rw [hrsi₃, pub₂ .rsi (by decide), hL.rsi]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec _) = BitVec.ofNat _ 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hrdx₃, hrdx]

/-! ## The whole function -/

set_option simprocs false in
theorem test_ok {s₀ : State} :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = s₀.mem ∧
      s₁.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => Common s₀ (nb s₀) s' := by
  refine WP.seq (WP.mono test_ok fun s₁ ⟨hg, hrd, hwr, hm, hzf⟩ => ?_)
  have hc₀ : Common s₀ 0 s₁ :=
    ⟨by rw [hg], hrd, hwr, by rw [hm]; exact Frame.refl _ _, by rw [hm]; rfl⟩
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        rsi := by rw [hg]; simp [blkAddr]
        rdx := by rw [hg]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- The registers no instruction writes: the callee-saved ones, `rdi` and `rcx`. -/
def kept : List Reg := [.rbx, .rbp, .rsp, .r12, .r13, .r14, .r15, .rdi, .rcx]

theorem compress_keeps : ((instrs compress).all fun i => kept.all fun r => !Taint.clobbers i r) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem compress_keeps_reg {r : Reg} (hr : r ∈ kept) : ∀ i ∈ instrs compress, Taint.clobbers i r = false := by
  intro i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp compress_keeps i hi) r hr
  simpa using this

/-- `compress` meets the calling convention and its postcondition. -/
theorem correct' {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Md5.compressX86_64.post s₀ s' := by
  obtain ⟨t, s', he, hc⟩ := correct hp
  refine ⟨t, s', he, ⟨fun r hr => Exec.gpr (compress_keeps_reg ?_) he, ?_⟩, hc.state⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact hc.frame.readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 16⟩, ⟨0x3000, 64⟩]

theorem compress_verified :
    Verified X86_64.target Impl.Md5.X86_64.compress Proof.Md5.compressX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct' (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Md5.X86_64
