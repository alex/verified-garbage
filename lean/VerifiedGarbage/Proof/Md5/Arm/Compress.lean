import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Md5.Spec
import VerifiedGarbage.Impl.Md5.Arm
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Spill
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Md5
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Offset

/-!
# MD5 compression function on ARMv7: the 64 operations

Each operation is the auxiliary function of its round, symbolically executed
once per round (`fn_ok`), followed by the additions and the rotation,
symbolically executed once for all operations (`tail_ok`).
-/

namespace VG.Proof.Md5.Arm

open VG VG.Arm VG.Impl.Md5.Arm
open VG.Spec.Md5 (HashValue Word Block ks Ts roundFn F G H I)

/-- The words `v` are in the registers of operation `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧ s.gpr (var t 2) = v[2] ∧ s.gpr (var t 3) = v[3]

/-- The pointers, the count, `Ones` and the registers the operations never
write. -/
def pubRegs : List Reg := [.r0, .r1, .r2, .r3, .r8, .r10, .r11, .lr]

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

theorem work_ne' : ∀ r ∈ work, r ≠ T0 ∧ r ≠ T1 ∧ ∀ p ∈ pubRegs, r ≠ p := by decide

theorem var_ne_T0 (t k : Nat) : var t k ≠ T0 := (work_ne' _ (var_mem t k)).1

theorem var_ne_T1 (t k : Nat) : var t k ≠ T1 := (work_ne' _ (var_mem t k)).2.1

theorem var_ne_pub (t k : Nat) {p : Reg} (hp : p ∈ pubRegs) : var t k ≠ p :=
  (work_ne' _ (var_mem t k)).2.2 p hp

theorem var_ne_aux : ∀ c < 4, ∀ i < 4, ∀ j < 4, i ≠ j →
    work.getD ((i + 4 - c) % 4) .r4 ≠ work.getD ((j + 4 - c) % 4) .r4 := by decide

/-- The registers of an operation are all different. -/
theorem var_ne (t : Nat) {i j : Nat} (hi : i < 4) (hj : j < 4) (h : i ≠ j) : var t i ≠ var t j :=
  var_ne_aux (t % 4) (Nat.mod_lt _ (by omega)) i hi j hj h

/-! ## The auxiliary functions -/

theorem fn_ok (r : Nat) (hr : r < 4) (b c d : Reg) (hb : b ≠ T0) (hc : c ≠ T0) (hd : d ≠ T0)
    (s : State) (vb vc vd : Word) (h₁ : s.gpr b = vb) (h₂ : s.gpr c = vc)
    (h₃ : s.gpr d = vd) (h₄ : s.gpr Ones = ones) :
    WP isa (.block (fn r b c d)) s fun s' =>
      s'.gpr T0 = roundFn r vb vc vd ∧ (∀ x, x ≠ T0 → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [T0, Ones] at hb hc hd h₄ ⊢
  apply WP.of_runBlock
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [fn, T0, Ones, runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, ite_true, ite_false, hb, hc, hd,
    h₁, h₂, h₃, h₄, Option.map_some, Option.some.injEq, exists_eq_left'] <;>
  refine ⟨?_, fun x hx => by simp [hx], trivial⟩
  · rw [show roundFn 0 = F from rfl, F_eq]
  · rw [show roundFn 1 = G from rfl, G_eq]
  · rfl
  · rw [show roundFn 3 = I from rfl, I_eq]; rfl

/-! ## The rest of an operation -/

/-- The instructions of an operation after the auxiliary function. -/
def tailI (a b : Reg) (k : Nat) (T : Word) (n : Nat) : List Instr := [
  .dp .add a a (.reg T0),
  .ldr T1 .r1 (4 * k),
  .dp .add a a (.reg T1),
  .movw T1 (T.extractLsb' 0 16),
  .movt T1 (T.extractLsb' 16 16),
  .dp .add a a (.reg T1),
  .dp .add a b (.shifted a .ror n)]

theorem step_split (t : Nat) :
    step t = fn (t / 16) (var t 1) (var t 2) (var t 3) ++
      tailI (var t 0) (var t 1) (ks.getD t 0) (Ts.getD t 0) (32 - Proof.Md5.rot t) := rfl

theorem tail_ok (a b : Reg) (k : Nat) (hk : k < 16) (T : Word) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 31) (hba : b ≠ a)
    (ha₁ : a ≠ T1) (hb₁ : b ≠ T1) (hax : a ≠ .r1)
    (s : State) (va vb f x : Word) (bp : BitVec 32)
    (h₁ : s.gpr a = va) (h₂ : s.gpr b = vb) (h₃ : s.gpr T0 = f)
    (hr1 : s.gpr .r1 = bp) (hin : InRegions (s.rd ++ s.wr) (State.addr (bp + BitVec.ofNat 32 (4 * k))) 4)
    (hx : s.mem.readW (State.addr (bp + BitVec.ofNat 32 (4 * k))) 32 = x) :
    WP isa (.block (tailI a b k T n)) s fun s' =>
      s'.gpr a = vb + (va + f + x + T).rotateRight n ∧
      (∀ r, r ≠ a → r ≠ T1 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have ho : 4 * k < 4096 := by omega
  have ha₁' : T1 ≠ a := fun h => ha₁ h.symm
  have hax' : Reg.r1 ≠ a := fun h => hax h.symm
  simp only [T0, T1] at h₃ ha₁ ha₁' hb₁ ⊢
  apply WP.of_runBlock
  simp (config := {decide := true}) only [tailI, T0, T1, runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, State.load32, ho, hn, ite_true, ite_false,
    ha₁, ha₁', hb₁, hba, hax', h₁, h₂, h₃, hr1, hin, hx, and_self,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [movw_movt], fun r hr hr' => by simp [hr, hr'], trivial⟩

/-! ## One operation -/

/-- The operation is symbolically executed once per round for the auxiliary
function and once for the rest, for any registers `a … d`. -/
theorem step_ok (t : Nat) (ht : t < 64) (s : State) (v : HashValue) (X : Block) (bp : BitVec 32)
    (hv : Vars t s v) (hr1 : s.gpr .r1 = bp) (hones : s.gpr Ones = ones)
    (hin : ∀ k < 16, InRegions (s.rd ++ s.wr) (State.addr (bp + BitVec.ofNat 32 (4 * k))) 4)
    (hX : ∀ k (hk : k < 16), s.mem.readW (State.addr (bp + BitVec.ofNat 32 (4 * k))) 32 = X ⟨k, hk⟩) :
    WP isa (.block (step t)) s fun s' =>
      Vars (t + 1) s' (Spec.Md5.step X v t) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  obtain ⟨h0, h1, h2, h3⟩ := hv
  have hk := ks_lt t ht
  have hr := rot_range t ht
  rw [step_split, WP.block_append_iff]
  refine WP.mono (fn_ok (t / 16) (by omega) _ _ _ (var_ne_T0 t 1) (var_ne_T0 t 2) (var_ne_T0 t 3) s
    v[1] v[2] v[3] h1 h2 h3 hones) fun s₁ ⟨f₁, e₁, m₁, rd₁, wr₁⟩ => ?_
  have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k => e₁ _ (var_ne_T0 t k)
  refine WP.mono (tail_ok (var t 0) (var t 1) (ks.getD t 0) hk (Ts.getD t 0) (32 - rot t)
    (by omega) (var_ne t (by omega) (by omega) (by omega)) (var_ne_T1 t 0)
    (var_ne_T1 t 1) (var_ne_pub t 0 (by decide)) s₁ v[0] v[1] (roundFn (t / 16) v[1] v[2] v[3])
    (X ⟨ks.getD t 0, hk⟩) bp (by rw [e]; exact h0) (by rw [e]; exact h1) f₁
    (by rw [e₁ _ (by decide)]; exact hr1)
    (by rw [rd₁, wr₁]; exact hin _ hk) (by rw [m₁]; exact hX _ hk))
    fun s₂ ⟨a₂, e₂, m₂, rd₂, wr₂⟩ => ?_
  have g : ∀ r, r ≠ var t 0 → r ≠ T0 → r ≠ T1 → s₂.gpr r = s.gpr r := fun r h h' h'' => by
    rw [e₂ r h h'', e₁ r h']
  refine ⟨?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun r hr =>
    g r (fun h => var_ne_pub t 0 hr h.symm) (fun h => by subst h; simp [pubRegs, T0] at hr)
      (fun h => by subst h; simp [pubRegs, T1] at hr)⟩
  rw [step_eq X v ht]
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 3 by omega),
    var_succ t _ (show 1 < 3 by omega), var_succ t _ (show 2 < 3 by omega), stepKX,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 3) (var_ne_T1 t 3), h3]
  · rw [a₂, rotateLeft_eq _ hr.1 hr.2]
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 1) (var_ne_T1 t 1), h1]
  · rw [g _ (var_ne t (by omega) (by omega) (by omega)) (var_ne_T0 t 2) (var_ne_T1 t 2), h2]

/-! ## The 64 operations -/

/-- Invariant, relative to the state `sB` at the start of the operations. -/
structure RInv (H : HashValue) (X : Block) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (Spec.Md5.steps H X t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  mem : s.mem = sB.mem

theorem steps_ok (H : HashValue) (X : Block) (bp : BitVec 32) (sB : State) (hr1 : sB.gpr .r1 = bp)
    (hones : sB.gpr Ones = ones)
    (hin : ∀ k < 16, InRegions (sB.rd ++ sB.wr) (State.addr (bp + BitVec.ofNat 32 (4 * k))) 4)
    (hX : ∀ k (hk : k < 16), sB.mem.readW (State.addr (bp + BitVec.ofNat 32 (4 * k))) 32 = X ⟨k, hk⟩)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 64, WP isa (steps t) sB (RInv H X sB t) := by
  intro t ht
  induction t with
  | zero => exact WP.block_nil (M := isa) ⟨h0, fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    have hs_r1 : s.gpr .r1 = bp := (hs.pub .r1 (by decide)).trans hr1
    have hs_ones : s.gpr Ones = ones := (hs.pub .r8 (by decide)).trans hones
    refine WP.mono (step_ok t (by omega) s _ X bp hs.vars hs_r1 hs_ones
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.mem]; exact hX)) fun s' ⟨hv, hm, hrd, hwr, hp⟩ => ?_
    refine ⟨?_, fun r hr => by rw [hp r hr, hs.pub r hr], by rw [hrd, hs.rd], by rw [hwr, hs.wr],
      by rw [hm, hs.mem]⟩
    rw [Proof.Md5.steps_succ]; exact hv

end VG.Proof.Md5.Arm

/-!
# MD5 compression function on ARMv7: the whole function
-/

/-!
## MD5: the 32-bit ARM contract

The contracts the proofs are written against; the artifacts are emitted with the
shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
contracts of the 32-bit ARM implementations of the compression function and of
the streaming functions (`init`, `update`, `finalize`; see `VG.Spec.Md5.Repr`),
in terms of `Spec/Md5.lean`. The streaming contracts are those of AArch64
(`Proof/Md5/AArch64/Compress.lean`), with the arguments where AAPCS passes them.
-/

namespace VG.Proof.Md5

open Spec.Md5

open VG.Arm in
/-- 32-bit ARM contract for
`vg_md5_compress(state: *mut [u32; 4], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 8])`:
updates the MD buffer at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(16 bytes) and `scratch` (64 bytes, whose contents on exit are unspecified).
These may not overlap each other, and none of them may wrap around the end of
the (32-bit) address space. The pointers and `n` are public; the MD buffer
and the blocks are secret. -/
def compressArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 16⟩
    let blocks : Region := ⟨State.addr (s.gpr .r1), 64 * (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 64⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    (s.gpr .r0).toNat + 16 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + 64 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem (State.addr (s.gpr .r0)) =
      compressBlocks (stateAt s.mem (State.addr (s.gpr .r0))) s.mem (State.addr (s.gpr .r1))
        (s.gpr .r2).toNat
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

open VG.Arm in
/-- The 64-bit `count` argument of `update`/`finalize`, in `r2:r3` (AAPCS: the
low word in `r2`). -/
def countArm (s : Arm.State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

open VG.Arm in
/-- 32-bit ARM contract for `vg_md5_init(state: *mut [u8; 80])`: makes the
streaming state at `state` represent the empty message.

The code may write `state` (80 bytes), which may not wrap around the end of
the (32-bit) address space. The pointer is public. -/
def initArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 80⟩
    s.rd = [] ∧ s.wr = [state] ∧ (s.gpr .r0).toNat + 80 ≤ 2 ^ 32
  post s s' := Repr s'.mem (State.addr (s.gpr .r0)) []
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0

open VG.Arm in
/-- 32-bit ARM contract for
`vg_md5_update(state: *mut [u8; 80], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 14])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), then afterwards it represents `m` followed by the `len` bytes at
`data`.

Under AAPCS, `state` is in `r0`, `count` in `r2:r3`, and `data`, `len` and
`scratch` are the stack arguments 0, 1 and 2. The code may read those
arguments (12 bytes at `sp`) and `data` (`len` bytes), and read and write
`state` (80 bytes) and `scratch` (112 bytes, whose contents on exit are
unspecified). The writable buffers may not overlap each other, the data or
the arguments; the data may not overlap them either; and nothing may wrap
around the end of the (32-bit) address space. `sp`, the pointers, `count`
and `len` are public; the state and the data are secret. -/
def updateArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 80⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 2), 112⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 80 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
    (stackArg s 2).toNat + 112 ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ m, Repr s.mem (State.addr (s.gpr .r0)) m → countArm s = BitVec.ofNat 64 m.length →
    Repr s'.mem (State.addr (s.gpr .r0))
      (m ++ bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

open VG.Arm in
/-- 32-bit ARM contract for
`vg_md5_finalize(state: *mut [u8; 80], count: u64, out: *mut [u8; 16], scratch: *mut [u64; 14])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), writes the MD5 digest of `m` to `out`.

Under AAPCS, `state` is in `r0`, `count` in `r2:r3`, and `out` and `scratch`
are the stack arguments 0 and 1. The code may read those arguments (8 bytes
at `sp`), and read and write `state` (80 bytes, whose contents on exit are
unspecified), `out` (16 bytes) and `scratch` (112 bytes, whose contents on
exit are unspecified). These may not overlap each other or the arguments,
and nothing may wrap around the end of the (32-bit) address space. `sp`, the
pointers and `count` are public; the state is secret. -/
def finalizeArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 80⟩
    let out : Region := ⟨State.addr (stackArg s 0), 16⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 112⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 80 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 16 ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 112 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ m, Repr s.mem (State.addr (s.gpr .r0)) m → countArm s = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (State.addr (stackArg s 0)) 16 = Spec.Md5.hash m
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.Md5


namespace VG.Proof.Md5.Arm

open VG VG.Arm VG.Impl.Md5.Arm
open VG.Spec.Md5 (HashValue Word Block stateAt blockAt compressBlocks compress parseBlock)

/-! ## Addresses and regions -/

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem contains_sub {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64)
    {a : Addr} (ha : a = base + BitVec.ofNat 64 off) : (⟨base, len⟩ : Region).Contains a n := by
  subst ha; exact contains_offset h ho

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev bp : BitVec 32 := s₀.gpr .r1
abbrev nb : Nat := (s₀.gpr .r2).toNat
abbrev scr : BitVec 32 := s₀.gpr .r3
abbrev stR : Region := ⟨State.addr (st s₀), 16⟩
abbrev blR : Region := ⟨State.addr (bp s₀), 64 * nb s₀⟩
abbrev scrR : Region := ⟨State.addr (scr s₀), 64⟩
abbrev H₀ : HashValue := stateAt s₀.mem (State.addr (st s₀))

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (State.addr (bp s₀) + BitVec.ofNat 64 (64 * i))

/-- The address of word `k` of the MD buffer. -/
abbrev stAddr (k : Nat) : Addr := State.addr (st s₀ + BitVec.ofNat 32 (4 * k))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  st_fits : (st s₀).toNat + 16 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 64 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 64 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Md5.compressArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem stAddr_eq {k : Nat} (hk : k < 4) :
    stAddr s₀ k = State.addr (st s₀) + BitVec.ofNat 64 (4 * k) :=
  addr_add (by have := h.st_fits; omega)

theorem blkAddr_eq {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t)) =
      State.addr (bp s₀) + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) := by
  have := h.blk_fits
  rw [addr_add (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (bp s₀).isLt; omega),
    addr_add (by omega)]

theorem in_state {k : Nat} (hk : k < 4) : InRegions (s₀.rd ++ s₀.wr) (stAddr s₀ k) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_sub (by omega) (by omega) (h.stAddr_eq hk)⟩

theorem out_state {k : Nat} (hk : k < 4) : InRegions s₀.wr (stAddr s₀ k) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_sub (by omega) (by omega) (h.stAddr_eq hk)⟩

theorem in_save {d : Nat} (hd : d + 4 ≤ 64) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (scr s₀) + BitVec.ofNat 64 d) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset hd (by omega)⟩

theorem out_save {d : Nat} (hd : d + 4 ≤ 64) : InRegions s₀.wr (State.addr (scr s₀) + BitVec.ofNat 64 d) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset hd (by omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 4 := by
  have := h.blk_fits
  rw [h.blkAddr_eq hi ht, Offset.add_ofNat_add_ofNat]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 4) (hk : k < 4) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofNat 64 (4 * j)) 4 (p + BitVec.ofNat 64 (4 * k)) 4 :=
  Offset.sep p (by omega) (by omega) (by omega)

/-- Reading word `j` of the MD buffer after writing word `k`. -/
theorem readW_writeW_word {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {j k : Nat} (hj : j < 4)
    (hk : k < 4) (h : j ≠ k) :
    (m.writeW (stAddr s₀ k) v).readW (stAddr s₀ j) 32 = m.readW (stAddr s₀ j) 32 := by
  rw [hp.stAddr_eq hj, hp.stAddr_eq hk]
  exact Mem.readW_writeW_sep (word_sep _ hj hk h) (by decide)

theorem stateAt_eq {m : Mem} {s₀ : State} (hp : Pre s₀) {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 4) → m.readW (stAddr s₀ k) 32 = v[k]) :
    stateAt m (State.addr (st s₀)) = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← hp.stAddr_eq hk]; exact h k hk

theorem stateAt_get {s₀ : State} (hp : Pre s₀) (m : Mem) {k : Nat} (hk : k < 4) :
    (stateAt m (State.addr (st s₀)))[k] = m.readW (stAddr s₀ k) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, hp.stAddr_eq hk]

/-! ## The loop invariant -/

/-- The callee-saved registers we use are saved in the scratch buffer. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (State.addr (scr s₀)) s₀.gpr saved

theorem saved_slots : Spill.Slots 0 24 saved := by decide

/-- The registers the code never writes. -/
def keptRegs : List Reg := [.r0, .r3, .r10, .r11, .lr]

theorem keptRegs_pub : ∀ r ∈ keptRegs, r ∈ pubRegs := by decide

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  kept : ∀ r ∈ keptRegs, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (State.addr (st s₀)) =
    compressBlocks (H₀ s₀) s₀.mem (State.addr (bp s₀)) i
  saved : Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  r1 : s.gpr .r1 = blkAddr s₀ i
  r2 : s.gpr .r2 = BitVec.ofNat 32 (nb s₀ - i)

theorem Common.r0 {s₀ : State} {i : Nat} {s : State} (h : Common s₀ i s) : s.gpr .r0 = st s₀ :=
  h.kept .r0 (by decide)

theorem Common.r3 {s₀ : State} {i : Nat} {s : State} (h : Common s₀ i s) : s.gpr .r3 = scr s₀ :=
  h.kept .r3 (by decide)

/-! ## One block -/

theorem load_eq : load = [
    .ldr .r4 .r0 (4 * 0), .ldr .r5 .r0 (4 * 1), .ldr .r6 .r0 (4 * 2), .ldr .r7 .r0 (4 * 3),
    .movw .r8 (ones.extractLsb' 0 16), .movt .r8 (ones.extractLsb' 16 16)] := by
  decide

theorem update_eq : update ++ advance = [
    .ldr .r12 .r0 (4 * 0), .dp .add .r4 .r4 (.reg .r12), .str .r4 .r0 (4 * 0),
    .ldr .r12 .r0 (4 * 1), .dp .add .r5 .r5 (.reg .r12), .str .r5 .r0 (4 * 1),
    .ldr .r12 .r0 (4 * 2), .dp .add .r6 .r6 (.reg .r12), .str .r6 .r0 (4 * 2),
    .ldr .r12 .r0 (4 * 3), .dp .add .r7 .r7 (.reg .r12), .str .r7 .r0 (4 * 3),
    .dp .add .r1 .r1 (.imm 64), .subs .r2 .r2 (.imm 1)] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .r4 = v[0] ∧ s.gpr .r5 = v[1] ∧ s.gpr .r6 = v[2] ∧ s.gpr .r7 = v[3] := Iff.rfl

/-- The registers `load` does not write. -/
def loadKept : List Reg := [.r0, .r1, .r2, .r3, .r10, .r11, .lr]

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr0 : s.gpr .r0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (State.addr (st s₀))) ∧ s₁.gpr Ones = ones ∧
      (∀ r ∈ loadKept, s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 4 →
      InRegions (s.rd ++ s.wr) (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide)
  apply WP.of_runBlock
  rw [load_eq]
  simp (config := {decide := true}) only [vars0, Ones, runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, State.load32,
    hr0, h0, h1, h2, h3, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  simp only [stateAt_get hp _ (show 0 < 4 by decide), stateAt_get hp _ (show 1 < 4 by decide),
    stateAt_get hp _ (show 2 < 4 by decide), stateAt_get hp _ (show 3 < 4 by decide), movw_movt]
  simp (config := {decide := true}) [loadKept]

/-- Four words written in order to the MD buffer. -/
def writeState (s₀ : State) (m : Mem) (v : HashValue) : Mem :=
  ((((m.writeW (stAddr s₀ 0) v[0]).writeW (stAddr s₀ 1) v[1]).writeW (stAddr s₀ 2) v[2]).writeW
    (stAddr s₀ 3) v[3])

set_option simprocs false in
theorem stateAt_writeState {s₀ : State} (hp : Pre s₀) (m : Mem) (v : HashValue) :
    stateAt (writeState s₀ m v) (State.addr (st s₀)) = v := by
  apply stateAt_eq hp
  intro k hk
  simp only [writeState]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_word hp]

theorem frame_writeState {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Frame [stR s₀] m m')
    (v : HashValue) : Frame [stR s₀] m (writeState s₀ m' v) := by
  have c : ∀ k, k < 4 → (stR s₀).Contains (stAddr s₀ k) (32 / 8) :=
    fun k hk => contains_sub (by omega) (by omega) (hp.stAddr_eq hk)
  simp only [writeState]
  refine (((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _ (c 3 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hr0 : s.gpr .r0 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 4) → s.mem.readW (stAddr s₀ k) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s₀ s.mem (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .r1 = s.gpr .r1 + 64 ∧ s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧
      (∀ r ∈ keptRegs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 4 →
      InRegions (s.rd ++ s.wr) (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 4 → InRegions s.wr (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
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
    runBlock_nil, exec, Op2.eval, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    State.load32, State.store32, subFlags, hr0,
    i0, i1, i2, i3, o0, o1, o2, o3,
    readW_writeW_word hp,
    m0, m1, m2, m3, v0, v1, v2, v3, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  and_intros
  · simp only [writeState, Vector.getElem_zipWith]
  all_goals first
    | trivial
    | (intro r hr
       simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}))

theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [stR s₀] m m') : Saved s₀ m' :=
  h.frame saved_slots hf fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Region.Disjoint.sub_left hp.st_scr.symm (Offset.sub_base _ (by decide))

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (hp : Pre s₀) {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    s₀.mem.readW (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 32 = blk s₀ i ⟨t, ht⟩ := by
  rw [hp.blkAddr_eq hi ht, readW_bytes]
  simp only [blk, blockAt, parseBlock, Offset.add_ofNat_add_one, Nat.add_assoc, Nat.reduceAdd]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.r0 hL.rd hL.wr)
    fun s₁ ⟨hv₁, hones₁, hkept₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hX : ∀ t (ht : t < 16),
      s₁.mem.readW (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 32 = blk s₀ i ⟨t, ht⟩ := by
    intro t ht
    rw [hm₁, hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩)
      (by decide)]
    exact blk_word hp hi ht
  have hr1₁ : s₁.gpr .r1 = blkAddr s₀ i := (hkept₁ .r1 (by decide)).trans hL.r1
  refine WP.seq (WP.mono (steps_ok _ (blk s₀ i) _ s₁ hr1₁ hones₁
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hX hv₁ 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have kept₂ : ∀ r ∈ loadKept, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r (by revert r hr; decide), hkept₁ r hr]
  have hr0₂ : s₂.gpr .r0 = st s₀ := by rw [kept₂ .r0 (by decide), hL.r0]
  refine WP.mono (update_ok hp _ (stateAt s.mem (State.addr (st s₀))) hR.vars hr0₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.mem, hm₁, stateAt_get hp _ hk]
  obtain ⟨hm₃, hr1₃, hr2₃, hz₃, hkept₃, hrd₃, hwr₃⟩ := h₃
  have hnb : nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  have hr2 : s₂.gpr .r2 - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [kept₂ .r2 (by decide), hL.r2]
    rw [show (1 : BitVec _) = BitVec.ofNat _ 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [hm₃, hR.mem, hm₁]
    exact (frame_writeState hp (Frame.refl _ _) _).sub fun r hr =>
      ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨fun r hr => ?_, by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr],
      hframe, ?_, ?_⟩
    · rw [hkept₃ r hr, kept₂ r (by revert r hr; decide), hL.kept r hr]
    · rw [hm₃, stateAt_writeState hp, compressBlocks_succ, ← hL.state]
      rfl
    · rw [hm₃]
      refine saved_frame hp ?_ (frame_writeState hp (Frame.refl _ _) _)
      rw [hR.mem, hm₁]; exact hL.saved
  have hev : eval .ne s₃ = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hz₃, hr2]
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon _ rfl with r1 := ?_, r2 := ?_ }⟩
    · rw [hr1₃, kept₂ .r1 (by decide), hL.r1]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec _) = BitVec.ofNat _ 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hr2₃, hr2]

/-! ## Prologue and epilogue -/

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (State.addr (scr s₀)) s₀.gpr saved

theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save ++ ([.cmp .r2 (.imm 0)] : List Instr))) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.z = (s₀.gpr .r2 - 0 == 0) :=
  Spill.save_slots_ok saved_slots (Nat.le_trans (Nat.add_le_add_left (by decide : 24 ≤ 64) _) hp.scr_fits)
    (fun _ _ hd => hp.out_save (by omega)) (WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩⟩)

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := Spill.saveMem_saved _ _ _ _ saved_slots

theorem saveMem_frame (s₀ : State) : Frame [scrR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame _ _ _ (by decide) saved (by decide)

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hg : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) : Common s₀ 0 s₁ := by
  refine ⟨fun r _ => by rw [hg], hrd, hwr, ?_, ?_, by rw [hm]; exact saveMem_saved s₀⟩
  · rw [hm]; exact (saveMem_frame s₀).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq hp
    intro k hk
    rw [(saveMem_frame s₀).readW (contains_sub (len := 16) (off := 4 * k) (by omega) (by omega)
      (hp.stAddr_eq hk))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get hp _ hk]
    rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Md5.compressArm.post s₀ s' := by
  rw [restore, ← List.append_nil (saved.map _)]
  refine Spill.restore_slots_ok saved_slots (by decide) (g := s₀.gpr) (by rw [hc.r3]; have := hp.scr_fits; omega)
    (fun _ _ hd => by rw [hc.rd, hc.wr, hc.r3]; exact hp.in_save (by omega)) (by rw [hc.r3]; exact hc.saved)
    fun s' hs ho hm _ _ _ => WP.block_nil ⟨fun r hr => ?_, (congrArg (stateAt · _) hm).trans hc.state⟩
  by_cases h : r ∈ saved.map Prod.fst
  · exact Spill.restored_reg hs h
  · have hk : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → r ∈ keptRegs := by decide
    rw [ho r h]; exact hc.kept r (hk r hr h)

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Md5.compressArm.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  have hc₀ := common_zero hp hg hrd hwr hm
  refine WP.ite (s₀.gpr .r2 - 0 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
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
        r1 := by rw [hg]; simp [blkAddr]
        r2 := by rw [hg]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 16⟩, ⟨0x3000, 64⟩]

theorem compress_verified :
    Verified Arm.target Impl.Md5.Arm.compress Proof.Md5.compressArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_
      (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Md5.Arm
