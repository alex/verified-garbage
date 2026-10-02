import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Sha512.Arm.Rounds
import VerifiedGarbage.Impl.Sha3.Arm
import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Impl.Sha3.Arm.Stream

section

/-!
# SHA-3: the 32-bit ARM contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`), with the arguments where AAPCS passes them.

The return address is in `lr`, which the target's calling convention
requires to be preserved (`VG.Arm.abiPreserved`); the streaming functions
save it in their scratch space around their calls of the permutation, so
they use no stack.
-/

namespace VG.Proof.Sha3

open Spec.Sha3

open Arm in
/-- 32-bit ARM contract for
`vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut [u64; 64])`: applies
Keccak-f[1600] to the state at `state`.

The code may read and write `state` (200 bytes) and `scratch` (512 bytes,
whose contents on exit are unspecified), which may not overlap or wrap
around the end of the (32-bit) address space. The pointers are public; the
state is secret. -/
def permuteArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let scratch : Region := ⟨State.addr (s.gpr .r1), 512⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch ∧
    (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 512 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem (State.addr (s.gpr .r0)) = keccakF (stateAt s.mem (State.addr (s.gpr .r0)))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

open Arm in
/-- 32-bit ARM contract for `vg_keccak_absorb(state = r0, rate = r1,
pos = r2, data = r3, len = [sp], scratch = [sp, #4]) -> r0`: absorbs `data`
into the streaming state (`Repr`) and returns the new position in the
block.

The code may read the arguments on the stack (8 bytes at `sp`) and `data`,
and read and write `state` (200 bytes) and `scratch` (640 bytes). The
writable buffers may not overlap each other, the data or the arguments, and
nothing may wrap around the end of the (32-bit) address space. `rate` is one
of `rates`, and `pos < rate`. -/
def absorbArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let data : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 640 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
    (s.gpr .r1).toNat ∈ rates ∧ (s.gpr .r2).toNat < (s.gpr .r1).toNat
  post s s' :=
    (∀ msg, Repr s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat msg →
      (s.gpr .r2).toNat = msg.length % (s.gpr .r1).toNat →
      Repr s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
        (msg ++ bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)) ∧
    (s'.gpr .r0).toNat = ((s.gpr .r2).toNat + (stackArg s 0).toNat) % (s.gpr .r1).toNat
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

open Arm in
/-- 32-bit ARM contract for `vg_keccak_pad(state = r0, rate = r1, pos = r2,
suffix = r3, scratch = [sp])`: absorbs the padding (with the low byte of
`suffix`) into the streaming state.

The code may read the argument on the stack (4 bytes at `sp`), and read and
write `state` (200 bytes) and `scratch` (640 bytes), which may not overlap
each other or the argument, or wrap around the end of the (32-bit) address
space. `rate` is one of `rates`, and `pos < rate`. -/
def padArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [args] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 640 ≤ 2 ^ 32 ∧
    s.sp.toNat + 4 ≤ 2 ^ 32 ∧
    (s.gpr .r1).toNat ∈ rates ∧ (s.gpr .r2).toNat < (s.gpr .r1).toNat
  post s s' := ∀ msg, Repr s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat msg →
    (s.gpr .r2).toNat = msg.length % (s.gpr .r1).toNat →
    stateAt s'.mem (State.addr (s.gpr .r0)) =
      absorb (s.gpr .r1).toNat (pad (s.gpr .r1).toNat ((s.gpr .r3).setWidth 8) msg)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

open Arm in
/-- 32-bit ARM contract for `vg_keccak_squeeze(state = r0, rate = r1,
pos = r2, out = r3, outlen = [sp], scratch = [sp, #4]) -> r0`: writes
`outlen` bytes of output from byte `pos` on to `out`, and returns the
position after them, leaving a state from which the output continues.

The code may read the arguments on the stack (8 bytes at `sp`), and read
and write `state` (200 bytes), `out` (`outlen` bytes) and `scratch` (640
bytes), which may not overlap each other or the arguments, or wrap around
the end of the (32-bit) address space. `rate` is one of `rates`, and
`pos ≤ rate`. -/
def squeezeArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let out : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 640 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
    (s.gpr .r1).toNat ∈ rates ∧ (s.gpr .r2).toNat ≤ (s.gpr .r1).toNat
  post s s' :=
    bytesAt s'.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat =
      squeezeFrom (s.gpr .r1).toNat (stateAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r2).toNat
        (stackArg s 0).toNat ∧
    (s'.gpr .r0).toNat ≤ (s.gpr .r1).toNat ∧
    ∀ d, squeezeFrom (s.gpr .r1).toNat (stateAt s'.mem (State.addr (s.gpr .r0))) (s'.gpr .r0).toNat d =
      squeezeFrom (s.gpr .r1).toNat (stateAt s.mem (State.addr (s.gpr .r0)))
        ((s.gpr .r2).toNat + (stackArg s 0).toNat) d
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.Sha3

end

section

/-!
# Keccak-f[1600] on ARMv7: one round

One round (`round src dst`) from the state at `src` to the state at `dst`,
lane by lane (`Proof.Sha3.out`), each lane a pair of 32-bit halves (as the
SHA-512 proof handles them: `VG.Proof.Sha512.Arm`), proved once for both of
the rounds of an iteration (`src`, `dst` being `r0`, `r1` or `r1`, `r0`).
-/

namespace VG.Proof.Sha3.Arm

open VG VG.Arm VG.Impl.Sha3.Arm
open VG.Impl.Sha3 (piSrc rhoOff)
open VG.Impl.Sha512.Arm (lo hi ld st sig Op)
open VG.Proof.Sha512.Arm (Only Wrote Pair rd64 write64 A Reg64 wp_ld wp_st wp_sig wp_eor mem_rd
  A_eq rd64_write64_self rd64_write64_ne frame_write64 contains_A lo_xor hi_xor lo_and hi_and
  lo_rd64 hi_rd64 evalOps)
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_and wp_ldr wp_str wp_add op2_reg op2_imm)
open VG.Proof.Sha3 (C D B out outState)

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

/-! ## Registers -/

/-- The pointer registers, which a round never writes. -/
def Ptr (r : Reg) : Prop := r ∈ [Reg.r0, .r1]

/-- The registers the columns write. -/
def colRegs : List Reg := [cl 0, ch 0, cl 1, ch 1, cl 2, ch 2, cl 3, ch 3, cl 4, ch 4, T1]

theorem cl_inj : ∀ x < 5, ∀ x' < 5, cl x = cl x' → x = x' := by decide
theorem ch_inj : ∀ x < 5, ∀ x' < 5, ch x = ch x' → x = x' := by decide
theorem cl_ch : ∀ x < 5, ∀ x' < 5, cl x ≠ ch x' := by decide
theorem cl_T : ∀ x < 5, cl x ≠ T1 ∧ cl x ≠ T2 ∧ ch x ≠ T1 ∧ ch x ≠ T2 := by decide
theorem T12 : T1 ≠ T2 := by decide
theorem ptr_cl : ∀ r ∈ [Reg.r0, .r1], ∀ x < 5, cl x ≠ r ∧ ch x ≠ r := by decide
theorem ptr_T : ∀ r ∈ [Reg.r0, .r1], T1 ≠ r ∧ T2 ≠ r := by decide
theorem ptr_col : ∀ r ∈ [Reg.r0, .r1], r ∉ colRegs := by decide
theorem col_mono : ∀ x < 5, ∀ r ∈ colRegs ++ [cl x, ch x, T1], r ∈ colRegs := by decide

/-- The registers the planes write. -/
def bRegs : List Reg := [cl 0, ch 0, cl 1, ch 1, cl 2, ch 2, cl 3, ch 3, cl 4, ch 4, T1, T2]

theorem ptr_b : ∀ r ∈ [Reg.r0, .r1], r ∉ bRegs := by decide
theorem b_mono : ∀ x < 5, ∀ r ∈ bRegs ++ [T1, T2, cl x, ch x], r ∈ bRegs := by decide

theorem Ptr.cl {r : Reg} (h : Ptr r) {x : Nat} (hx : x < 5) : cl x ≠ r ∧ ch x ≠ r := ptr_cl r h x hx

theorem Ptr.T {r : Reg} (h : Ptr r) : T1 ≠ r ∧ T2 ≠ r := ptr_T r h

theorem cl_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x' ≠ x) : cl x' ≠ cl x :=
  fun e => h (cl_inj x' hx' x hx e)

theorem ch_ne {x x' : Nat} (hx : x < 5) (hx' : x' < 5) (h : x' ≠ x) : ch x' ≠ ch x :=
  fun e => h (ch_inj x' hx' x hx e)

theorem nm2 {r a b : Reg} (h₁ : r ≠ a) (h₂ : r ≠ b) : r ∉ [a, b] := by simp [h₁, h₂]
theorem nm3 {r a b c : Reg} (h₁ : r ≠ a) (h₂ : r ≠ b) (h₃ : r ≠ c) : r ∉ [a, b, c] := by
  simp [h₁, h₂, h₃]
theorem nm4 {r a b c d : Reg} (h₁ : r ≠ a) (h₂ : r ≠ b) (h₃ : r ≠ c) (h₄ : r ≠ d) :
    r ∉ [a, b, c, d] := by simp [h₁, h₂, h₃, h₄]

/-! ## States in memory -/

/-- The state at `b` holds `K`, lane `i` as the pair of words at `b + 8i`. -/
def Lanes32 (m : Mem) (b : BitVec 32) (K : KState) : Prop := ∀ i < 25, rd64 m b (8 * i) = K[i]!

/-- The 32-bit region of `n` bytes at `b`. -/
abbrev regR (b : BitVec 32) (n : Nat) : Region := ⟨State.addr b, n⟩

/-- Where a round reads and writes: the state at `S`, the pointer at
`Sc + rcPtr` to the round constant, the round constant at `P`, and the state
at `Dd`, which overlaps none of them. -/
structure Env (wr : List Region) (S Dd Sc P : BitVec 32) : Prop where
  fitS : S.toNat + 200 ≤ 2 ^ 32
  fitD : Dd.toNat + 200 ≤ 2 ^ 32
  wS : Reg64 wr S 200
  wD : Reg64 wr Dd 200
  ptr_in : InRegions wr (A Sc rcPtr) 4
  rc_in : ∀ o, o = 0 ∨ o = 4 → InRegions wr (A P o) 4
  src_dst : Region.Disjoint (regR S 200) (regR Dd 200)
  ptr_dst : Region.Disjoint ⟨A Sc rcPtr, 4⟩ (regR Dd 200)
  rc_dst : ∀ o, o = 0 ∨ o = 4 → Region.Disjoint ⟨A P o, 4⟩ (regR Dd 200)

theorem Env.src {wr : List Region} {S Dd Sc P : BitVec 32} (E : Env wr S Dd Sc P) {m m' : Mem}
    (hf : Frame [regR Dd 200] m m') {i : Nat} (hi : i < 25) : rd64 m' S (8 * i) = rd64 m S (8 * i) :=
  VG.Proof.Sha512.Arm.rd64_frame hf (by simpa using E.src_dst) E.fitS (by omega)

theorem Env.ptr {wr : List Region} {S Dd Sc P : BitVec 32} (E : Env wr S Dd Sc P) {m m' : Mem}
    (hf : Frame [regR Dd 200] m m') : m'.readW (A Sc rcPtr) 32 = m.readW (A Sc rcPtr) 32 :=
  hf.readW (Region.contains_self _ _) (by simpa using E.ptr_dst) (by decide)

theorem Env.rc {wr : List Region} {S Dd Sc P : BitVec 32} (E : Env wr S Dd Sc P) {m m' : Mem}
    (hf : Frame [regR Dd 200] m m') {o : Nat} (ho : o = 0 ∨ o = 4) :
    m'.readW (A P o) 32 = m.readW (A P o) 32 :=
  hf.readW (Region.contains_self _ _) (by simpa using E.rc_dst o ho) (by decide)

theorem Env.dst_contains {wr : List Region} {S Dd Sc P : BitVec 32} (E : Env wr S Dd Sc P) {o : Nat}
    (ho : o + 4 ≤ 200) : (regR Dd 200).Contains (A Dd o) (32 / 8) :=
  contains_A E.fitD ho

/-! ## θ -/

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- `(l, h) ^=` the lane at `[b, #off]`. -/
theorem wp_ldx {l h b : Reg} {B' : BitVec 32} {off : Nat} {v : Lane} (hlT : l ≠ T1) (hhT : h ≠ T1)
    (hbT : b ≠ T1) (hbl : b ≠ l) (hlh : l ≠ h) (ho : off + 4 < 4096) (hb : s.gpr b = B')
    (hi : InRegions s.wr (A B' off) 4) (hi' : InRegions s.wr (A B' (off + 4)) 4) (hp : Pair s l h v)
    (k : ∀ s', Only [T1, l, h] s s' → Pair s' l h (v ^^^ rd64 s.mem B' off) → WP isa (.block rest) s' Q) :
    WP isa (.block (ldx l h b off ++ rest)) s Q := by
  simp only [ldx, List.cons_append, List.nil_append]
  refine wp_ldr (by omega) (by rw [hb]) (mem_rd hi) fun s₁ u₁ => ?_
  refine wp_eor (op2_reg _ _) fun s₂ u₂ => ?_
  refine wp_ldr ho (by rw [u₂.other b hbl, u₁.other b hbT, hb])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact mem_rd hi') fun s₃ u₃ => ?_
  refine wp_eor (op2_reg _ _) fun s₄ u₄ => k s₄ ((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans
    (Only.of_upd u₃)).trans (Only.of_upd u₄) |>.mono (by simp)) ⟨?_, ?_⟩
  · rw [u₄.other l hlh, u₃.other l hlT, u₂.gpr, u₁.other l hlT, u₁.gpr, hp.1, lo_xor, lo_rd64]
  · rw [u₄.gpr, u₃.gpr, u₃.other h hhT, u₂.other h (Ne.symm hlh), u₁.other h hhT,
      u₂.mem, u₁.mem, hp.2, hi_xor, hi_rd64]

theorem wp_ldx' {l h b : Reg} {B' : BitVec 32} {off : Nat} {v : Lane} (hlT : l ≠ T1) (hhT : h ≠ T1)
    (hbT : b ≠ T1) (hbl : b ≠ l) (hlh : l ≠ h) (ho : off + 4 < 4096) (hb : s.gpr b = B')
    (hi : InRegions s.wr (A B' off) 4) (hi' : InRegions s.wr (A B' (off + 4)) 4) (hp : Pair s l h v)
    (k : ∀ s', Only [T1, l, h] s s' → Pair s' l h (v ^^^ rd64 s.mem B' off) → Q s') :
    WP isa (.block (ldx l h b off)) s Q := by
  rw [← List.append_nil (ldx l h b off)]
  exact wp_ldx hlT hhT hbT hbl hlh ho hb hi hi' hp fun s' o p => WP.block_nil (k s' o p)

end

theorem column_ok (x : Nat) (hx : x < 5) {src : Reg} (hsrc : Ptr src) {S : BitVec 32} {K : KState}
    (s : State) (h0 : s.gpr src = S) (hR : Reg64 s.wr S 200) (hK : Lanes32 s.mem S K) :
    WP isa (.block (column src x)) s fun s' =>
      Only [cl x, ch x, T1] s s' ∧ Pair s' (cl x) (ch x) (C K x) := by
  obtain ⟨hlT, -, hhT, -⟩ := cl_T x hx
  obtain ⟨hsl, hsh⟩ := hsrc.cl hx
  have hsT := hsrc.T.1
  have hlh : cl x ≠ ch x := cl_ch x hx x hx
  unfold column
  refine wp_ld hsl hlh (by omega) h0 (hR _ (by omega)).1 (hR _ (by omega)).2 fun s₁ o₁ p₁ => ?_
  have g : ∀ t : State, Only [cl x, ch x, T1] s t → t.gpr src = S ∧ t.wr = s.wr ∧ t.mem = s.mem :=
    fun t o => ⟨by rw [o.gpr src (nm3 hsl.symm hsh.symm hsT.symm), h0], o.wr, o.mem⟩
  have o₁' : Only [cl x, ch x, T1] s s₁ := o₁.mono (by simp)
  obtain ⟨a₁, w₁, m₁⟩ := g s₁ o₁'
  refine wp_ldx hlT hhT hsT.symm hsl.symm hlh (by omega) a₁ (by rw [w₁]; exact (hR _ (by omega)).1)
    (by rw [w₁]; exact (hR _ (by omega)).2) p₁ fun s₂ o₂ p₂ => ?_
  have o₂' : Only [cl x, ch x, T1] s s₂ := (o₁'.trans o₂).mono (by simp)
  obtain ⟨a₂, w₂, m₂⟩ := g s₂ o₂'
  refine wp_ldx hlT hhT hsT.symm hsl.symm hlh (by omega) a₂ (by rw [w₂]; exact (hR _ (by omega)).1)
    (by rw [w₂]; exact (hR _ (by omega)).2) p₂ fun s₃ o₃ p₃ => ?_
  have o₃' : Only [cl x, ch x, T1] s s₃ := (o₂'.trans o₃).mono (by simp)
  obtain ⟨a₃, w₃, m₃⟩ := g s₃ o₃'
  refine wp_ldx hlT hhT hsT.symm hsl.symm hlh (by omega) a₃ (by rw [w₃]; exact (hR _ (by omega)).1)
    (by rw [w₃]; exact (hR _ (by omega)).2) p₃ fun s₄ o₄ p₄ => ?_
  have o₄' : Only [cl x, ch x, T1] s s₄ := (o₃'.trans o₄).mono (by simp)
  obtain ⟨a₄, w₄, m₄⟩ := g s₄ o₄'
  refine wp_ldx' hlT hhT hsT.symm hsl.symm hlh (by omega) a₄ (by rw [w₄]; exact (hR _ (by omega)).1)
    (by rw [w₄]; exact (hR _ (by omega)).2) p₄ fun s₅ o₅ p₅ => ⟨(o₄'.trans o₅).mono (by simp), ?_⟩
  rw [m₁, m₂, m₃, m₄, hK x (by omega), hK (x + 5) (by omega), hK (x + 10) (by omega),
    hK (x + 15) (by omega), hK (x + 20) (by omega)] at p₅
  exact p₅

/-- After the first `k` columns. -/
def ColInv (s₀ : State) (K : KState) (k : Nat) (s : State) : Prop :=
  Only colRegs s₀ s ∧ ∀ x < k, Pair s (cl x) (ch x) (C K x)

theorem columns_ok {src : Reg} (hsrc : Ptr src) {S : BitVec 32} {K : KState} (s₀ : State)
    (h0 : s₀.gpr src = S) (hR : Reg64 s₀.wr S 200) (hK : Lanes32 s₀.mem S K) :
    WP isa (.block ((List.range 5).flatMap (column src))) s₀ (ColInv s₀ K 5) := by
  refine wp_range_flatMap (M := isa) (ColInv s₀ K) (fun x s hx ⟨ho, hc⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Only.refl _ _, fun _ h => absurd h (by omega)⟩
  refine WP.mono (column_ok x hx hsrc (K := K) s (by rw [ho.gpr src (ptr_col src hsrc), h0])
    (by rw [ho.wr]; exact hR) (by rw [ho.mem]; exact hK)) fun s' ⟨o, p⟩ =>
      ⟨(ho.trans o).mono (col_mono x hx), fun x' hx' => ?_⟩
  by_cases e : x' = x
  · subst e; exact p
  · have hx'5 : x' < 5 := by omega
    exact (hc x' (by omega)).of_only o
      (nm3 (cl_ne hx hx'5 e) (cl_ch x' hx'5 x hx) (cl_T x' hx'5).1)
      (nm3 (fun h => cl_ch x hx x' hx'5 h.symm) (ch_ne hx hx'5 e) (cl_T x' hx'5).2.2.1)

/-! ## D -/

theorem evalOps_rotr (v : Lane) (n : Nat) : evalOps v [.rotr n] = v.rotateRight n := by
  simp [evalOps, VG.Impl.Sha512.Arm.Op.eval]

theorem dOff_lt (x : Nat) (hx : x < 5) : dOff x + 8 ≤ 200 := by simp only [dOff]; omega

theorem dcol_ok (x : Nat) (hx : x < 5) {dst : Reg} (hdst : Ptr dst) {Dd : BitVec 32} {K : KState}
    (s : State) (hd : s.gpr dst = Dd) (hR : Reg64 s.wr Dd 200)
    (hc : ∀ x' < 5, Pair s (cl x') (ch x') (C K x')) :
    WP isa (.block (dcol dst x)) s fun s' => Wrote [T1, T2] s s' (write64 s.mem Dd (dOff x) (D K x)) := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h4 : (x + 4) % 5 < 5 := Nat.mod_lt _ (by omega)
  obtain ⟨l1T1, l1T2, h1T1, h1T2⟩ := cl_T _ h1
  obtain ⟨l4T1, l4T2, h4T1, h4T2⟩ := cl_T _ h4
  have hdo := dOff_lt x hx
  unfold dcol
  refine wp_sig (by simp) (by decide) T12 l1T1 h1T1 l1T2 h1T2 (hc _ h1) fun s₁ o₁ p₁ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_eor (op2_reg _ _) fun s₂ u₂ => wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  rw [← List.append_nil (st T1 T2 dst (dOff x))]
  have hd₃ : s₃.gpr dst = Dd := by
    rw [u₃.other dst hdst.T.2.symm, u₂.other dst hdst.T.1.symm,
      o₁.gpr dst (nm2 hdst.T.1.symm hdst.T.2.symm), hd]
  have hw₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, o₁.wr]
  refine wp_st (x := D K x) (by omega) hd₃ ⟨?_, ?_⟩ (by rw [hw₃]; exact (hR _ hdo).1)
    (by rw [hw₃]; exact (hR _ hdo).2) fun s₄ u₄ => WP.block_nil ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₃.other T1 T12, u₂.gpr, p₁.1, o₁.gpr (cl _) (nm2 l4T1 l4T2), (hc _ h4).1, evalOps_rotr, D,
      lo_xor]
  · rw [u₃.gpr, u₂.other T2 T12.symm, u₂.other _ h4T1, p₁.2, o₁.gpr (ch _) (nm2 h4T1 h4T2),
      (hc _ h4).2, evalOps_rotr, D, hi_xor]
  · have ⟨a, b⟩ : r ≠ T1 ∧ r ≠ T2 := by simpa using hr
    rw [u₄.gpr, u₃.other r b, u₂.other r a, o₁.gpr r hr]
  · rw [u₄.mem, u₃.mem, u₂.mem, o₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, o₁.rd]
  · rw [u₄.wr, hw₃]
  · rw [u₄.sp, u₃.sp, u₂.sp, o₁.sp]

/-- After the first `k` of the `D[x]`. -/
structure DInv (s₀ : State) (K : KState) (Dd : BitVec 32) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [T1, T2] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [regR Dd 200] s₀.mem s.mem
  dl : ∀ x < k, rd64 s.mem Dd (dOff x) = D K x

theorem dcols_ok {dst : Reg} (hdst : Ptr dst) {Dd : BitVec 32} {K : KState} (s₀ : State)
    (hd : s₀.gpr dst = Dd) (fitD : Dd.toNat + 200 ≤ 2 ^ 32) (hR : Reg64 s₀.wr Dd 200)
    (hc : ∀ x < 5, Pair s₀ (cl x) (ch x) (C K x)) :
    WP isa (.block ((List.range 5).flatMap (dcol dst))) s₀ (DInv s₀ K Dd 5) := by
  refine wp_range_flatMap (M := isa) (DInv s₀ K Dd) (fun x s hx hI => ?_) 5 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  have hdo := dOff_lt x hx
  refine WP.mono (dcol_ok x hx hdst (K := K) s (by rw [hI.gpr dst (nm2 hdst.T.1.symm hdst.T.2.symm), hd])
    (by rw [hI.wr]; exact hR) fun x' hx' => ⟨?_, ?_⟩) fun s' w => ⟨fun r hr => by
      rw [w.gpr r hr, hI.gpr r hr], w.rd.trans hI.rd, w.wr.trans hI.wr, w.sp.trans hI.sp, ?_, ?_⟩
  · rw [hI.gpr _ (nm2 (cl_T x' hx').1 (cl_T x' hx').2.1)]; exact (hc x' hx').1
  · rw [hI.gpr _ (nm2 (cl_T x' hx').2.2.1 (cl_T x' hx').2.2.2)]; exact (hc x' hx').2
  · rw [w.mem]; exact frame_write64 hI.frame (List.mem_singleton_self _) fitD hdo _
  · intro x' hx'
    rw [w.mem]
    by_cases e : x' = x
    · subst e; exact rd64_write64_self _ _ (by omega)
    · rw [rd64_write64_ne _ _ (by omega) (by have := dOff_lt x' (by omega); omega)
        (by simp only [dOff]; omega)]
      exact hI.dl x' (by omega)

/-! ## A plane -/

theorem rhoOff_ne32 : ∀ j < 25, rhoOff j ≠ 32 := by decide

theorem laneB_ok (x y : Nat) (hx : x < 5) (_hy : y < 5) {src dst : Reg} (hsrc : Ptr src)
    (hdst : Ptr dst) {S Dd : BitVec 32} {K : KState} (s : State) (h0 : s.gpr src = S)
    (hd : s.gpr dst = Dd) (hRS : Reg64 s.wr S 200) (hRD : Reg64 s.wr Dd 200)
    (hK : Lanes32 s.mem S K) (hD : ∀ x' < 5, rd64 s.mem Dd (dOff x') = D K x') :
    WP isa (.block (laneB src dst x y)) s fun s' =>
      Only [T1, T2, cl x, ch x] s s' ∧ Pair s' (cl x) (ch x) (B K x y) := by
  have hj : piSrc x y < 25 := by simp only [piSrc]; omega
  have hk : (x + 3 * y) % 5 < 5 := Nat.mod_lt _ (by omega)
  have hko := dOff_lt _ hk
  obtain ⟨lT1, lT2, hT1, hT2⟩ := cl_T x hx
  obtain ⟨sT1, sT2⟩ := hsrc.T
  obtain ⟨dT1, dT2⟩ := hdst.T
  unfold laneB
  simp only [List.cons_append, List.nil_append]
  refine wp_ldr (a := A S (8 * piSrc x y)) (by omega) (by rw [h0]) (mem_rd (hRS _ (by omega)).1)
    fun s₁ u₁ => ?_
  refine wp_ldr (a := A Dd (dOff ((x + 3 * y) % 5))) (by omega) (by rw [u₁.other dst dT1.symm, hd])
    (by rw [u₁.rd, u₁.wr]; exact mem_rd (hRD _ hko).1) fun s₂ u₂ => ?_
  refine wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_ldr (a := A S (8 * piSrc x y + 4)) (by omega)
    (by rw [u₃.other src sT1.symm, u₂.other src sT2.symm, u₁.other src sT1.symm, h0])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact mem_rd (hRS _ (by omega)).2)
    fun s₄ u₄ => ?_
  refine wp_ldr (a := A Dd (dOff ((x + 3 * y) % 5) + 4)) (by omega)
    (by rw [u₄.other dst dT2.symm, u₃.other dst dT1.symm, u₂.other dst dT2.symm,
      u₁.other dst dT1.symm, hd])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact mem_rd (hRD _ hko).2)
    fun s₅ u₅ => ?_
  refine wp_eor (op2_reg _ _) fun s₆ u₆ => ?_
  have o₆ : Only [T1, T2, cl x, ch x] s s₆ := ((((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans
    (Only.of_upd u₃)).trans (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans (Only.of_upd u₆)).mono
    (by simp)
  have p₆ : Pair s₆ T1 T2 (K[piSrc x y]! ^^^ D K ((x + 3 * y) % 5)) := by
    constructor
    · rw [u₆.other T1 T12, u₅.other T1 lT1.symm, u₄.other T1 T12, u₃.gpr, u₂.other T1 T12, u₂.gpr,
        u₁.gpr, u₁.mem, lo_xor, ← hK _ hj, ← hD _ hk, lo_rd64, lo_rd64]
    · rw [u₆.gpr, u₅.gpr, u₅.other T2 lT2.symm, u₄.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hi_xor,
        ← hK _ hj, ← hD _ hk, hi_rd64, hi_rd64]
  unfold rot
  split
  · rename_i h
    refine wp_mov (op2_reg _ _) fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ =>
      WP.block_nil ⟨(o₆.trans (Only.of_upd u₇)).trans (Only.of_upd u₈) |>.mono (by simp), ?_, ?_⟩
    · rw [u₈.other (cl x) (cl_ch x hx x hx), u₇.gpr, p₆.1, B, Proof.Sha3.rotl, ite_eq_left_of_eq_true _ _ (eq_true h)]
    · rw [u₈.gpr, u₇.other T2 lT2.symm, p₆.2, B, Proof.Sha3.rotl, ite_eq_left_of_eq_true _ _ (eq_true h)]
  · rename_i h
    have h64 := Proof.Sha3.rhoOff_lt _ hj
    have h32 := rhoOff_ne32 _ hj
    rw [← List.append_nil (sig _ _ _ _ _)]
    refine wp_sig (by simp) (fun o ho => ?_) (cl_ch x hx x hx) lT1.symm lT2.symm hT1.symm hT2.symm p₆
      fun s₇ o₇ p₇ => WP.block_nil ⟨(o₆.trans o₇).mono (by simp), ?_⟩
    · simp only [List.mem_singleton] at ho
      subst ho
      simp only [VG.Impl.Sha512.Arm.Op.valid, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
      omega
    · rw [evalOps_rotr] at p₇
      rw [B, Proof.Sha3.rotl, ite_eq_right_of_eq_false _ _ (eq_false h)]
      exact p₇

/-- `¬b ∧ c`, as the model computes it without `bic`. -/
theorem andNot (b c : Lane) : (b ^^^ 0xffffffffffffffff) &&& c = (b &&& c) ^^^ c := by
  have e : (0xffffffffffffffff : Lane) = BitVec.allOnes 64 := by decide
  rw [e]
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_allOnes]
  cases b[i] <;> cases c[i] <;> rfl

/-- A half (`f`, `lo` or `hi`) of lane `(x, y)` of the output, from the
halves `r` of the lanes `B`. -/
theorem chiHalf_ok (x y : Nat) (hx : x < 5) (_hy : y < 5) {dst : Reg} (hdst : Ptr dst)
    (r : Nat → Reg) (hr : ∀ x' < 5, r x' ≠ T1 ∧ r x' ≠ T2) (f : Lane → BitVec 32)
    (hfx : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (hfa : ∀ a b, f (a &&& b) = f a &&& f b)
    {Dd Sc P : BitVec 32} {K : KState} {rc : Lane} {off o : Nat} (ho : o < 4096) (hoff : off < 4096)
    (s : State) (hd : s.gpr dst = Dd) (h1 : s.gpr .r1 = Sc) (hout : InRegions s.wr (A Dd o) 4)
    (hb : ∀ x' < 5, s.gpr (r x') = f (B K x' y))
    (hrc : x = 0 ∧ y = 0 → InRegions (s.rd ++ s.wr) (A Sc rcPtr) 4 ∧
      s.mem.readW (A Sc rcPtr) 32 = P ∧ InRegions (s.rd ++ s.wr) (A P off) 4 ∧
      s.mem.readW (A P off) 32 = f rc) :
    WP isa (.block (chiHalf dst r x y off o)) s fun s' =>
      Wrote [T1, T2] s s' (s.mem.writeW (A Dd o) (f (out K rc x y))) := by
  have h1' : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h2' : (x + 2) % 5 < 5 := Nat.mod_lt _ (by omega)
  unfold chiHalf
  simp only [List.cons_append, List.nil_append]
  refine wp_and (op2_reg _ _) fun s₁ u₁ => wp_eor (op2_reg _ _) fun s₂ u₂ =>
    wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  have hT : s₃.gpr T1 = f ((B K ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B K ((x + 2) % 5) y ^^^
      B K x y) := by
    rw [u₃.gpr, u₂.gpr, u₂.other (r x) (hr x hx).1, u₁.gpr, u₁.other (r ((x + 2) % 5)) (hr _ h2').1,
      u₁.other (r x) (hr x hx).1, hb _ h1', hb _ h2', hb x hx, andNot, hfx, hfx, hfa]
  have fin : ∀ s₄ : State, (∀ q, q ≠ T1 → q ≠ T2 → s₄.gpr q = s.gpr q) →
      s₄.gpr T1 = f (out K rc x y) → s₄.mem = s.mem → s₄.rd = s.rd → s₄.wr = s.wr → s₄.sp = s.sp →
      WP isa (.block [.str T1 dst o]) s₄ fun s' =>
        Wrote [T1, T2] s s' (s.mem.writeW (A Dd o) (f (out K rc x y))) :=
    fun s₄ g₄ v₄ m₄ r₄ w₄ p₄ => by
      refine wp_str ho (by rw [g₄ dst hdst.T.1.symm hdst.T.2.symm, hd]) (by rw [w₄]; exact hout)
        fun s₅ u₅ => WP.block_nil ⟨fun q hq => ?_, by rw [u₅.mem, m₄, v₄], by rw [u₅.rd, r₄],
          by rw [u₅.wr, w₄], by rw [u₅.sp, p₄]⟩
      have ⟨a, b⟩ : q ≠ T1 ∧ q ≠ T2 := by simpa using hq
      rw [u₅.gpr, g₄ q a b]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have g₃ : ∀ q, q ≠ T1 → s₃.gpr q = s.gpr q := fun q hq => by
    rw [u₃.other q hq, u₂.other q hq, u₁.other q hq]
  by_cases h0 : x = 0 ∧ y = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
    simp only [List.cons_append, List.nil_append]
    obtain ⟨i1, e1, i2, e2⟩ := hrc h0
    refine wp_ldr (a := A Sc rcPtr) (by decide) (by rw [g₃ .r1 (by decide), h1])
      (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i1) fun s₄ u₄ => ?_
    refine wp_ldr (a := A P off) hoff (by rw [u₄.gpr, m₃, e1])
      (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i2) fun s₅ u₅ => ?_
    refine wp_eor (op2_reg _ _) fun s₆ u₆ => fin s₆ (fun q a b => ?_) ?_ (by
      rw [u₆.mem, u₅.mem, u₄.mem, m₃]) (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
    · rw [u₆.other q a, u₅.other q b, u₄.other q b, g₃ q a]
    · rw [u₆.gpr, u₅.other T1 T12, u₄.other T1 T12, u₅.gpr, u₄.mem, m₃, e2, hT, ← hfx, out]
      simp only [h0, and_self, ite_true]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
    simp only [List.nil_append]
    refine fin s₃ (fun q a _ => g₃ q a) ?_ m₃ (by rw [u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₃.wr, u₂.wr, u₁.wr]) (by rw [u₃.sp, u₂.sp, u₁.sp])
    rw [hT, out]
    simp only [h0, ite_false]

theorem rc_lo {m : Mem} {P : BitVec 32} {rc : Lane} (h : rd64 m P 0 = rc) :
    m.readW (A P 0) 32 = lo rc := by rw [← h, lo_rd64]

theorem rc_hi {m : Mem} {P : BitVec 32} {rc : Lane} (h : rd64 m P 0 = rc) :
    m.readW (A P 4) 32 = hi rc := by rw [← h, hi_rd64]

theorem Env.rc64 {wr : List Region} {S Dd Sc P : BitVec 32} (E : Env wr S Dd Sc P) {m m' : Mem}
    (hf : Frame [regR Dd 200] m m') : rd64 m' P 0 = rd64 m P 0 := by
  simp only [rd64]
  rw [E.rc hf (o := 0 + 4) (.inr rfl), E.rc hf (.inl rfl)]

theorem chi_ok (x y : Nat) (hx : x < 5) (hy : y < 5) {dst : Reg} (hdst : Ptr dst)
    {S Dd Sc P : BitVec 32} {K : KState} {rc : Lane} (s : State) (E : Env s.wr S Dd Sc P)
    (hd : s.gpr dst = Dd) (h1 : s.gpr .r1 = Sc) (hP : s.mem.readW (A Sc rcPtr) 32 = P)
    (hrc : rd64 s.mem P 0 = rc) (hb : ∀ x' < 5, Pair s (cl x') (ch x') (B K x' y)) :
    WP isa (.block (chi dst x y)) s fun s' =>
      Wrote [T1, T2] s s' (write64 s.mem Dd (8 * (x + 5 * y)) (out K rc x y)) := by
  have ho : 8 * (x + 5 * y) + 8 ≤ 200 := by omega
  unfold chi
  rw [WP.block_append_iff]
  refine WP.mono (chiHalf_ok x y hx hy hdst cl (fun x' hx' => ⟨(cl_T x' hx').1, (cl_T x' hx').2.1⟩)
    lo lo_xor lo_and (by omega) (by decide) s hd h1 (E.wD _ ho).1 (fun x' hx' => (hb x' hx').1)
    (fun _ => ⟨mem_rd E.ptr_in, hP, mem_rd (E.rc_in 0 (.inl rfl)), rc_lo hrc⟩)) fun s₁ w₁ => ?_
  have hf : Frame [regR Dd 200] s.mem s₁.mem := by
    rw [w₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (E.dst_contains (by omega))
  obtain ⟨dT1, dT2⟩ := hdst.T
  refine WP.mono (chiHalf_ok x y hx hy hdst ch
    (fun x' hx' => ⟨(cl_T x' hx').2.2.1, (cl_T x' hx').2.2.2⟩) hi hi_xor hi_and (by omega) (by decide)
    s₁ (by rw [w₁.gpr dst (nm2 dT1.symm dT2.symm), hd]) (by rw [w₁.gpr .r1 (by decide), h1])
    (by rw [w₁.wr]; exact (E.wD _ ho).2)
    (fun x' hx' => by
      rw [w₁.gpr _ (nm2 (cl_T x' hx').2.2.1 (cl_T x' hx').2.2.2)]; exact (hb x' hx').2)
    (fun _ => ⟨by rw [w₁.rd, w₁.wr]; exact mem_rd E.ptr_in, by rw [E.ptr hf, hP],
      by rw [w₁.rd, w₁.wr]; exact mem_rd (E.rc_in 4 (.inr rfl)), by rw [E.rc hf (.inr rfl), rc_hi hrc]⟩))
    fun s₂ w₂ => ⟨fun q hq => by rw [w₂.gpr q hq, w₁.gpr q hq], by rw [w₂.mem, w₁.mem]; rfl,
      w₂.rd.trans w₁.rd, w₂.wr.trans w₁.wr, w₂.sp.trans w₁.sp⟩

/-- After `k` lanes of plane `y` of the output. -/
structure ChiInv (s₀ : State) (K : KState) (rc : Lane) (Dd : BitVec 32) (y k : Nat) (s : State) :
    Prop where
  gpr : ∀ q, q ∉ [T1, T2] → s.gpr q = s₀.gpr q
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [regR Dd 200] s₀.mem s.mem
  dl : y + 1 < 5 → ∀ x < 5, rd64 s.mem Dd (dOff x) = D K x
  lanes : ∀ j < 5 * y + k, rd64 s.mem Dd (8 * j) = out K rc (j % 5) (j / 5)

theorem chis_ok (y : Nat) (hy : y < 5) {dst : Reg} (hdst : Ptr dst) {S Dd Sc P : BitVec 32}
    {K : KState} {rc : Lane} (s₀ : State) (E : Env s₀.wr S Dd Sc P) (hd : s₀.gpr dst = Dd)
    (h1 : s₀.gpr .r1 = Sc) (hP : s₀.mem.readW (A Sc rcPtr) 32 = P) (hrc : rd64 s₀.mem P 0 = rc)
    (hb : ∀ x < 5, Pair s₀ (cl x) (ch x) (B K x y))
    (hdl : y + 1 < 5 → ∀ x < 5, rd64 s₀.mem Dd (dOff x) = D K x)
    (hl : ∀ j < 5 * y, rd64 s₀.mem Dd (8 * j) = out K rc (j % 5) (j / 5)) :
    WP isa (.block ((List.range 5).flatMap fun x => chi dst x y)) s₀ (ChiInv s₀ K rc Dd y 5) := by
  have fD := E.fitD
  obtain ⟨dT1, dT2⟩ := hdst.T
  refine wp_range_flatMap (M := isa) (ChiInv s₀ K rc Dd y) (fun x s hx hI => ?_) 5 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, hdl, fun j hj => hl j (by omega)⟩
  have ho : 8 * (x + 5 * y) + 8 ≤ 200 := by omega
  refine WP.mono (chi_ok x y hx hy hdst s (hI.wr ▸ E) (by rw [hI.gpr dst (nm2 dT1.symm dT2.symm), hd])
    (by rw [hI.gpr .r1 (by decide), h1]) (by rw [E.ptr hI.frame, hP]) (by rw [E.rc64 hI.frame, hrc])
    (fun x' hx' => ⟨by rw [hI.gpr _ (nm2 (cl_T x' hx').1 (cl_T x' hx').2.1)]; exact (hb x' hx').1,
      by rw [hI.gpr _ (nm2 (cl_T x' hx').2.2.1 (cl_T x' hx').2.2.2)]; exact (hb x' hx').2⟩))
    fun s' w => ⟨fun q hq => by rw [w.gpr q hq, hI.gpr q hq], w.rd.trans hI.rd, w.wr.trans hI.wr,
      w.sp.trans hI.sp, ?_, fun hy' x' hx' => ?_, fun j hj => ?_⟩
  · rw [w.mem]; exact frame_write64 hI.frame (List.mem_singleton_self _) fD ho _
  · rw [w.mem, rd64_write64_ne _ _ (by omega) (by have := dOff_lt x' hx'; omega)
      (by simp only [dOff]; omega)]
    exact hI.dl hy' x' hx'
  · rw [w.mem]
    by_cases e : j = x + 5 * y
    · subst e
      rw [rd64_write64_self _ _ (by omega), show (x + 5 * y) % 5 = x by omega,
        show (x + 5 * y) / 5 = y by omega]
    · rw [rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
      exact hI.lanes j (by omega)

/-- After the first `k` lanes `B[x]` of plane `y`. -/
def BInv (s₀ : State) (K : KState) (y k : Nat) (s : State) : Prop :=
  Only bRegs s₀ s ∧ ∀ x < k, Pair s (cl x) (ch x) (B K x y)

theorem laneBs_ok (y : Nat) (hy : y < 5) {src dst : Reg} (hsrc : Ptr src) (hdst : Ptr dst)
    {S Dd : BitVec 32} {K : KState} (s₀ : State) (h0 : s₀.gpr src = S) (hd : s₀.gpr dst = Dd)
    (hRS : Reg64 s₀.wr S 200) (hRD : Reg64 s₀.wr Dd 200) (hK : Lanes32 s₀.mem S K)
    (hD : ∀ x < 5, rd64 s₀.mem Dd (dOff x) = D K x) :
    WP isa (.block ((List.range 5).flatMap fun x => laneB src dst x y)) s₀ (BInv s₀ K y 5) := by
  refine wp_range_flatMap (M := isa) (BInv s₀ K y) (fun x s hx ⟨ho, hc⟩ => ?_) 5 (Nat.le_refl _) s₀
    ⟨Only.refl _ _, fun _ h => absurd h (by omega)⟩
  refine WP.mono (laneB_ok x y hx hy hsrc hdst (K := K) s (by rw [ho.gpr src (ptr_b src hsrc), h0])
    (by rw [ho.gpr dst (ptr_b dst hdst), hd]) (by rw [ho.wr]; exact hRS) (by rw [ho.wr]; exact hRD)
    (by rw [ho.mem]; exact hK) (by rw [ho.mem]; exact hD)) fun s' ⟨o, p⟩ =>
      ⟨(ho.trans o).mono (b_mono x hx), fun x' hx' => ?_⟩
  by_cases e : x' = x
  · subst e; exact p
  · have hx'5 : x' < 5 := by omega
    exact (hc x' (by omega)).of_only o
      (nm4 (cl_T x' hx'5).1 (cl_T x' hx'5).2.1 (cl_ne hx hx'5 e) (cl_ch x' hx'5 x hx))
      (nm4 (cl_T x' hx'5).2.2.1 (cl_T x' hx'5).2.2.2 (fun h => cl_ch x hx x' hx'5 h.symm)
        (ch_ne hx hx'5 e))

/-- After the first `y` planes of the output. -/
structure PInv (s₀ : State) (K : KState) (rc : Lane) (Dd : BitVec 32) (y : Nat) (s : State) :
    Prop where
  gpr : ∀ q ∈ [Reg.r0, .r1], s.gpr q = s₀.gpr q
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [regR Dd 200] s₀.mem s.mem
  dl : y < 5 → ∀ x < 5, rd64 s.mem Dd (dOff x) = D K x
  lanes : ∀ j < 5 * y, rd64 s.mem Dd (8 * j) = out K rc (j % 5) (j / 5)

theorem planes_ok {src dst : Reg} (hsrc : Ptr src) (hdst : Ptr dst) {S Dd Sc P : BitVec 32}
    {K : KState} {rc : Lane} (s₀ : State) (E : Env s₀.wr S Dd Sc P) (h0 : s₀.gpr src = S)
    (hd : s₀.gpr dst = Dd) (h1 : s₀.gpr .r1 = Sc) (hK : Lanes32 s₀.mem S K)
    (hP : s₀.mem.readW (A Sc rcPtr) 32 = P) (hrc : rd64 s₀.mem P 0 = rc) (s : State)
    (hs : PInv s₀ K rc Dd 0 s) :
    WP isa (.block ((List.range 5).flatMap (plane src dst))) s (PInv s₀ K rc Dd 5) := by
  refine wp_range_flatMap (M := isa) (PInv s₀ K rc Dd) (fun y s hy hI => ?_) 5 (Nat.le_refl _) s hs
  unfold plane
  rw [WP.block_append_iff]
  have E' : Env s.wr S Dd Sc P := hI.wr ▸ E
  refine WP.mono (laneBs_ok y hy hsrc hdst (K := K) s (by rw [hI.gpr src hsrc, h0])
    (by rw [hI.gpr dst hdst, hd]) E'.wS E'.wD (fun i hi => by rw [E.src hI.frame hi, hK i hi])
    (hI.dl hy)) fun s₁ ⟨o₁, b₁⟩ => ?_
  have E₁ : Env s₁.wr S Dd Sc P := o₁.wr ▸ E'
  refine WP.mono (chis_ok y hy hdst s₁ E₁ (by rw [o₁.gpr dst (ptr_b dst hdst), hI.gpr dst hdst, hd])
    (by rw [o₁.gpr .r1 (by decide), hI.gpr .r1 (by simp), h1]) (by rw [o₁.mem, E.ptr hI.frame, hP])
    (by rw [o₁.mem, E.rc64 hI.frame, hrc]) b₁ (fun hy' => by rw [o₁.mem]; exact hI.dl hy)
    (fun j hj => by rw [o₁.mem]; exact hI.lanes j hj)) fun s₂ h₂ => ⟨fun q hq => ?_,
      by rw [h₂.rd, o₁.rd, hI.rd], by rw [h₂.wr, o₁.wr, hI.wr], by rw [h₂.sp, o₁.sp, hI.sp],
      hI.frame.trans (o₁.mem ▸ h₂.frame), fun hy' => h₂.dl (by omega),
      fun j hj => h₂.lanes j (by omega)⟩
  obtain ⟨qT1, qT2⟩ := ptr_T q hq
  rw [h₂.gpr q (nm2 qT1.symm qT2.symm), o₁.gpr q (ptr_b q hq), hI.gpr q hq]

/-! ## The round -/

theorem rd64_writeW_disj (m : Mem) {Dd : BitVec 32} {a : Addr} (v : BitVec 32)
    (hd : Region.Disjoint ⟨a, 4⟩ (regR Dd 200)) (hfit : Dd.toNat + 200 ≤ 2 ^ 32) {o : Nat}
    (ho : o + 8 ≤ 200) : rd64 (m.writeW a v) Dd o = rd64 m Dd o := by
  simp only [rd64]
  rw [Mem.readW_writeW_sep (hd.symm.sep (contains_A hfit (by omega)) (Region.contains_self a 4))
    (by decide), Mem.readW_writeW_sep (hd.symm.sep (contains_A hfit (by omega))
    (Region.contains_self a 4)) (by decide)]

theorem round_ok {src dst : Reg} (hsrc : Ptr src) (hdst : Ptr dst) {S Dd Sc P : BitVec 32}
    {K : KState} {rc : Lane} (s : State) (E : Env s.wr S Dd Sc P) (h0 : s.gpr src = S)
    (hd : s.gpr dst = Dd) (h1 : s.gpr .r1 = Sc) (hK : Lanes32 s.mem S K)
    (hP : s.mem.readW (A Sc rcPtr) 32 = P) (hrc : rd64 s.mem P 0 = rc) :
    WP isa (.block (round src dst)) s fun s' =>
      Lanes32 s'.mem Dd (outState K rc) ∧ Frame [regR Dd 200, ⟨A Sc rcPtr, 4⟩] s.mem s'.mem ∧
      s'.mem.readW (A Sc rcPtr) 32 = P + 8 ∧ (∀ q ∈ [Reg.r0, .r1], s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨dT1, dT2⟩ := hdst.T
  unfold round
  rw [WP.block_append_iff]
  refine WP.mono (columns_ok hsrc (K := K) s h0 E.wS hK) fun s₁ ⟨o₁, c₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dcols_ok hdst s₁ (by rw [o₁.gpr dst (ptr_col dst hdst), hd]) E.fitD
    (by rw [o₁.wr]; exact E.wD) c₁) fun s₂ d₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (planes_ok hsrc hdst s E h0 hd h1 hK hP hrc s₂ ⟨fun q hq => ?_,
    by rw [d₂.rd, o₁.rd], by rw [d₂.wr, o₁.wr], by rw [d₂.sp, o₁.sp], by rw [← o₁.mem]; exact d₂.frame,
    fun _ => d₂.dl, fun j hj => absurd hj (by omega)⟩) fun s₃ p₃ => ?_
  · obtain ⟨qT1, qT2⟩ := ptr_T q hq
    rw [d₂.gpr q (nm2 qT1.symm qT2.symm), o₁.gpr q (ptr_col q hq)]
  have g₃ : s₃.gpr .r1 = Sc := by rw [p₃.gpr .r1 (by simp), h1]
  refine wp_ldr (a := A Sc rcPtr) (by decide) (by rw [g₃]) (by rw [p₃.rd, p₃.wr]; exact mem_rd E.ptr_in)
    fun s₄ u₄ => ?_
  refine wp_add (op2_imm (by decide)) fun s₅ u₅ => ?_
  refine wp_str (a := A Sc rcPtr) (by decide) (by rw [u₅.other .r1 (by decide), u₄.other .r1 (by decide), g₃])
    (by rw [u₅.wr, u₄.wr, p₃.wr]; exact E.ptr_in) fun s₆ u₆ =>
      WP.block_nil ⟨fun i hi => ?_, ?_, ?_, fun q hq => ?_, by rw [u₆.rd, u₅.rd, u₄.rd, p₃.rd],
        by rw [u₆.wr, u₅.wr, u₄.wr, p₃.wr], by rw [u₆.sp, u₅.sp, u₄.sp, p₃.sp]⟩
  · rw [u₆.mem, rd64_writeW_disj _ _ E.ptr_dst E.fitD (by omega), u₅.mem, u₄.mem, p₃.lanes i (by omega)]
    simp [outState, hi]
  · rw [u₆.mem, u₅.mem, u₄.mem]
    exact (p₃.frame.mono (by simp)).writeW (r := ⟨A Sc rcPtr, 4⟩) (by simp) _ (Region.contains_self _ _)
  · rw [u₆.mem, Mem.readW_writeW_self32, u₅.gpr, u₄.gpr, E.ptr p₃.frame, hP]
  · obtain ⟨qT1, -⟩ := ptr_T q hq
    rw [u₆.gpr, u₅.other q qT1.symm, u₄.other q qT1.symm, p₃.gpr q hq]

end VG.Proof.Sha3.Arm

end

/-!
# Keccak-f[1600] on ARMv7: the whole function

The prologue saves the callee-saved registers and stores the round constants
in the scratch space; each iteration of the loop runs two rounds (`round_ok`),
from the state to the second state in the scratch space and back; the epilogue
restores the registers.
-/

namespace VG.Proof.Sha3.Arm

open VG VG.Arm VG.Impl.Sha3.Arm
open VG.Spec.Sha3 (stateAt keccakF rnd RC)
open VG.Impl.Sha512.Arm (lo hi)
open VG.Proof.Sha512.Arm (rd64 write64 A A_eq contains_A readW64 rd64_write64_self rd64_write64_ne
  rd64_write64_disj frame_write64 rd64_frame mem_rd wp_movw wp_movt Reg64)
open VG.Proof.MdStream.Arm (Upd Mupd wp_add wp_sub wp_ldr wp_str wp_cmp op2_reg op2_imm eval_ne
  sub_beq readW_writeW_save)
open VG.Proof.Sha3 (outState_eq foldl_succ off_disjoint sub_offset add_zero')

/-! ## Addresses -/

section
variable (s₀ : State)

abbrev stp : BitVec 32 := s₀.gpr .r0
abbrev scp : BitVec 32 := s₀.gpr .r1
abbrev A₀ : KState := stateAt s₀.mem (State.addr (stp s₀))

/-- The state the rounds read from before round `r`, and the one they write. -/
def cur (r : Nat) : BitVec 32 := if r % 2 = 0 then stp s₀ else scp s₀
def oth (r : Nat) : BitVec 32 := if r % 2 = 0 then scp s₀ else stp s₀

/-- The address of the constant of round `r`. -/
abbrev rcp (r : Nat) : BitVec 32 := scp s₀ + BitVec.ofNat 32 (200 + 8 * r)

end

theorem cur_succ (s₀ : State) (r : Nat) : cur s₀ (r + 1) = oth s₀ r := by
  simp only [cur, oth]; split <;> split <;> first | rfl | omega

theorem cur_cases (s₀ : State) (r : Nat) :
    (cur s₀ r = stp s₀ ∧ oth s₀ r = scp s₀) ∨ (cur s₀ r = scp s₀ ∧ oth s₀ r = stp s₀) := by
  simp only [cur, oth]; split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

theorem cur_even (s₀ : State) (t : Nat) : cur s₀ (2 * t) = stp s₀ ∧ oth s₀ (2 * t) = scp s₀ := by
  simp only [cur, oth]; split
  · exact ⟨rfl, rfl⟩
  · omega

theorem cur_odd (s₀ : State) (t : Nat) : cur s₀ (2 * t + 1) = scp s₀ ∧ oth s₀ (2 * t + 1) = stp s₀ := by
  simp only [cur, oth]; split
  · omega
  · exact ⟨rfl, rfl⟩

theorem A_add (b : BitVec 32) (a o : Nat) : A (b + BitVec.ofNat 32 a) o = A b (a + o) := by
  simp only [A]; rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem rcp_succ (s₀ : State) (r : Nat) : rcp s₀ r + 8 = rcp s₀ (r + 1) := by
  simp only [rcp]
  bv_omega

theorem rd64_rcp (m : Mem) (s₀ : State) (r : Nat) : rd64 m (rcp s₀ r) 0 = rd64 m (scp s₀) (200 + 8 * r) := by
  simp only [rd64, rcp, A_add, Nat.zero_add, Nat.add_zero]

theorem rd64_congr {m m' : Mem} {b : BitVec 32} {o : Nat} (h1 : m'.readW (A b o) 32 = m.readW (A b o) 32)
    (h2 : m'.readW (A b (o + 4)) 32 = m.readW (A b (o + 4)) 32) : rd64 m' b o = rd64 m b o := by
  simp only [rd64]; rw [h1, h2]

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-! ## The precondition -/

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [regR (stp s₀) 200, regR (scp s₀) 512]
  disj : (regR (stp s₀) 200).Disjoint (regR (scp s₀) 512)
  fitS : (stp s₀).toNat + 200 ≤ 2 ^ 32
  fitC : (scp s₀).toNat + 512 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha3.permuteArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem scA {d : Nat} (hd : d < 512) : A (scp s₀) d = State.addr (scp s₀) + BitVec.ofNat 64 d :=
  A_eq (by have := h.fitC; omega)

theorem scr_in {d : Nat} (hd : d + 4 ≤ 512) : InRegions s₀.wr (A (scp s₀) d) 4 :=
  ⟨_, by rw [h.wr]; simp, contains_A h.fitC hd⟩

theorem scr_disj {a n b k : Nat} (ha : a + n ≤ 512) (hb : b + k ≤ 512) (hs : a + n ≤ b ∨ b + k ≤ a)
    (hn : 0 < n) (hk : 0 < k) : Region.Disjoint ⟨A (scp s₀) a, n⟩ ⟨A (scp s₀) b, k⟩ := by
  rw [h.scA (by omega), h.scA (by omega)]
  exact off_disjoint _ (by omega) (by omega) hs

theorem off_st {d n : Nat} (hd : d + n ≤ 512) (hn : 0 < n) :
    Region.Disjoint ⟨A (scp s₀) d, n⟩ (regR (stp s₀) 200) := by
  have hs : Region.Sub ⟨A (scp s₀) d, n⟩ (regR (scp s₀) 512) := by
    rw [h.scA (by omega)]; exact sub_offset hd (by omega)
  exact h.disj.symm.sub_left hs

theorem off_scr {d n : Nat} (hd₀ : 200 ≤ d) (hd : d + n ≤ 512) (hn : 0 < n) :
    Region.Disjoint ⟨A (scp s₀) d, n⟩ (regR (scp s₀) 200) := by
  have := off_disjoint (State.addr (scp s₀)) (a := d) (n := n) (b := 0) (k := 200) (by omega)
    (by omega) (.inr hd₀)
  rw [add_zero'] at this
  rw [h.scA (by omega)]; exact this

theorem off_dst {Dd : BitVec 32} (hD : Dd = stp s₀ ∨ Dd = scp s₀) {d n : Nat} (hd₀ : 200 ≤ d)
    (hd : d + n ≤ 512) (hn : 0 < n) : Region.Disjoint ⟨A (scp s₀) d, n⟩ (regR Dd 200) := by
  rcases hD with rfl | rfl
  · exact h.off_st hd hn
  · exact h.off_scr hd₀ hd hn

theorem st_scr200 : (regR (stp s₀) 200).Disjoint (regR (scp s₀) 200) :=
  h.disj.sub_right (Region.sub_prefix (by omega))

theorem reg64_st : Reg64 s₀.wr (stp s₀) 200 :=
  VG.Proof.Sha512.Arm.Reg64.of_mem (by rw [h.wr]; simp) h.fitS

theorem reg64_scr : Reg64 s₀.wr (scp s₀) 200 := fun o ho =>
  ⟨h.scr_in (d := o) (by omega), h.scr_in (d := o + 4) (by omega)⟩

theorem env_of {S Dd : BitVec 32} (hS : S = stp s₀ ∨ S = scp s₀) (hD : Dd = stp s₀ ∨ Dd = scp s₀)
    (hSD : (regR S 200).Disjoint (regR Dd 200)) {r : Nat} (hr : r < 24) :
    Env s₀.wr S Dd (scp s₀) (rcp s₀ r) := by
  have fS := h.fitS
  have fC := h.fitC
  refine ⟨?_, ?_, ?_, ?_, h.scr_in (d := rcPtr) (by decide), fun o ho => ?_, hSD,
    h.off_dst hD (d := rcPtr) (by decide) (by decide) (by decide), fun o ho => ?_⟩
  · rcases hS with rfl | rfl <;> omega
  · rcases hD with rfl | rfl <;> omega
  · rcases hS with rfl | rfl
    · exact h.reg64_st
    · exact h.reg64_scr
  · rcases hD with rfl | rfl
    · exact h.reg64_st
    · exact h.reg64_scr
  · rw [A_add]; exact h.scr_in (by rcases ho with rfl | rfl <;> omega)
  · rw [A_add]; exact h.off_dst hD (by omega) (by rcases ho with rfl | rfl <;> omega) (by decide)

theorem env {r : Nat} (hr : r < 24) : Env s₀.wr (cur s₀ r) (oth s₀ r) (scp s₀) (rcp s₀ r) := by
  rcases cur_cases s₀ r with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rw [e₁, e₂]
  · exact h.env_of (.inl rfl) (.inr rfl) h.st_scr200 hr
  · exact h.env_of (.inr rfl) (.inl rfl) h.st_scr200.symm hr

end Pre

/-! ## What the scratch space holds -/

/-- The round constants. -/
def Aux (s₀ : State) (m : Mem) : Prop := ∀ j < 24, rd64 m (scp s₀) (200 + 8 * j) = RC j

/-- The saved registers. -/
def Saved (s₀ : State) (m : Mem) : Prop := ∀ p ∈ saved, m.readW (A (scp s₀) p.2) 32 = s₀.gpr p.1

theorem saved_ok : ∀ p ∈ saved, p.1 ≠ .r1 ∧ p.2 < 4096 ∧ 396 ≤ p.2 ∧ p.2 + 4 ≤ 432 := by decide

theorem Aux.keep {s₀ : State} {m m' : Mem} (ha : Aux s₀ m)
    (hk : ∀ d, 200 ≤ d → d + 4 ≤ 392 → m'.readW (A (scp s₀) d) 32 = m.readW (A (scp s₀) d) 32) :
    Aux s₀ m' := fun j hj =>
  (rd64_congr (hk (200 + 8 * j) (by omega) (by omega)) (hk (200 + 8 * j + 4) (by omega) (by omega))).trans
    (ha j hj)

theorem Saved.keep {s₀ : State} {m m' : Mem} (hs : Saved s₀ m)
    (hk : ∀ d, 396 ≤ d → d + 4 ≤ 432 → m'.readW (A (scp s₀) d) 32 = m.readW (A (scp s₀) d) 32) :
    Saved s₀ m' := fun p hp => by
  obtain ⟨-, -, h1, h2⟩ := saved_ok p hp
  rw [hk _ h1 h2]; exact hs p hp

theorem readW_writeW_A (m : Mem) {b : BitVec 32} {N : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (v : BitVec 32)
    {d e : Nat} (hd : d + 4 ≤ N) (he : e + 4 ≤ N) (hs : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (A b e) v).readW (A b d) 32 = m.readW (A b d) 32 := by
  rw [A_eq (by omega), A_eq (by omega)]; exact readW_writeW_save m _ v (by omega) (by omega) hs

/-- Words the rounds do not write. -/
theorem Pre.keep_round {s₀ : State} (hp : Pre s₀) {Dd : BitVec 32} (hD : Dd = stp s₀ ∨ Dd = scp s₀)
    {m m' : Mem} (hf : Frame [regR Dd 200, ⟨A (scp s₀) rcPtr, 4⟩] m m') {d : Nat} (hd : 200 ≤ d)
    (hd' : d + 4 ≤ 512) (hne : d + 4 ≤ 392 ∨ 396 ≤ d) :
    m'.readW (A (scp s₀) d) 32 = m.readW (A (scp s₀) d) 32 := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.off_dst hD hd hd' (by decide)
  · exact hp.scr_disj hd' (by decide) (by simp only [rcPtr]; omega) (by decide) (by decide)

/-! ## The state in memory -/

theorem stateAt_get {b : BitVec 32} (hfit : b.toNat + 200 ≤ 2 ^ 32) (m : Mem) {i : Nat} (hi : i < 25) :
    (stateAt m (State.addr b))[i] = rd64 m b (8 * i) := by
  simp only [stateAt, Vector.getElem_ofFn, rd64]
  rw [readW64, A_eq (by omega), A_eq (by omega),
    show State.addr b + BitVec.ofNat 64 (8 * i) + 4 = State.addr b + BitVec.ofNat 64 (8 * i + 4) by
      bv_omega]

theorem stateAt_eq {b : BitVec 32} (hfit : b.toNat + 200 ≤ 2 ^ 32) {m : Mem} {K : KState}
    (h : Lanes32 m b K) : stateAt m (State.addr b) = K := by
  apply Vector.ext
  intro i hi
  rw [stateAt_get hfit m hi, h i hi]
  exact getElem!_pos K i hi

/-! ## The rounds -/

/-- The loop's invariant, before round `r`. -/
structure LInv (s₀ : State) (r : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = stp s₀
  r1 : s.gpr .r1 = scp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ptr : s.mem.readW (A (scp s₀) rcPtr) 32 = rcp s₀ r
  state : Lanes32 s.mem (cur s₀ r) ((List.range r).foldl rnd (A₀ s₀))
  aux : Aux s₀ s.mem
  saved : Saved s₀ s.mem
  frame : Frame [regR (stp s₀) 200, regR (scp s₀) 512] s₀.mem s.mem

theorem round_step {s₀ : State} (hp : Pre s₀) {r : Nat} (hr : r < 24) {src dst : Reg} (hsrc : Ptr src)
    (hdst : Ptr dst) {s : State} (hL : LInv s₀ r s) (h0 : s.gpr src = cur s₀ r)
    (hd : s.gpr dst = oth s₀ r) : WP isa (.block (round src dst)) s (LInv s₀ (r + 1)) := by
  have hD : oth s₀ r = stp s₀ ∨ oth s₀ r = scp s₀ := (cur_cases s₀ r).symm.imp (·.2) (·.2)
  have E : Env s.wr (cur s₀ r) (oth s₀ r) (scp s₀) (rcp s₀ r) := hL.wr ▸ hp.env hr
  refine WP.mono (round_ok hsrc hdst (rc := RC r) s E h0 hd hL.r1 hL.state hL.ptr
    (by rw [rd64_rcp]; exact hL.aux r hr)) fun s' ⟨hl, hf, hptr, hq, hrd, hwr, hsp⟩ => ?_
  refine ⟨by rw [hq .r0 (by simp), hL.r0], by rw [hq .r1 (by simp), hL.r1], hrd.trans hL.rd,
    hwr.trans hL.wr, hsp.trans hL.sp, by rw [hptr, rcp_succ], ?_,
    hL.aux.keep fun d hd hd' => hp.keep_round hD hf hd (by omega) (.inl hd'),
    hL.saved.keep fun d hd hd' => hp.keep_round hD hf (by omega) (by omega) (.inr hd), ?_⟩
  · rw [cur_succ, foldl_succ, ← outState_eq]; exact hl
  · refine hL.frame.trans (hf.sub fun R hR => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · rcases hD with e | e <;> rw [e]
      · exact ⟨regR (stp s₀) 200, by simp, fun _ h => h⟩
      · exact ⟨regR (scp s₀) 512, by simp, Region.sub_prefix (by omega)⟩
    · refine ⟨regR (scp s₀) 512, by simp, ?_⟩
      rw [hp.scA (by decide)]; exact sub_offset (by decide) (by decide)

theorem body_ok {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < 12) {s : State} (hL : LInv s₀ (2 * t) s) :
    WP isa (.block body) s fun s' =>
      (eval .ne s' = some false ∧ LInv s₀ 24 s') ∨
      (eval .ne s' = some true ∧ t + 1 < 12 ∧ LInv s₀ (2 * (t + 1)) s') := by
  unfold body
  rw [WP.block_append_iff]
  refine WP.mono (round_step hp (r := 2 * t) (by omega) (src := .r0) (dst := .r1) (by simp [Ptr])
    (by simp [Ptr]) hL (by rw [hL.r0, (cur_even s₀ t).1]) (by rw [hL.r1, (cur_even s₀ t).2]))
    fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_step hp (r := 2 * t + 1) (by omega) (src := .r1) (dst := .r0) (by simp [Ptr])
    (by simp [Ptr]) h₁ (by rw [h₁.r1, (cur_odd s₀ t).1]) (by rw [h₁.r0, (cur_odd s₀ t).2]))
    fun s₂ h₂ => ?_
  have h₂' : LInv s₀ (2 * (t + 1)) s₂ := by rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega]; exact h₂
  refine wp_ldr (a := A (scp s₀) rcPtr) (by decide) (by rw [h₂.r1])
    (by rw [h₂.rd, h₂.wr]; exact mem_rd (hp.scr_in (by decide))) fun s₃ u₃ => ?_
  refine wp_sub (op2_reg _ _) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ u₅ hz => WP.block_nil ?_
  have hT : s₄.gpr T1 = BitVec.ofNat 32 (216 + 16 * t) := by
    rw [u₄.gpr, u₃.gpr, u₃.other .r1 (by decide), h₂'.ptr, h₂.r1]
    show scp s₀ + _ - scp s₀ = _
    rw [BitVec.add_comm, BitVec.add_sub_cancel, show 200 + 8 * (2 * (t + 1)) = 216 + 16 * t by omega]
  rw [hT, show (392 : BitVec 32) = BitVec.ofNat 32 392 from rfl,
    VG.Proof.MdStream.Arm.sub_beq (by omega) (by omega)] at hz
  have hs₅ : LInv s₀ (2 * (t + 1)) s₅ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.gpr, u₄.other .r0 (by decide), u₃.other .r0 (by decide), h₂'.r0]
    · rw [u₅.gpr, u₄.other .r1 (by decide), u₃.other .r1 (by decide), h₂'.r1]
    · rw [u₅.rd, u₄.rd, u₃.rd, h₂'.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, h₂'.wr]
    · rw [u₅.sp, u₄.sp, u₃.sp, h₂'.sp]
    · rw [u₅.mem, u₄.mem, u₃.mem, h₂'.ptr]
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.state
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.aux
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.saved
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.frame
  by_cases hlast : t + 1 = 12
  · refine .inl ⟨by rw [eval_ne, hz, decide_eq_true (by omega)]; rfl, ?_⟩
    rw [show 24 = 2 * (t + 1) by omega]; exact hs₅
  · exact .inr ⟨by rw [eval_ne, hz, decide_eq_false (by omega)]; rfl, by omega, hs₅⟩

/-! ## The prologue -/

/-- The memory after storing the registers `l` (values `g`) at `b + offset`. -/
def saveMemA (m : Mem) (b : BitVec 32) (g : Reg → BitVec 32) : List (Reg × Nat) → Mem
  | [] => m
  | p :: l => saveMemA (m.writeW (A b p.2) (g p.1)) b g l

theorem saveA_ok {bR : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop),
    (∀ p ∈ l, p.2 < 4096 ∧ InRegions s.wr (A (s.gpr bR) p.2) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMemA s.mem (s.gpr bR) s.gpr l → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.str p.1 bR p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ k; exact k s rfl rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hl k
    obtain ⟨h1, h3⟩ := hl p (by simp)
    refine wp_str h1 rfl h3 fun s₁ u₁ => ?_
    refine ih s₁ Q (fun q hq => ?_) fun s' g rd wr sp m => k s' (g.trans u₁.gpr) (rd.trans u₁.rd)
      (wr.trans u₁.wr) (sp.trans u₁.sp) ?_
    · rw [u₁.gpr, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rw [m, u₁.mem, u₁.gpr]; rfl

theorem saveMemA_frame {b : BitVec 32} {N : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (g : Reg → BitVec 32) :
    ∀ (l : List (Reg × Nat)) (m : Mem), (∀ p ∈ l, p.2 + 4 ≤ N) →
      Frame [regR b N] m (saveMemA m b g l) := by
  intro l
  induction l with
  | nil => intro m _; exact Frame.refl _ _
  | cons p l ih =>
    intro m hl
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_A hfit (hl p (by simp)))).trans
      (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

set_option simprocs false in
theorem saveMemA_saved (m : Mem) {b : BitVec 32} (hfit : b.toNat + 512 ≤ 2 ^ 32) (g : Reg → BitVec 32) :
    ∀ p ∈ saved, (saveMemA m b g saved).readW (A b p.2) 32 = g p.1 := by
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega) only [saved, saveMemA, Mem.readW_writeW_self32, readW_writeW_A (hfit := hfit)]

/-- Round constant `k`, stored in the scratch space. -/
theorem rcStore_ok (k : Nat) (hk : k < 24) (s : State)
    (hin : InRegions s.wr (A (s.gpr .r1) (200 + 8 * k)) 4)
    (hin' : InRegions s.wr (A (s.gpr .r1) (200 + 8 * k + 4)) 4) :
    WP isa (.block (rcStore k)) s fun s' =>
      (∀ r, r ≠ T1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = write64 s.mem (s.gpr .r1) (200 + 8 * k) (RC k) := by
  unfold rcStore
  refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => ?_
  refine wp_str (a := A (s.gpr .r1) (200 + 8 * k)) (by omega)
    (by rw [u₂.other .r1 (by decide), u₁.other .r1 (by decide)]) (by rw [u₂.wr, u₁.wr]; exact hin)
    fun s₃ u₃ => ?_
  refine wp_movw fun s₄ u₄ => wp_movt fun s₅ u₅ => ?_
  refine wp_str (a := A (s.gpr .r1) (200 + 8 * k + 4)) (by omega)
    (by rw [u₅.other .r1 (by decide), u₄.other .r1 (by decide), u₃.gpr, u₂.other .r1 (by decide),
      u₁.other .r1 (by decide), show 204 + 8 * k = 200 + 8 * k + 4 by omega])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hin') fun s₆ u₆ =>
      WP.block_nil ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.gpr, u₅.other r hr, u₄.other r hr, u₃.gpr, u₂.other r hr, u₁.other r hr]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₆.mem, u₅.gpr, u₄.gpr, movw_movt, u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, movw_movt, u₂.mem,
      u₁.mem]
    rfl

/-- During the stores of the round constants. -/
structure RcInv (s₀ : State) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = stp s₀
  r1 : s.gpr .r1 = scp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [regR (scp s₀) 512] s₀.mem s.mem
  saved : Saved s₀ s.mem
  rcs : ∀ j < k, rd64 s.mem (scp s₀) (200 + 8 * j) = RC j

theorem rcs_ok {s₀ : State} (hp : Pre s₀) :
    ∀ s, RcInv s₀ 0 s → WP isa (.block ((List.range 24).flatMap rcStore)) s (RcInv s₀ 24) := by
  have fC := hp.fitC
  refine wp_range_flatMap (M := isa) (RcInv s₀) (fun k s hk hI => ?_) 24 (Nat.le_refl _)
  refine WP.mono (rcStore_ok k hk s (by rw [hI.wr, hI.r1]; exact hp.scr_in (by omega))
    (by rw [hI.wr, hI.r1]; exact hp.scr_in (by omega))) fun s' ⟨g', r', w', p', m'⟩ => ?_
  rw [hI.r1] at m'
  refine ⟨by rw [g' _ (by decide), hI.r0], by rw [g' _ (by decide), hI.r1], r'.trans hI.rd, w'.trans hI.wr,
    p'.trans hI.sp, ?_, ?_, fun j hj => ?_⟩
  · rw [m']; exact frame_write64 hI.frame (List.mem_singleton_self _) fC (by omega) _
  · refine hI.saved.keep fun d hd hd' => ?_
    rw [m']
    simp only [write64]
    rw [readW_writeW_A _ fC _ (by omega) (by omega) (by omega),
      readW_writeW_A _ fC _ (by omega) (by omega) (by omega)]
  · rw [m']
    by_cases e : j = k
    · subst e; exact rd64_write64_self _ _ (by omega)
    · rw [rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
      exact hI.rcs j (by omega)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block prologue) s₀ (LInv s₀ 0) := by
  have fC := hp.fitC
  have fS := hp.fitS
  rw [show prologue = saved.map (fun p => Instr.str p.1 .r1 p.2) ++
    ((List.range 24).flatMap rcStore ++ [.dp .add T1 .r1 (.imm 200), .str T1 .r1 rcPtr]) from rfl]
  refine saveA_ok saved s₀ _ (fun p hp' => ⟨(saved_ok p hp').2.1, hp.scr_in (by have := saved_ok p hp'; omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rcs_ok hp s₁ ⟨by rw [g₁], by rw [g₁], rd₁, wr₁, sp₁, ?_, ?_,
    fun _ h => absurd h (by omega)⟩) fun s₂ h₂ => ?_
  · rw [m₁]; exact saveMemA_frame fC _ _ _ (fun p hp' => by have := saved_ok p hp'; omega)
  · intro p hp'; rw [m₁]; exact saveMemA_saved _ fC _ p hp'
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_str (a := A (scp s₀) rcPtr) (by decide) (by rw [u₃.other .r1 (by decide), h₂.r1])
    (by rw [u₃.wr, h₂.wr]; exact hp.scr_in (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have hm : s₄.mem = s₂.mem.writeW (A (scp s₀) rcPtr) (rcp s₀ 0) := by
    rw [u₄.mem, u₃.mem, u₃.gpr, h₂.r1]; rfl
  have keep : ∀ d, 200 ≤ d → d + 4 ≤ 512 → d + 4 ≤ 392 ∨ 396 ≤ d →
      s₄.mem.readW (A (scp s₀) d) 32 = s₂.mem.readW (A (scp s₀) d) 32 := fun d hd hd' hne => by
    rw [hm]; exact readW_writeW_A _ fC _ hd' (by decide) (by simp only [rcPtr]; omega)
  refine ⟨by rw [u₄.gpr, u₃.other .r0 (by decide), h₂.r0], by rw [u₄.gpr, u₃.other .r1 (by decide), h₂.r1],
    by rw [u₄.rd, u₃.rd, h₂.rd], by rw [u₄.wr, u₃.wr, h₂.wr], by rw [u₄.sp, u₃.sp, h₂.sp],
    by rw [hm, Mem.readW_writeW_self32], fun i hi => ?_,
    Aux.keep h₂.rcs fun d hd hd' => keep d hd (by omega) (.inl hd'),
    h₂.saved.keep fun d hd hd' => keep d (by omega) (by omega) (.inr hd), ?_⟩
  · have hc : cur s₀ 0 = stp s₀ := by simp [cur]
    rw [hc, hm, rd64_writeW_disj _ _ (hp.off_st (d := rcPtr) (by decide) (by decide)) fS (by omega),
      rd64_frame h₂.frame (fun r hr => by simp at hr; subst hr; exact hp.disj) fS (by omega),
      ← stateAt_get fS _ hi]
    simp only [List.range_zero, List.foldl_nil]
    exact (getElem!_pos _ i hi).symm
  · rw [hm]
    exact (h₂.frame.mono (by simp)).writeW (by simp) _ (contains_A fC (by decide))

/-! ## The epilogue -/

theorem restoreA_ok {bR : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ bR ∧ p.2 < 4096 ∧ InRegions (s.rd ++ s.wr) (A (s.gpr bR) p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (A (s.gpr bR) p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldr p.1 bR p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_ldr h1 rfl h3 fun s₁ u₁ => ?_
    have e : s₁.gpr bR = s.gpr bR := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm => k s' (fun q hq => ?_) (fun r hr => ?_)
      (hm.trans u₁.mem)
    · rw [e, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, e]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

theorem preserved_saved : ∀ r ∈ preserved, ∃ p ∈ saved, p.1 = r := by decide

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hL : LInv s₀ 24 s) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permuteArm.post s₀ s' := by
  rw [show restore = saved.map (fun p => Instr.ldr p.1 .r1 p.2) from rfl, ← List.append_nil (saved.map _)]
  refine restoreA_ok saved s _ (by decide) (fun p hp' => ⟨(saved_ok p hp').1, (saved_ok p hp').2.1, ?_⟩)
    fun s' ho _ hm => WP.block_nil ⟨fun r hr => ?_, ?_⟩
  · rw [hL.rd, hL.wr, hL.r1]; exact mem_rd (hp.scr_in (by have := saved_ok p hp'; omega))
  · obtain ⟨p, hp', rfl⟩ := preserved_saved r hr
    rw [ho p hp', hL.r1]; exact hL.saved p hp'
  · show stateAt s'.mem (State.addr (stp s₀)) = keccakF (A₀ s₀)
    rw [hm]
    have hc : cur s₀ 24 = stp s₀ := by simp [cur]
    exact stateAt_eq hp.fitS (hc ▸ hL.state)

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permuteArm.post s₀ s' := by
  unfold permute
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := LInv s₀ 24) ?_ fun s₂ h₂ => restore_ok hp h₂)
  let Inv : Nat → State → Prop := fun n s => ∃ t, n = 12 - t ∧ t < 12 ∧ LInv s₀ (2 * t) s
  refine WP.loop (M := isa) Inv (fun n s ⟨t, hn, ht, hL⟩ => ?_) 12 s₁ ⟨0, rfl, by omega, h₁⟩
  refine WP.mono (body_ok hp ht hL) fun s' h => ?_
  rcases h with ⟨he, hL'⟩ | ⟨he, ht', hL'⟩
  · exact .inl ⟨he, hL'⟩
  · exact .inr ⟨he, 12 - (t + 1), by omega, t + 1, rfl, ht', hL'⟩

/-! ## Constant time -/

/-- The constant-time analysis's taint without the round constants that the
prologue stores at `[200, 392)` of the scratch space: public, but no
address or branch depends on them, and the kernel checks the analysis much
faster without them (`taint_decide_weak`). -/
def dropRC (τ : VG.Arm.Taint.T) : VG.Arm.Taint.T :=
  { τ with slots := τ.slots.filter fun sl => !(200 ≤ sl.2.1 && sl.2.1 < 392) }

/-- The initial taint: the pointers are public, and point at the writable regions. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1], flags := false, lens := [200, 512], bases := [(.r0, 0), (.r1, 1)] }

theorem wf₀ {s : State} (h : Proof.Sha3.permuteArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of s h
  have hst := hp.fitS; have hsc := hp.fitC
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.disj, ?_⟩, ?_,
    fun h => absurd h (by decide), fun _ h => by simp [τ₀] at h⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.permuteArm.pre s₁) (h₂ : Proof.Sha3.permuteArm.pre s₂)
    (hpub : Proof.Sha3.permuteArm.pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p0, p1⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · rw [(pre_of s₁ h₁).wr, (pre_of s₂ h₂).wr, stp, scp, stp, scp, p0, p1]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 512⟩]

theorem permute_verified : Verified Arm.target Impl.Sha3.Arm.permute Proof.Sha3.permuteArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · exact VG.Taint.constantTime (A := VG.Arm.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
      (by taint_decide_weak dropRC)
  · refine ⟨satState, rfl, rfl, ?_, by decide, by decide⟩
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha3.Arm

section

/-!
# SHA-3 on ARMv7: calling the permutation, and saving registers

What the streaming functions (`VG.Impl.Sha3.Arm.Stream`) share: the call of
the permutation, the saving and restoring of our caller's registers in the
scratch space, and arithmetic on 32-bit values.
-/

namespace VG.Proof.Sha3.Arm

open VG VG.Arm VG.Impl.Sha3.Arm
open VG.Spec.Sha3 (stateAt keccakF)
open VG.Proof.Sha512.Arm (A A_eq contains_A)
open VG.Proof.Sha3 (off_disjoint sub_offset add_zero')

/-! ## The permutation -/

theorem permute_noCalls : permute.noCalls = true := by decide +kernel

theorem permute_r0 : ∀ i ∈ instrs permute, dstOf i ≠ some .r0 := by
  have : ((instrs permute).all fun i => dstOf i != some .r0) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem permute_r1 : ∀ i ∈ instrs permute, dstOf i ≠ some .r1 := by
  have : ((instrs permute).all fun i => dstOf i != some .r1) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- The state and the permutation's part of a scratch space of `N` bytes. -/
theorem covers_of {wr : List Region} {st scr : BitVec 32} {N : Nat} (hN : 512 ≤ N)
    (hS : regR st 200 ∈ wr) (hC : regR scr N ∈ wr) : Covers [regR st 200, regR scr 512] wr := by
  apply Covers.of_sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, hS, 0, by simp, by simp⟩
  · exact ⟨_, hC, 0, by simp, by simpa using hN⟩

/-- Calling `vg_keccak_f1600` on the state at `r0`, with scratch space at
`r1`: the callee-saved registers other than `lr`, and `r0` and `r1`, are
kept. -/
theorem call_ok {s : State} {st scr : BitVec 32} (h0 : s.gpr .r0 = st) (h1 : s.gpr .r1 = scr)
    (fS : st.toNat + 200 ≤ 2 ^ 32) (fC : scr.toNat + 512 ≤ 2 ^ 32)
    (d₁ : Region.Disjoint (regR st 200) (regR scr 512))
    (hw : Covers [regR st 200, regR scr 512] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) → s'.gpr .r0 = st → s'.gpr .r1 = scr →
      Frame [regR st 200, regR scr 512] s.mem s'.mem →
      stateAt s'.mem (State.addr st) = keccakF (stateAt s.mem (State.addr st)) → Q s') :
    WP isa Impl.Sha3.Arm.Stream.permuteCall s Q := by
  have c0 : s.callEntry.gpr .r0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .r1 = scr := (State.callEntry_gpr _ (by decide)).trans h1
  refine WP.call (k := Proof.Sha3.permuteArm) permute_verified.1
    (rd := []) (wr := [regR st 200, regR scr 512]) ?_ ?_ hw ?_ permute_noCalls
  · simp only [Proof.Sha3.permuteArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, d₁, fS, fC⟩
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hw a n (by simpa using h)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro s' hrd hwr hsp hf hcs hg hpost
    simp only [Proof.Sha3.permuteArm, State.withRegions_gpr, State.withRegions_mem, c0] at hpost
    exact hQ s' hrd hwr hsp hcs (by rw [hg _ permute_r0 (by decide), h0])
      (by rw [hg _ permute_r1 (by decide), h1]) hf (by rw [hpost]; rfl)

/-! ## Saving the caller's registers -/

/-- The caller's registers `g` saved at `scr`. -/
def SSaved (scr : BitVec 32) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ p ∈ Impl.Sha3.Arm.Stream.saved, m.readW (A scr p.2) 32 = g p.1

theorem ssaved_ok : ∀ p ∈ Impl.Sha3.Arm.Stream.saved,
    p.1 ≠ .r1 ∧ p.1 ≠ .r12 ∧ p.2 < 4096 ∧ 512 ≤ p.2 ∧ p.2 + 4 ≤ 532 := by decide

set_option simprocs false in
theorem saveMemA_ssaved (m : Mem) {b : BitVec 32} (hfit : b.toNat + 640 ≤ 2 ^ 32) (g : Reg → BitVec 32) :
    SSaved b g (saveMemA m b g Impl.Sha3.Arm.Stream.saved) := by
  intro p hp
  simp only [Impl.Sha3.Arm.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega) only [Impl.Sha3.Arm.Stream.saved, saveMemA, Mem.readW_writeW_self32,
    readW_writeW_A (hfit := hfit)]

theorem SSaved.keep {scr : BitVec 32} {g : Reg → BitVec 32} {m m' : Mem} (h : SSaved scr g m)
    (hk : ∀ d, 512 ≤ d → d + 4 ≤ 532 → m'.readW (A scr d) 32 = m.readW (A scr d) 32) :
    SSaved scr g m' := fun p hp => by
  obtain ⟨-, -, -, h1, h2⟩ := ssaved_ok p hp
  rw [hk _ h1 h2]; exact h p hp

theorem SSaved.of_gpr {scr : BitVec 32} {g g' : Reg → BitVec 32} {m : Mem} (h : SSaved scr g m)
    (hg : ∀ r, r ≠ .r12 → g r = g' r) : SSaved scr g' m := fun p hp => by
  rw [h p hp, hg _ (ssaved_ok p hp).2.1]

/-- Writes to the state and to the permutation's scratch space keep the
words of the scratch space after the permutation's part. -/
theorem readW_hi {st scr : BitVec 32} (fC : scr.toNat + 640 ≤ 2 ^ 32)
    (hd : Region.Disjoint (regR st 200) (regR scr 640)) {m m' : Mem} {rs : List Region}
    (hf : Frame rs m m') (hrs : ∀ r ∈ rs, r = regR st 200 ∨ r = regR scr 512) {d : Nat}
    (hd₁ : 512 ≤ d) (hd₂ : d + 4 ≤ 640) : m'.readW (A scr d) 32 = m.readW (A scr d) 32 := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases hrs r hr with rfl | rfl
  · refine hd.symm.sub_left ?_
    rw [A_eq (by omega)]; exact sub_offset (by omega) (by omega)
  · have := off_disjoint (State.addr scr) (a := d) (n := 4) (b := 0) (k := 512) (by omega)
      (by omega) (.inr hd₁)
    rw [add_zero'] at this
    rw [A_eq (by omega)]; exact this

/-- Writes to the state and to the permutation's scratch space keep the
saved registers. -/
theorem SSaved.frame {st scr : BitVec 32} (fC : scr.toNat + 640 ≤ 2 ^ 32)
    (hd : Region.Disjoint (regR st 200) (regR scr 640)) {g : Reg → BitVec 32} {m m' : Mem}
    (h : SSaved scr g m) {rs : List Region} (hf : Frame rs m m')
    (hrs : ∀ r ∈ rs, r = regR st 200 ∨ r = regR scr 512) : SSaved scr g m' :=
  h.keep fun _ hd₁ hd₂ => readW_hi fC hd hf hrs hd₁ (by omega)

theorem restore_eq :
    Impl.Sha3.Arm.Stream.restore = Impl.Sha3.Arm.Stream.saved.map (fun p => Instr.ldr p.1 .r1 p.2) := rfl

theorem save_eq :
    Impl.Sha3.Arm.Stream.save = Impl.Sha3.Arm.Stream.saved.map (fun p => Instr.str p.1 .r12 p.2) := rfl

/-- Every callee-saved register is saved, or one of `r8`–`r11`. -/
theorem preserved_cases : ∀ r ∈ preserved,
    (∃ p ∈ Impl.Sha3.Arm.Stream.saved, p.1 = r) ∨ r ∈ [Reg.r8, .r9, .r10, .r11] := by decide

/-! ## Arithmetic on 32-bit values -/

theorem ofNat32_succ (k : Nat) : BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.ofNat_add]; rfl

theorem sub_ofNat32 {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) :=
  VG.Proof.MdStream.Arm.sub_ofNat h

theorem ofNat32_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) :=
  VG.Proof.MdStream.Arm.ofNat_beq_zero h

theorem sub_beq_zero32 {a : Nat} (ha : a < 2 ^ 32) (y : BitVec 32) :
    (BitVec.ofNat 32 a - y == 0) = decide (a = y.toNat) := by
  by_cases h : a = y.toNat
  · subst h; simp
  · have : BitVec.ofNat 32 a - y ≠ 0 := by intro e; apply h; bv_omega
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem beq_zero32 (x : BitVec 32) : (x == 0) = decide (x.toNat = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    rw [beq_eq_false_iff_ne.mpr h]; simp [this]

theorem xor_setWidth32 (x y : Byte) : (x.setWidth 32 ^^^ y.setWidth 32).setWidth 8 = x ^^^ y := by
  ext i hi
  simp

theorem xor_setWidth32' (x : Byte) (y : BitVec 32) :
    (x.setWidth 32 ^^^ y).setWidth 8 = x ^^^ y.setWidth 8 := by
  ext i hi
  simp

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

theorem add_imm0 (a : BitVec 32) : a + 0 = a := by simp

theorem sub_imm0 (a : BitVec 32) : a - 0 = a := by simp

/-! ## The arguments on the stack -/

theorem arg_in {s : State} {n : Nat} (hsp : s.sp.toNat + 4 * n ≤ 2 ^ 32) {k : Nat} (hk : k < n) :
    (⟨stackArgAddr s 0, 4 * n⟩ : Region).Contains (stackArgAddr s k) 4 := by
  simp only [stackArgAddr, Region.Contains]
  rw [addr_add (a := s.sp) (k := 4 * k) (by omega), addr_add (a := s.sp) (k := 4 * 0) (by omega)]
  bv_omega

theorem argByte_eq {s : State} {n : Nat} (hsp : s.sp.toNat + n ≤ 2 ^ 32) {k : Nat} (hk : k < n) :
    VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [VG.Arm.Taint.argByte, stackArgAddr]
  rw [addr_add (a := s.sp) (k := 4 * (k / 4)) (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

end VG.Proof.Sha3.Arm

end
