import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Sha512.Spec
import VerifiedGarbage.Impl.Sha512.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha512.X86_64.Lit

/-!
# SHA-512 compression function on x86-64: the message schedule and the rounds
-/

namespace VG.Proof.Sha512.X86_64

open VG VG.X86_64 VG.Impl.Sha512.X86_64
open VG.Spec.Sha512 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)

/-- The working variables `v` are in the registers of round `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧ s.gpr (var t 2) = v[2] ∧ s.gpr (var t 3) = v[3] ∧
  s.gpr (var t 4) = v[4] ∧ s.gpr (var t 5) = v[5] ∧ s.gpr (var t 6) = v[6] ∧ s.gpr (var t 7) = v[7]

/-- The registers that hold pointers and the count, and `rsp`: never written by the rounds. -/
def pubRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .rsp]

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; congr 1; omega

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 8 - t % 8) % 8]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 :=
  (by decide : ∀ r ∈ work, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2) r h

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 :=
  (by decide : ∀ r ∈ pubRegs, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2) r h

theorem var_not_pub (t k : Nat) : var t k ∉ pubRegs :=
  fun h => (by decide : ∀ r ∈ work, r ∉ pubRegs) _ (var_mem t k) h

/-- The registers of a round are all different. -/
theorem round_nodup (t : Nat) :
    [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, T0, T1, T2].Nodup := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

/-- The round is symbolically executed once, for any registers `a … h`
(which `round_nodup` says are different from each other and the temporaries). -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hw : s.gpr T0 = w) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  have hd := round_nodup t
  have hd' := VG.nodup_reverse hd
  have p3 := var_not_pub t 3
  have p7 := var_not_pub t 7
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by omega),
    var_succ t _ (show 1 < 7 by omega), var_succ t _ (show 2 < 7 by omega),
    var_succ t _ (show 3 < 7 by omega), var_succ t _ (show 4 < 7 by omega),
    var_succ t _ (show 5 < 7 by omega), var_succ t _ (show 6 < 7 by omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha512.X86_64.round]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  simp only [T0, T1, T2, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hd hd' hw ⊢
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, execShift, readSrc,
    isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, ite_true, ite_false, hd, hd',
    h0, h1, h2, h3, h4, h5, h6, h7, hw,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial, trivial, trivial, fun r hr => ?_⟩
  rotate_right
  · obtain ⟨-, n1, n2⟩ := pubRegs_ne hr
    have nh : r ≠ h := fun e => p7 (e ▸ hr)
    have nd : r ≠ d := fun e => p3 (e ▸ hr)
    simp only [T1, T2] at n1 n2
    simp only [nh, nd, n1, n2, ite_false]
  all_goals
    simp only [roundKW_0, roundKW_1, roundKW_2, roundKW_3, roundKW_4, roundKW_5, roundKW_6,
      roundKW_7, bsig1_eq, ch_eq, bsig0_eq, maj_eq, BitVec.add_assoc]

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : Addr) (j : Nat) : Addr := scr + BitVec.ofInt 64 ↑(8 * (j % 16))

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hrsi : s.gpr .rsi = bp) (hrcx : s.gpr .rcx = scr)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 8)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 8)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (bp + BitVec.ofInt 64 ↑(8 * t)) 8)
    (hblk : t < 16 → bswap64 (s.mem.readW (bp + BitVec.ofInt 64 ↑(8 * t)) 64) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 64 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.gpr T0 = W M t ∧
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    simp only [Impl.Sha512.X86_64.schedule, ht, ite_true, slot, at_, T0, T1, T2]
    simp (config := {decide := true}) only [runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, isa, State.ea,
      State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, hrsi, hrcx, hi, hout, ite_true,
      ite_false, hb,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, trivial, trivial, fun r h0 h1 h2 => ?_⟩
    simp [h0]
  · have hw := hwin (by omega)
    have e2 := hw (t - 2) (by omega) (by omega)
    have e7 := hw (t - 7) (by omega) (by omega)
    have e15 := hw (t - 15) (by omega) (by omega)
    have e16 := hw (t - 16) (by omega) (by omega)
    rw [show (t - 2) % 16 = (t + 14) % 16 by omega] at e2
    rw [show (t - 7) % 16 = (t + 9) % 16 by omega] at e7
    rw [show (t - 15) % 16 = (t + 1) % 16 by omega] at e15
    rw [show (t - 16) % 16 = t % 16 by omega] at e16
    simp only [Impl.Sha512.X86_64.schedule, ht, ite_false, slot, at_, T0, T1, T2]
    simp (config := {decide := true}) only [runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, execShift, readSrc,
      isa, State.ea, State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
      RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, hrcx, hin, hout, ite_true, ite_false, e2, e7, e15, e16,
      Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
    have hW := W_ge M (t := t) (by omega)
    rw [ssig0_eq, ssig1_eq] at hW
    refine ⟨by rw [hW], by rw [hW], trivial, trivial, fun r h0 h1 h2 => ?_⟩
    simp [h0, h1, h2]

/-! ## The 80 rounds -/

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

/-- The window `⟨scr, 128⟩`. -/
abbrev winRegion (scr : Addr) : Region := ⟨scr, 128⟩

theorem win_contains (scr : Addr) (j : Nat) : (winRegion scr).Contains (slotAddr scr j) 8 := by
  simp only [slotAddr, ofInt_natCast]
  exact Offset.contains_base _ (by omega) (by omega)

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 8 (slotAddr scr j) 8 := by
  simp only [slotAddr, ofInt_natCast]
  exact Offset.sep _ (by omega) (by omega) (by omega)

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (H : HashValue) (M : Block) (scr : Addr) (sB : State) (t : Nat) (s : State) : Prop where
  vars : Vars t s (VG.Spec.Sha512.rounds H M t)
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [winRegion scr] sB.mem s.mem
  win : ∀ j < t, t ≤ j + 16 → s.mem.readW (slotAddr scr j) 64 = W M j

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hrsi : sB.gpr .rsi = bp) (hrcx : sB.gpr .rcx = scr)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 8)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 8)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 8)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → bswap64 (m.readW (bp + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M t)
    (h0 : Vars 0 sB H) :
    ∀ t ≤ 80, WP isa (rounds t) sB (RInv H M scr sB t) := by
  intro t ht
  induction t with
  | zero =>
    refine WP.block_nil (M := isa) ⟨?_, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (by omega)⟩
    rw [rounds_zero]; exact h0
  | succ t ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_rsi : s.gpr .rsi = bp := (hs.pub .rsi (by decide)).trans hrsi
    have hs_rcx : s.gpr .rcx = scr := (hs.pub .rcx (by decide)).trans hrcx
    refine WP.mono (schedule_ok t s M bp scr hs_rsi hs_rcx
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.wr]; exact hout)
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
    have hv₁ : Vars t s₁ (VG.Spec.Sha512.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k =>
        have := work_ne (var_mem t k); hr₁ _ this.1 this.2.1 this.2.2
      simp only [Vars, e] at hv ⊢
      exact hv
    refine WP.mono (round_ok t s₁ _ _ hv₁ hT0) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · have e : VG.Spec.Sha512.rounds H M (t + 1) =
          roundKW (VG.Spec.Sha512.rounds H M t) (K t) (W M t) := by
        rw [rounds_succ, round_eq]
      rw [e]; exact hv₂
    · have := pubRegs_ne hr
      rw [hr₂ r hr, hr₁ r this.1 this.2.1 this.2.2, hs.pub r hr]
    · rw [hm₂, hm₁]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains scr t)
    · intro j hj hj'
      rw [hm₂, hm₁]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep scr (by omega)) (by decide)]
        exact hs.win j (by omega) (by omega)

end VG.Proof.Sha512.X86_64

/-!
# SHA-512 compression function on x86-64: the whole function
-/

/-!
## SHA-512: the x86-64 contracts

**Untrusted**: the contracts the proofs are written against; the artifacts are emitted with the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The contracts of the x86-64
implementations of the compression function and the streaming interface, in
terms of `Spec/Sha512.lean`.
-/

namespace VG.Proof.Sha512

open Spec.Sha512

open VG.X86_64 in
/-- x86-64 contract for
`vg_sha512_compress(state: *mut [u64; 8], blocks: *const [u8; 128], n: usize, scratch: *mut [u64; 22])`:
updates the hash value at `state` with the `n` 128-byte blocks at `blocks`.

The code may read `blocks` (`128 * n` bytes) and read and write `state`
(64 bytes) and `scratch` (176 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the return address on the stack.
The pointers and `n` are public; the hash value and the blocks are secret. -/
def compressX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 64⟩
    let blocks : Region := ⟨s.gpr .rsi, 128 * (s.gpr .rdx).toNat⟩
    let scratch : Region := ⟨s.gpr .rcx, 176⟩
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
/-- x86-64 contract for `vg_<alg>_init(state: *mut [u8; 192])`, where `iv` is
the initial hash value of `<alg>` (`H0_384`, `H0_512`, `H0_512_224` or
`H0_512_256`): makes the streaming state at `state` represent the empty
message, hashed from `iv`.

The code may write `state` (192 bytes), which may not overlap the return
address on the stack. The pointer is public. -/
def initX86_64 (iv : HashValue) : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [state] ∧ ret.Disjoint state
  post s s' := Repr iv s'.mem (s.gpr .rdi) []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi

open VG.X86_64 in
/-- x86-64 contract for
`vg_sha512_update(state: *mut [u8; 192], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 172])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), hashed from any initial hash value, then afterwards it
represents `m` followed by the `len` bytes at `data`, from the same one.

The code may read `data` (`len` bytes) and read and write `state` (192
bytes) and `scratch` (1376 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the return address on the stack, nor
the 8 bytes below it (where the call of `vg_sha512_compress` stores its
return address).
The pointers, `count` and `len` are public; the state and the data are
secret. -/
def updateX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 192⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 1376⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, Repr iv s.mem (s.gpr .rdi) m → s.gpr .rsi = BitVec.ofNat 64 m.length →
    Repr iv s'.mem (s.gpr .rdi) (m ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

open VG.X86_64 in
/-- x86-64 contract for
`vg_sha512_finalize(state: *mut [u8; 192], count: u64, out: *mut [u8; 64], scratch: *mut [u64; 172])`:
if the streaming state at `state` represents a message `m` of `count` bytes,
fewer than 2⁶⁴, hashed from the initial hash value `iv`, writes the final
hash value `H⁽ᴺ⁾` of `m` from `iv` (64 bytes; `finalHash iv m`) to `out`. The
digest of SHA-384, SHA-512/224 or SHA-512/256 is its first 48, 28 or 32
bytes.

The code may read and write `state` (192 bytes, whose contents on exit are
unspecified), `out` (64 bytes) and `scratch` (1376 bytes, whose contents on
exit are unspecified). These may not overlap each other, nor the return
address on the stack, nor the 8 bytes below it (where the call of
`vg_sha512_compress` stores its return address). The pointers and `count`
are public; the state is secret. -/
def finalizeX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 192⟩
    let out : Region := ⟨s.gpr .rdx, 64⟩
    let scratch : Region := ⟨s.gpr .rcx, 1376⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, Repr iv s.mem (s.gpr .rdi) m → m.length < 2 ^ 64 →
    s.gpr .rsi = BitVec.ofNat 64 m.length → bytesAt s'.mem (s.gpr .rdx) 64 = finalHash iv m
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Sha512


namespace VG.Proof.Sha512.X86_64

open VG VG.X86_64 VG.Impl.Sha512.X86_64
open VG.Spec.Sha512 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## Addresses and regions -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem contains_offset' {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofInt 64 (off : Int)) n := by
  rw [ofInt_natCast]; exact contains_offset h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 8) (hk : k < 8) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofInt 64 ((8 * j : Nat) : Int)) 8 (p + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 8 := by
  rw [ofInt_natCast, ofInt_natCast]
  exact Offset.sep p (by omega) (by omega) (by omega)

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 8) (hk : k < 8)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofInt 64 ((8 * k : Nat) : Int)) v).readW
      (p + BitVec.ofInt 64 ((8 * j : Nat) : Int)) 64 =
    m.readW (p + BitVec.ofInt 64 ((8 * j : Nat) : Int)) 64 :=
  Mem.readW_writeW_sep (word_sep p hj hk h) (by decide)

theorem save_sep (p : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    Mem.Sep (p + BitVec.ofInt 64 (d : Int)) 8 (p + BitVec.ofInt 64 (e : Int)) 8 := by
  rw [ofInt_natCast, ofInt_natCast]
  exact Offset.sep p h (by omega) (by omega)

theorem readW_writeW_save (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofInt 64 (e : Int)) v).readW (p + BitVec.ofInt 64 (d : Int)) 64 =
    m.readW (p + BitVec.ofInt 64 (d : Int)) 64 :=
  Mem.readW_writeW_sep (save_sep p hd he h) (by decide)

theorem stateAt_eq {m : Mem} {p : Addr} {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 8) → m.readW (p + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 64 = v[k]) :
    stateAt m p = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← ofInt_natCast]; exact h k hk

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 8) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 64 := by
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
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev blR : Region := ⟨bp s₀, 128 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 176⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (128 * i)
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

theorem pre_of (s₀ : State) (h : Proof.Sha512.compressX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from the state). -/
theorem nb_lt : 128 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 8 :=
  ⟨stR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 8 :=
  ⟨stR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem in_save {d : Nat} (hd : d + 8 ≤ 176) :
    InRegions (s₀.rd ++ s₀.wr) (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset' hd (by omega)⟩

theorem out_save {d : Nat} (hd : d + 8 ≤ 176) :
    InRegions s₀.wr (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset' hd (by omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 8 := by
  have := h.nb_lt
  rw [ofInt_natCast, show blkAddr s₀ i + BitVec.ofNat 64 (8 * t) =
    bp s₀ + BitVec.ofNat 64 (128 * i + 8 * t) from Offset.add_ofNat_add_ofNat _ _ _]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 8 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (scr s₀ + BitVec.ofInt 64 ((128 : Nat) : Int)) 64 = s₀.gpr .rbx ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((136 : Nat) : Int)) 64 = s₀.gpr .rbp ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((144 : Nat) : Int)) 64 = s₀.gpr .r12 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((152 : Nat) : Int)) 64 = s₀.gpr .r13 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((160 : Nat) : Int)) 64 = s₀.gpr .r14 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((168 : Nat) : Int)) 64 = s₀.gpr .r15

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rcx : s.gpr .rcx = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i
  saved : Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)

/-! ## One block -/

theorem load_eq : load = [
    .mov .rax (.mem (at_ .rdi (8 * 0))), .mov .rbx (.mem (at_ .rdi (8 * 1))),
    .mov .rbp (.mem (at_ .rdi (8 * 2))), .mov .r8 (.mem (at_ .rdi (8 * 3))),
    .mov .r9 (.mem (at_ .rdi (8 * 4))), .mov .r10 (.mem (at_ .rdi (8 * 5))),
    .mov .r11 (.mem (at_ .rdi (8 * 6))), .mov .r12 (.mem (at_ .rdi (8 * 7)))] := by
  decide

theorem update_eq : update ++ advance = [
    .alu .add .rax (.mem (at_ .rdi (8 * 0))), .alu .add .rbx (.mem (at_ .rdi (8 * 1))),
    .alu .add .rbp (.mem (at_ .rdi (8 * 2))), .alu .add .r8 (.mem (at_ .rdi (8 * 3))),
    .alu .add .r9 (.mem (at_ .rdi (8 * 4))), .alu .add .r10 (.mem (at_ .rdi (8 * 5))),
    .alu .add .r11 (.mem (at_ .rdi (8 * 6))), .alu .add .r12 (.mem (at_ .rdi (8 * 7))),
    .store (at_ .rdi (8 * 0)) .rax, .store (at_ .rdi (8 * 1)) .rbx,
    .store (at_ .rdi (8 * 2)) .rbp, .store (at_ .rdi (8 * 3)) .r8,
    .store (at_ .rdi (8 * 4)) .r9, .store (at_ .rdi (8 * 5)) .r10,
    .store (at_ .rdi (8 * 6)) .r11, .store (at_ .rdi (8 * 7)) .r12,
    .alu .add .rsi (.imm 128), .alu .sub .rdx (.imm 1)] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .rax = v[0] ∧ s.gpr .rbx = v[1] ∧ s.gpr .rbp = v[2] ∧ s.gpr .r8 = v[3] ∧
    s.gpr .r9 = v[4] ∧ s.gpr .r10 = v[5] ∧ s.gpr .r11 = v[6] ∧ s.gpr .r12 = v[7] := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrdi : s.gpr .rdi = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 8 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  apply WP.of_runBlock
  rw [load_eq]
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide); have h5 := hin 5 (by decide)
  have h6 := hin 6 (by decide); have h7 := hin 7 (by decide)
  simp (config := {decide := true}) only [vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at,
    State.load64, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, hrdi, h0, h1, h2, h3, h4, h5, h6, h7, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [stateAt_get _ _ (show 0 < 8 by decide), stateAt_get _ _ (show 1 < 8 by decide),
    stateAt_get _ _ (show 2 < 8 by decide), stateAt_get _ _ (show 3 < 8 by decide),
    stateAt_get _ _ (show 4 < 8 by decide), stateAt_get _ _ (show 5 < 8 by decide),
    stateAt_get _ _ (show 6 < 8 by decide), stateAt_get _ _ (show 7 < 8 by decide)]
  simp (config := {decide := true}) [pubRegs]

/-- Eight 64-bit words written to consecutive addresses. -/
def writeState (m : Mem) (p : Addr) (v : HashValue) : Mem :=
  ((((((((m.writeW (p + BitVec.ofInt 64 ((8 * 0 : Nat) : Int)) v[0]).writeW
    (p + BitVec.ofInt 64 ((8 * 1 : Nat) : Int)) v[1]).writeW
    (p + BitVec.ofInt 64 ((8 * 2 : Nat) : Int)) v[2]).writeW
    (p + BitVec.ofInt 64 ((8 * 3 : Nat) : Int)) v[3]).writeW
    (p + BitVec.ofInt 64 ((8 * 4 : Nat) : Int)) v[4]).writeW
    (p + BitVec.ofInt 64 ((8 * 5 : Nat) : Int)) v[5]).writeW
    (p + BitVec.ofInt 64 ((8 * 6 : Nat) : Int)) v[6]).writeW
    (p + BitVec.ofInt 64 ((8 * 7 : Nat) : Int)) v[7])

set_option simprocs false in
theorem stateAt_writeState (m : Mem) (p : Addr) (v : HashValue) : stateAt (writeState m p v) p = v := by
  apply stateAt_eq
  intro k hk
  simp only [writeState]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with h | h | h | h | h | h | h | h <;> subst h <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW_writeW_word]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  have c : ∀ k, k < 8 → (stR s₀).Contains (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) (64 / 8) :=
    fun k hk => contains_offset' (by omega) (by omega)
  simp only [writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _ (c 6 ?_)).writeW ?_ _ (c 7 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hrdi : s.gpr .rdi = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) →
      s.mem.readW (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 64 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .rsi = s.gpr .rsi + 128 ∧ s'.gpr .rdx = s.gpr .rdx - 1 ∧
      s'.zf = some (s.gpr .rdx - 1 == 0) ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 8 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 8 →
      InRegions s.wr (st s₀ + BitVec.ofInt 64 ((8 * k : Nat) : Int)) 8 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin 4 (by decide); have i5 := hin 5 (by decide)
  have i6 := hin 6 (by decide); have i7 := hin 7 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide); have o5 := hout 5 (by decide)
  have o6 := hout 6 (by decide); have o7 := hout 7 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH 4 (by decide); have m5 := hH 5 (by decide)
  have m6 := hH 6 (by decide); have m7 := hH 7 (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc,
    isa, ea_at, State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.cf_setReg, RegUpd.xmm_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.cf_arithFlags, RegUpd.xmm_arithFlags,
    hrdi, i0, i1, i2, i3, i4, i5, i6, i7, o0, o1, o2, o3, o4, o5, o6, o7,
    m0, m1, m2, m3, m4, m5, m6, m7, v0, v1, v2, v3, v4, v5, v6, v7, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  refine ⟨?_, by rw [e128], by rw [e1], by rw [e1], trivial⟩
  simp only [writeState, Vector.getElem_zipWith]

/-- A saved register's slot `⟨scr + d, 8⟩`. -/
theorem saveSlot_sub (p : Addr) {d : Nat} (hd : d + 8 ≤ 176) :
    Region.Sub ⟨p + BitVec.ofInt 64 (d : Int), 8⟩ ⟨p, 176⟩ := by
  rw [ofInt_natCast]; exact sub_offset hd (by omega)

theorem saveSlot_win (p : Addr) {d : Nat} (hd : 128 ≤ d) (hd' : d + 8 ≤ 176) :
    Region.Disjoint ⟨p + BitVec.ofInt 64 (d : Int), 8⟩ (winRegion p) := by
  rw [ofInt_natCast]
  exact Offset.disjoint_base _ hd (by omega)

theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [winRegion (scr s₀)] m m' ∨ Frame [stR s₀] m m') : Saved s₀ m' := by
  have key : ∀ d : Nat, 128 ≤ d → d + 8 ≤ 176 →
      m'.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 = m.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 := by
    intro d hd hd'
    rcases hf with hf | hf
    · exact hf.readW (Region.contains_self _ _) (by simpa using saveSlot_win (scr s₀) hd hd') (by decide)
    · exact hf.readW (Region.contains_self _ _)
        (by simpa using Region.Disjoint.sub_left hp.st_scr.symm (saveSlot_sub (scr s₀) hd')) (by decide)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨(key 128 (by omega) (by omega)).trans h1, (key 136 (by omega) (by omega)).trans h2,
    (key 144 (by omega) (by omega)).trans h3, (key 152 (by omega) (by omega)).trans h4,
    (key 160 (by omega) (by omega)).trans h5, (key 168 (by omega) (by omega)).trans h6⟩

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (128 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    bswap64 (s₀.mem.readW (blkAddr s₀ i + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) =
      W (blk s₀ i) t := by
  rw [W_lt _ ht, bswap64_readW, ofInt_natCast]
  simp only [blk, blockAt, parseBlock, Offset.add_ofNat_add_one, Nat.add_assoc, Nat.reduceAdd]

theorem win_sub (p : Addr) : Region.Sub (winRegion p) ⟨p, 176⟩ := Region.sub_prefix (by omega)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.rdi hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      bswap64 (m.readW (blkAddr s₀ i + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  have hrsi₁ : s₁.gpr .rsi = blkAddr s₀ i := (hpub₁ .rsi (by decide)).trans hL.rsi
  have hrcx₁ : s₁.gpr .rcx = scr s₀ := (hpub₁ .rcx (by decide)).trans hL.rcx
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) _ (scr s₀) s₁ hrsi₁ hrcx₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 80 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  have hrdi₂ : s₂.gpr .rdi = st s₀ := by
    rw [hR.pub .rdi (by decide), hpub₁ .rdi (by decide), hL.rdi]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hrdi₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.frame.readW (contains_offset' (by omega) (by omega)) hst (by decide), hm₁,
      stateAt_get _ _ hk]
  obtain ⟨hm₃, hrsi₃, hrdx₃, hzf₃, hrdi₃, hrcx₃, hrsp₃, hrd₃, hwr₃⟩ := h₃
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hrdx : s₂.gpr .rdx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [pub₂ .rdx (by decide), hL.rdx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
    rw [hm₃]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hrdi₃, hrdi₂], by rw [hrcx₃, pub₂ .rcx (by decide), hL.rcx],
      by rw [hrsp₃, pub₂ .rsp (by decide), hL.rsp], by rw [hrd₃, hR.rd, hrd₁, hL.rd],
      by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_, ?_⟩
    · rw [hm₃, stateAt_writeState, compressBlocks_succ, ← hL.state]
      rfl
    · rw [hm₃]
      refine saved_frame hp ?_ (.inr (frame_writeState (Frame.refl _ _) _))
      refine saved_frame hp ?_ (.inl hR.frame)
      rw [hm₁]; exact hL.saved
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
      rw [BitVec.add_assoc, show (128 : BitVec _) = BitVec.ofNat _ 128 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hrdx₃, hrdx]

/-! ## Prologue and epilogue -/

theorem save_eq : save ++ ([.alu .test .rdx (.reg .rdx)] : List Instr) = [
    .store (at_ .rcx 128) .rbx, .store (at_ .rcx 136) .rbp, .store (at_ .rcx 144) .r12,
    .store (at_ .rcx 152) .r13, .store (at_ .rcx 160) .r14, .store (at_ .rcx 168) .r15,
    .alu .test .rdx (.reg .rdx)] := rfl

theorem restore_eq : restore = [
    .mov .rbx (.mem (at_ .rcx 128)), .mov .rbp (.mem (at_ .rcx 136)), .mov .r12 (.mem (at_ .rcx 144)),
    .mov .r13 (.mem (at_ .rcx 152)), .mov .r14 (.mem (at_ .rcx 160)), .mov .r15 (.mem (at_ .rcx 168))] := rfl

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (scr s₀ + BitVec.ofInt 64 ((128 : Nat) : Int)) (s₀.gpr .rbx)).writeW
    (scr s₀ + BitVec.ofInt 64 ((136 : Nat) : Int)) (s₀.gpr .rbp)).writeW
    (scr s₀ + BitVec.ofInt 64 ((144 : Nat) : Int)) (s₀.gpr .r12)).writeW
    (scr s₀ + BitVec.ofInt 64 ((152 : Nat) : Int)) (s₀.gpr .r13)).writeW
    (scr s₀ + BitVec.ofInt 64 ((160 : Nat) : Int)) (s₀.gpr .r14)).writeW
    (scr s₀ + BitVec.ofInt 64 ((168 : Nat) : Int)) (s₀.gpr .r15)

set_option simprocs false in
theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save ++ ([.alu .test .rdx (.reg .rdx)] : List Instr))) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) := by
  have o0 := hp.out_save (d := 128) (by omega); have o1 := hp.out_save (d := 136) (by omega)
  have o2 := hp.out_save (d := 144) (by omega); have o3 := hp.out_save (d := 152) (by omega)
  have o4 := hp.out_save (d := 160) (by omega); have o5 := hp.out_save (d := 168) (by omega)
  apply WP.of_runBlock
  rw [save_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, ea_at,
    State.store64, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, o0, o1, o2, o3, o4, o5, ite_true,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> trivial

theorem saveMem_saved {s₀ : State} : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW_writeW_save]

theorem saveMem_frame {s₀ : State} : Frame [scrR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 8 ≤ 176 →
      (scrR s₀).Contains (scr s₀ + BitVec.ofInt 64 (d : Int)) (64 / 8) :=
    fun d hd => contains_offset' hd (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 128 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 136 (by omega))).writeW (List.mem_singleton_self _) _
    (c 144 (by omega))).writeW (List.mem_singleton_self _) _ (c 152 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 160 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 168 (by omega))

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hg : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) : Common s₀ 0 s₁ := by
  refine ⟨by rw [hg], by rw [hg], by rw [hg], hrd, hwr, ?_, ?_, by rw [hm]; exact saveMem_saved⟩
  · rw [hm]; exact saveMem_frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq
    intro k hk
    rw [saveMem_frame.readW (contains_offset' (off := 8 * k) (len := 64) (by omega) (by omega))
      (by simpa using hp.st_scr)
      (by decide), ← stateAt_get _ _ hk]
    rfl

set_option simprocs false in
theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha512.compressX86_64.post s₀ s' := by
  have i0 := hp.in_save (d := 128) (by omega); have i1 := hp.in_save (d := 136) (by omega)
  have i2 := hp.in_save (d := 144) (by omega); have i3 := hp.in_save (d := 152) (by omega)
  have i4 := hp.in_save (d := 160) (by omega); have i5 := hp.in_save (d := 168) (by omega)
  rw [← hc.rd, ← hc.wr] at i0 i1 i2 i3 i4 i5
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := hc.saved
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hc.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
  have hrsp := hc.rsp
  have hstate := hc.state
  have hrcx := hc.rcx
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at, State.load64,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, hrcx, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrsp, RegUpd.gpr_setReg]
  · exact hret
  · exact hstate

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha512.compressX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  have hc₀ := common_zero hp hg hrd hwr hm
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
  wr := [⟨0x1000, 64⟩, ⟨0x3000, 176⟩]

theorem compress_verified :
    Verified X86_64.target Impl.Sha512.X86_64.compress Proof.Sha512.compressX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha512.X86_64
