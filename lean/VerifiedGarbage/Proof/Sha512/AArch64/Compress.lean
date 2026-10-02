import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Sha512.Spec
import VerifiedGarbage.Impl.Sha512.AArch64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sha512.AArch64.Lit

/-!
# SHA-512 compression function on AArch64: the message schedule and the rounds
-/

namespace VG.Proof.Sha512.AArch64

open VG VG.AArch64 VG.Impl.Sha512.AArch64
open VG.Spec.Sha512 (HashValue Word Block K W bsig0 bsig1 ch maj ssig0 ssig1)

/-- The working variables `v` are in the registers of round `t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧
  s.gpr (var t 2) = v[2] ∧ s.gpr (var t 3) = v[3] ∧
  s.gpr (var t 4) = v[4] ∧ s.gpr (var t 5) = v[5] ∧
  s.gpr (var t 6) = v[6] ∧ s.gpr (var t 7) = v[7]

/-- The pointers, the count and the registers the ABI requires us to
preserve: never written by the rounds. -/
def pubRegs : List Reg := [.x0, .x1, .x2, .x3, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
  .x26, .x27, .x28, .x30]

/-- The working variables move one register along each round. -/
theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; congr 1; omega

/-- The registers of a round are all different. -/
theorem round_nodup (t : Nat) :
    [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, T0, T1, T2, T3].Nodup := by
  simp only [var]
  have := Nat.mod_lt t (show 8 > 0 by omega)
  generalize t % 8 = c at *
  revert this; revert c; decide

theorem var_mem (t k : Nat) : var t k ∈ work := by
  unfold var List.getD
  cases h : work[(k + 8 - t % 8) % 8]?
  · simp [work]
  · exact List.mem_of_getElem? h

theorem var_not_pub (t k : Nat) : var t k ∉ pubRegs :=
  fun h => (by decide : ∀ r ∈ work, r ∉ pubRegs) _ (var_mem t k) h

theorem pub_ne : ∀ r ∈ pubRegs, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 := by decide

/-- The round is symbolically executed once, for any registers `a … h`
(which `round_nodup` says are different from each other and the temporaries). -/
theorem round_ok (t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hw : s.gpr T0 = w) :
    WP isa (.block (round t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (K t) w) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r ∈ pubRegs, s'.gpr r = s.gpr r := by
  have p3 := var_not_pub t 3
  have p7 := var_not_pub t 7
  -- The registers the round reads and writes.
  have hs := round_nodup t
  have hs' := VG.nodup_reverse hs
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by omega),
    var_succ t _ (show 1 < 7 by omega), var_succ t _ (show 2 < 7 by omega),
    var_succ t _ (show 3 < 7 by omega), var_succ t _ (show 4 < 7 by omega),
    var_succ t _ (show 5 < 7 by omega), var_succ t _ (show 6 < 7 by omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  apply WP.of_runBlock
  simp only [Impl.Sha512.AArch64.round, movImm64, List.cons_append, List.nil_append]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  simp only [T0, T1, T2, T3, pubRegs, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hs hs' hw ⊢
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, Size.bits, ite_true, ite_false, hs, hs', h0, h1, h2, h3, h4, h5, h6, h7, hw,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, trivial, trivial, trivial, fun r hr => ?_⟩
  rotate_right
  · have hr' : r ∈ pubRegs := by
      simpa only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] using hr
    obtain ⟨-, n1, n2, -⟩ := pub_ne r hr'
    have nh : r ≠ h := fun e => p7 (e ▸ hr')
    have nd : r ≠ d := fun e => p3 (e ▸ hr')
    simp only [T1, T2] at n1 n2
    simp only [nh, nd, n1, n2, ite_false]
  all_goals
    simp (config := {failIfUnchanged := false}) only [roundKW_0, roundKW_1, roundKW_2, roundKW_3,
      roundKW_4, roundKW_5, roundKW_6, roundKW_7, bsig1, ch_eq, bsig0, maj_eq, movz_movk64',
      BitVec.add_assoc]

theorem slot_ok (j : Nat) : slot j % 8 = 0 ∧ slot j < 32768 := by
  simp only [slot]; omega

/-- The address of `W[j mod 16]`. -/
abbrev slotAddr (scr : Addr) (j : Nat) : Addr := scr + BitVec.ofNat 64 (slot j)

theorem schedule_ok (t : Nat) (s : State) (M : Block) (bp scr : Addr)
    (hx1 : s.gpr .x1 = bp) (hx3 : s.gpr .x3 = scr)
    (hin : ∀ j, InRegions (s.rd ++ s.wr) (slotAddr scr j) 8)
    (hout : ∀ j, InRegions s.wr (slotAddr scr j) 8)
    (hbin : t < 16 → InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (8 * t)) 8)
    (hblk : t < 16 → rev64 (s.mem.readW (bp + BitVec.ofNat 64 (8 * t)) 64) = W M t)
    (hwin : 16 ≤ t → ∀ j, j < t → t ≤ j + 16 → s.mem.readW (slotAddr scr j) 64 = W M j) :
    WP isa (.block (schedule t)) s fun s' =>
      s'.gpr T0 = W M t ∧
      s'.mem = s.mem.writeW (slotAddr scr t) (W M t) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ T0 → r ≠ T1 → r ≠ T2 → r ≠ T3 → s'.gpr r = s.gpr r := by
  simp only [slotAddr] at hin hout hwin ⊢
  apply WP.of_runBlock
  by_cases ht : t < 16
  · have hi := hbin ht
    have hb := hblk ht
    have ho : 8 * t % 8 = 0 ∧ 8 * t < 32768 := by omega
    simp only [Impl.Sha512.AArch64.schedule, ht, ite_true, T0, T1, T2, T3]
    simp (config := {decide := true}) only [runBlock_cons, runStep_some,
      runBlock_nil, exec_ldr_x ho, exec_str_x (slot_ok _),
      exec_rev, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Size.bits, hx1, hx3, hi, hout, ite_true,
      ite_false, BitVec.setWidth_eq, hb,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, trivial, trivial, fun r h0 _ _ _ => ?_⟩
    simp [h0]
  · have hw := hwin (by omega)
    have e2 := hw (t - 2) (by omega) (by omega)
    have e7 := hw (t - 7) (by omega) (by omega)
    have e15 := hw (t - 15) (by omega) (by omega)
    have e16 := hw (t - 16) (by omega) (by omega)
    rw [show slot (t - 2) = slot (t + 14) by simp only [slot]; omega] at e2
    rw [show slot (t - 7) = slot (t + 9) by simp only [slot]; omega] at e7
    rw [show slot (t - 15) = slot (t + 1) by simp only [slot]; omega] at e15
    rw [show slot (t - 16) = slot t by simp only [slot]; omega] at e16
    simp only [Impl.Sha512.AArch64.schedule, ht, ite_false, T0, T1, T2, T3]
    simp (config := {decide := true}) only [runBlock_cons, runStep_some,
      runBlock_nil, exec_ldr_x (slot_ok _),
      exec_str_x (slot_ok _), exec_add, exec_logic, exec_ror_x, exec_lsr_x, isa, State.read,
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Size.bits, hx3, hin, hout, ite_true, ite_false,
      BitVec.setWidth_eq, e2, e7, e15, e16, Option.some.injEq, exists_eq_left']
    have hW := W_ge M (t := t) (by omega)
    refine ⟨by rw [hW]; rfl, by rw [hW]; rfl, trivial, trivial, fun r h0 h1 h2 h3 => ?_⟩
    simp [h0, h1, h2, h3]

/-! ## The 80 rounds -/

theorem work_ne' : ∀ r ∈ work, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 := by decide

theorem work_ne {r : Reg} (h : r ∈ work) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 := work_ne' r h

theorem pubRegs_ne' : ∀ r ∈ pubRegs, r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 := by decide

theorem pubRegs_ne {r : Reg} (h : r ∈ pubRegs) : r ≠ T0 ∧ r ≠ T1 ∧ r ≠ T2 ∧ r ≠ T3 :=
  pubRegs_ne' r h

/-- The window `⟨scr, 128⟩`. -/
abbrev winRegion (scr : Addr) : Region := ⟨scr, 128⟩

theorem win_contains (scr : Addr) (j : Nat) : (winRegion scr).Contains (slotAddr scr j) 8 := by
  simp only [slotAddr, slot]
  exact Offset.contains_base _ (by omega) (by omega)

theorem slot_sep (scr : Addr) {i j : Nat} (h : i % 16 ≠ j % 16) :
    Mem.Sep (slotAddr scr i) 8 (slotAddr scr j) 8 := by
  simp only [slotAddr, slot]
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
    (hrsi : sB.gpr .x1 = bp) (hrcx : sB.gpr .x3 = scr)
    (hin : ∀ j, InRegions (sB.rd ++ sB.wr) (slotAddr scr j) 8)
    (hout : ∀ j, InRegions sB.wr (slotAddr scr j) 8)
    (hbin : ∀ t : Nat, t < 16 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (8 * t)) 8)
    (hblk : ∀ m, Frame [winRegion scr] sB.mem m →
      ∀ t : Nat, t < 16 → rev64 (m.readW (bp + BitVec.ofNat 64 (8 * t)) 64) = W M t)
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
    have hs_rsi : s.gpr .x1 = bp := (hs.pub .x1 (by decide)).trans hrsi
    have hs_rcx : s.gpr .x3 = scr := (hs.pub .x3 (by decide)).trans hrcx
    refine WP.mono (schedule_ok t s M bp scr hs_rsi hs_rcx
      (by rw [hs.rd, hs.wr]; exact hin) (by rw [hs.wr]; exact hout)
      (fun h => by rw [hs.rd, hs.wr]; exact hbin t h) (hblk _ hs.frame t)
      (fun _ => hs.win)) fun s₁ ⟨hT0, hm₁, hrd₁, hwr₁, hr₁⟩ => ?_
    have hv₁ : Vars t s₁ (VG.Spec.Sha512.rounds H M t) := by
      have hv := hs.vars
      have e : ∀ k, s₁.gpr (var t k) = s.gpr (var t k) := fun k =>
        have := work_ne (var_mem t k); hr₁ _ this.1 this.2.1 this.2.2.1 this.2.2.2
      simp only [Vars, e] at hv ⊢
      exact hv
    refine WP.mono (round_ok t s₁ _ _ hv₁ hT0) fun s₂ ⟨hv₂, hm₂, hrd₂, hwr₂, hr₂⟩ => ?_
    refine ⟨?_, fun r hr => ?_, by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr], ?_, ?_⟩
    · have e : VG.Spec.Sha512.rounds H M (t + 1) =
          roundKW (VG.Spec.Sha512.rounds H M t) (K t) (W M t) := by
        rw [rounds_succ, round_eq]
      rw [e]; exact hv₂
    · have := pubRegs_ne hr
      rw [hr₂ r hr, hr₁ r this.1 this.2.1 this.2.2.1 this.2.2.2, hs.pub r hr]
    · rw [hm₂, hm₁]
      exact hs.frame.writeW (List.mem_singleton_self _) _ (win_contains scr t)
    · intro j hj hj'
      rw [hm₂, hm₁]
      by_cases hjt : j = t
      · subst hjt; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (slot_sep scr (by omega)) (by decide)]
        exact hs.win j (by omega) (by omega)

end VG.Proof.Sha512.AArch64

/-!
# SHA-512 compression function on AArch64: the whole function
-/

/-!
## SHA-512: the AArch64 contracts

The contracts the proofs are written against; the artifacts are emitted with the
shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
contracts of the AArch64 implementations of the compression function and the
streaming interface, in terms of `Spec/Sha512.lean`.

The return address is in the link register `x30`, which the target's
calling convention requires to be preserved (`VG.AArch64.abiPreserved`), not
on the stack, so unlike on x86-64 no region needs to be kept disjoint from it.
-/

namespace VG.Proof.Sha512

open Spec.Sha512

open VG.AArch64 in
/-- AArch64 contract for
`vg_sha512_compress(state: *mut [u64; 8], blocks: *const [u8; 128], n: usize, scratch: *mut [u64; 22])`:
updates the hash value at `state` with the `n` 128-byte blocks at `blocks`.

The code may read `blocks` (`128 * n` bytes) and read and write `state`
(64 bytes) and `scratch` (176 bytes, whose contents on exit are unspecified).
These may not overlap each other. The pointers and `n` are public; the hash
value and the blocks are secret. -/
def compressAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 64⟩
    let blocks : Region := ⟨s.gpr .x1, 128 * (s.gpr .x2).toNat⟩
    let scratch : Region := ⟨s.gpr .x3, 176⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .x0) =
      compressBlocks (stateAt s.mem (s.gpr .x0)) s.mem (s.gpr .x1) (s.gpr .x2).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for `vg_<alg>_init(state: *mut [u8; 192])`, where `iv` is
the initial hash value of `<alg>` (`H0_384`, `H0_512`, `H0_512_224` or
`H0_512_256`): makes the streaming state at `state` represent the empty
message, hashed from `iv`.

The code may write `state` (192 bytes). The pointer is public. -/
def initAArch64 (iv : HashValue) : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 192⟩
    s.rd = [] ∧ s.wr = [state]
  post s s' := Repr iv s'.mem (s.gpr .x0) []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for
`vg_sha512_update(state: *mut [u8; 192], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 28])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), hashed from any initial hash value, then afterwards it
represents `m` followed by the `len` bytes at `data`, from the same one.

The code may read `data` (`len` bytes) and read and write `state` (192
bytes) and `scratch` (224 bytes, whose contents on exit are unspecified).
These may not overlap each other. The pointers, `count` and `len` are public;
the state and the data are secret. -/
def updateAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 192⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 224⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch
  post s s' := ∀ iv m, Repr iv s.mem (s.gpr .x0) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
    Repr iv s'.mem (s.gpr .x0) (m ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for
`vg_sha512_finalize(state: *mut [u8; 192], count: u64, out: *mut [u8; 64], scratch: *mut [u64; 28])`:
if the streaming state at `state` represents a message `m` of `count` bytes,
fewer than 2⁶⁴, hashed from the initial hash value `iv`, writes the final
hash value `H⁽ᴺ⁾` of `m` from `iv` (64 bytes; `finalHash iv m`) to `out`. The
digest of SHA-384, SHA-512/224 or SHA-512/256 is its first 48, 28 or 32
bytes.

The code may read and write `state` (192 bytes, whose contents on exit are
unspecified), `out` (64 bytes) and `scratch` (224 bytes, whose contents on
exit are unspecified). These may not overlap each other. The pointers and
`count` are public; the state is secret. -/
def finalizeAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 192⟩
    let out : Region := ⟨s.gpr .x2, 64⟩
    let scratch : Region := ⟨s.gpr .x3, 224⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch
  post s s' := ∀ iv m, Repr iv s.mem (s.gpr .x0) m → m.length < 2 ^ 64 →
    s.gpr .x1 = BitVec.ofNat 64 m.length → bytesAt s'.mem (s.gpr .x2) 64 = finalHash iv m
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.Sha512


namespace VG.Proof.Sha512.AArch64

open VG VG.AArch64 VG.Impl.Sha512.AArch64
open VG.Spec.Sha512 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## Addresses and regions -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 8) (hk : k < 8) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofNat 64 (8 * j)) 8 (p + BitVec.ofNat 64 (8 * k)) 8 :=
  Offset.sep p (by omega) (by omega) (by omega)

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 8) (hk : k < 8)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (8 * k)) v).readW (p + BitVec.ofNat 64 (8 * j)) 64 =
    m.readW (p + BitVec.ofNat 64 (8 * j)) 64 :=
  Mem.readW_writeW_sep (word_sep p hj hk h) (by decide)

theorem stateAt_eq {m : Mem} {p : Addr} {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 8) → m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = v[k]) :
    stateAt m p = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  exact h k hk

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 8) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofNat 64 (8 * k)) 64 := by
  simp only [stateAt, Vector.getElem_ofFn]

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev bp : Addr := s₀.gpr .x1
abbrev nb : Nat := (s₀.gpr .x2).toNat
abbrev scr : Addr := s₀.gpr .x3
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev blR : Region := ⟨bp s₀, 128 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 176⟩
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

theorem pre_of (s₀ : State) (h : Proof.Sha512.compressAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem nb_lt : 128 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by simp only [slot]; omega) (by simp only [slot]; omega)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by simp only [slot]; omega) (by simp only [slot]; omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (8 * t)) 8 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (8 * t) =
    bp s₀ + BitVec.ofNat 64 (128 * i + 8 * t) from Offset.add_ofNat_add_ofNat _ _ _]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (8 * t)) 8 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x3 : s.gpr .x3 = scr s₀
  kept : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  x1 : s.gpr .x1 = blkAddr s₀ i
  x2 : s.gpr .x2 = BitVec.ofNat 64 (nb s₀ - i)

theorem preserved_sub : ∀ r ∈ preserved, r ∈ pubRegs := by decide

/-! ## One block -/

theorem load_eq : load = [
    .ldr .x .x4 .x0 (8 * 0), .ldr .x .x5 .x0 (8 * 1), .ldr .x .x6 .x0 (8 * 2),
    .ldr .x .x7 .x0 (8 * 3), .ldr .x .x8 .x0 (8 * 4), .ldr .x .x9 .x0 (8 * 5),
    .ldr .x .x10 .x0 (8 * 6), .ldr .x .x11 .x0 (8 * 7)] := by
  decide

theorem update_eq : update ++ advance = [
    .ldr .x .x12 .x0 (8 * 0), .ldr .x .x13 .x0 (8 * 1), .ldr .x .x14 .x0 (8 * 2),
    .ldr .x .x15 .x0 (8 * 3),
    .add .x .x4 .x4 .x12, .add .x .x5 .x5 .x13, .add .x .x6 .x6 .x14, .add .x .x7 .x7 .x15,
    .ldr .x .x12 .x0 (8 * (0 + 4)), .ldr .x .x13 .x0 (8 * (1 + 4)), .ldr .x .x14 .x0 (8 * (2 + 4)),
    .ldr .x .x15 .x0 (8 * (3 + 4)),
    .add .x .x8 .x8 .x12, .add .x .x9 .x9 .x13, .add .x .x10 .x10 .x14, .add .x .x11 .x11 .x15,
    .str .x .x4 .x0 (8 * 0), .str .x .x5 .x0 (8 * 1), .str .x .x6 .x0 (8 * 2),
    .str .x .x7 .x0 (8 * 3), .str .x .x8 .x0 (8 * 4), .str .x .x9 .x0 (8 * 5),
    .str .x .x10 .x0 (8 * 6), .str .x .x11 .x0 (8 * 7),
    .addImm .x .x1 .x1 128, .subImm .x .x2 .x2 1] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .x4 = v[0] ∧ s.gpr .x5 = v[1] ∧
    s.gpr .x6 = v[2] ∧ s.gpr .x7 = v[3] ∧
    s.gpr .x8 = v[4] ∧ s.gpr .x9 = v[5] ∧
    s.gpr .x10 = v[6] ∧ s.gpr .x11 = v[7] := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hx0 : s.gpr .x0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 8 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide); have h5 := hin 5 (by decide)
  have h6 := hin 6 (by decide); have h7 := hin 7 (by decide)
  apply WP.of_runBlock
  rw [load_eq]
  simp (config := {decide := true}) only [vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec_ldr_x, isa, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hx0,
    h0, h1, h2, h3, h4, h5, h6, h7, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  simp only [stateAt_get _ _ (show 0 < 8 by decide), stateAt_get _ _ (show 1 < 8 by decide),
    stateAt_get _ _ (show 2 < 8 by decide), stateAt_get _ _ (show 3 < 8 by decide),
    stateAt_get _ _ (show 4 < 8 by decide), stateAt_get _ _ (show 5 < 8 by decide),
    stateAt_get _ _ (show 6 < 8 by decide), stateAt_get _ _ (show 7 < 8 by decide)]
  simp (config := {decide := true}) [pubRegs]

/-- Eight 64-bit words written to consecutive addresses. -/
def writeState (m : Mem) (p : Addr) (v : HashValue) : Mem :=
  ((((((((m.writeW (p + BitVec.ofNat 64 (8 * 0)) v[0]).writeW
    (p + BitVec.ofNat 64 (8 * 1)) v[1]).writeW
    (p + BitVec.ofNat 64 (8 * 2)) v[2]).writeW
    (p + BitVec.ofNat 64 (8 * 3)) v[3]).writeW
    (p + BitVec.ofNat 64 (8 * 4)) v[4]).writeW
    (p + BitVec.ofNat 64 (8 * 5)) v[5]).writeW
    (p + BitVec.ofNat 64 (8 * 6)) v[6]).writeW
    (p + BitVec.ofNat 64 (8 * 7)) v[7])

set_option simprocs false in
theorem stateAt_writeState (m : Mem) (p : Addr) (v : HashValue) : stateAt (writeState m p v) p = v := by
  apply stateAt_eq
  intro k hk
  simp only [writeState]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with h | h | h | h | h | h | h | h <;> subst h <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW_writeW_word]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  have c : ∀ k, k < 8 → (stR s₀).Contains (st s₀ + BitVec.ofNat 64 (8 * k)) (64 / 8) :=
    fun k hk => contains_offset (by omega) (by omega)
  simp only [writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _ (c 6 ?_)).writeW ?_ _ (c 7 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hx0 : s.gpr .x0 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) → s.mem.readW (st s₀ + BitVec.ofNat 64 (8 * k)) 64 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .x1 = s.gpr .x1 + 128 ∧ s'.gpr .x2 = s.gpr .x2 - 1 ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.gpr .x3 = s.gpr .x3 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 8 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 8 → InRegions s.wr (st s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin (0 + 4) (by decide); have i5 := hin (1 + 4) (by decide)
  have i6 := hin (2 + 4) (by decide); have i7 := hin (3 + 4) (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide); have o5 := hout 5 (by decide)
  have o6 := hout 6 (by decide); have o7 := hout 7 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH (0 + 4) (by decide); have m5 := hH (1 + 4) (by decide)
  have m6 := hH (2 + 4) (by decide); have m7 := hH (3 + 4) (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec_ldr_x, exec_str_x, exec_add, exec_addImm_x, exec_subImm_x, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Size.bits, hx0,
    i0, i1, i2, i3, i4, i5, i6, i7, o0, o1, o2, o3, o4, o5, o6, o7,
    m0, m1, m2, m3, m4, m5, m6, m7, v0, v1, v2, v3, v4, v5, v6, v7, ite_true, ite_false,
    BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · simp only [writeState, Vector.getElem_zipWith]
  and_intros
  rotate_left 4
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true})
  all_goals trivial

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (128 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    rev64 (s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (8 * t)) 64) = W (blk s₀ i) t := by
  rw [W_lt _ ht, rev64_readW]
  simp only [blk, blockAt, parseBlock, Offset.add_ofNat_add_one, Nat.add_assoc, Nat.reduceAdd]

theorem win_sub (p : Addr) : Region.Sub (winRegion p) ⟨p, 176⟩ := Region.sub_prefix (by omega)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .x .x2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.x0 hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      rev64 (m.readW (blkAddr s₀ i + BitVec.ofNat 64 (8 * t)) 64) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  have hx1₁ : s₁.gpr .x1 = blkAddr s₀ i := (hpub₁ .x1 (by decide)).trans hL.x1
  have hx3₁ : s₁.gpr .x3 = scr s₀ := (hpub₁ .x3 (by decide)).trans hL.x3
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) _ (scr s₀) s₁ hx1₁ hx3₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 80 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hx0₂ : s₂.gpr .x0 = st s₀ := by rw [pub₂ .x0 (by decide), hL.x0]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hx0₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.frame.readW (contains_offset (by omega) (by omega)) hst (by decide), hm₁,
      stateAt_get _ _ hk]
  obtain ⟨hm₃, hx1₃, hx2₃, hx0₃, hx3₃, hkept₃, hrd₃, hwr₃⟩ := h₃
  have hx2 : s₂.gpr .x2 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [pub₂ .x2 (by decide), hL.x2, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
    rw [hm₃]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hx0₃, hx0₂], by rw [hx3₃, pub₂ .x3 (by decide), hL.x3],
      fun r hr => by rw [hkept₃ r hr, pub₂ r (preserved_sub r hr), hL.kept r hr],
      by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_⟩
    rw [hm₃, stateAt_writeState, compressBlocks_succ, ← hL.state]
    rfl
  have hev : eval (.nonzero .x .x2) s₃ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx2₃, hx2]
  have := hp.nb_lt
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon _ rfl with x1 := ?_, x2 := ?_ }⟩
    · rw [hx1₃, pub₂ .x1 (by decide), hL.x1]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (128 : BitVec _) = BitVec.ofNat _ 128 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [hx2₃, hx2]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha512.compressAArch64.post s₀ s' := by
  have hc₀ : Common s₀ 0 s₀ :=
    ⟨rfl, rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩
  refine WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s' hc => ⟨hc.kept, hc.state⟩
  refine WP.ite (s₀.gpr .x2 == 0) (by simp [eval, State.read]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₀ :=
      { hc₀ with
        x1 := by simp [blkAddr]
        x2 := by simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₀ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x3000, 176⟩]

theorem compress_verified :
    Verified AArch64.target Impl.Sha512.AArch64.compress Proof.Sha512.compressAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha512.AArch64
