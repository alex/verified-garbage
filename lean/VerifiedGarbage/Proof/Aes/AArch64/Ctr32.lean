import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Aes.AArch64.Group
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES counter mode on AArch64: the whole function

The prologue saves the callee-saved registers (checked by evaluation in the
naming domain, as is the epilogue restoring them), copies the counter block
to its slots and writes back the final counter; the key loop and the
group loop (`Group.lean`) do the rest.
-/

namespace VG.Proof.Aes

open Spec.Gcm

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for
`vg_aes_ctr32(schedule: *const [u8; 240], rounds: usize, counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])`:
XORs the AES counter-mode keystream from the counter block at `counter`
into the `n` blocks at `data`, and advances the counter block by `n`.

The code may read `schedule` (240 bytes) and read and write `counter` (16
bytes), `data` (`16 n` bytes) and `scratch` (2048 bytes, whose contents on
exit are unspecified). These may not overlap each other, and `data` may not
wrap around the end of the address space. `rounds` is 10, 12 or 14. The
pointers, `rounds` and `n` are public; the key schedule, the counter block
and the data are secret. -/
def ctr32AArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 240⟩
    let counter : Region := ⟨s.gpr .x2, 16⟩
    let data : Region := ⟨s.gpr .x3, 16 * (s.gpr .x4).toNat⟩
    let scratch : Region := ⟨s.gpr .x5, 2048⟩
    s.rd = [sched] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x3).toNat + 16 * (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    let ciph := aesWith (s.gpr .x1).toNat
      (Spec.Aes.bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)))
    blocksAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat =
        ctr32 ciph (blockAt s.mem (s.gpr .x2)) (blocksAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) ∧
      blockAt s'.mem (s.gpr .x2) = Nat.repeat inc32 (s.gpr .x4).toNat (blockAt s.mem (s.gpr .x2))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.sp = s₂.sp

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for
`vg_aes_expand_key(key: *const u8, key_len: usize, schedule: *mut [u8; 240], scratch: *mut [u64; 64])`:
writes the key schedule of the `key_len`-byte key at `key` to `schedule`.

The code may read `key` (`key_len` bytes) and read and write `schedule`
(240 bytes) and `scratch` (512 bytes, whose contents on exit are
unspecified). These may not overlap each other. `key_len` is 16, 24 or 32.
The pointers and `key_len` are public; the key is secret. -/
def expandKeyAArch64 : Contract AArch64.isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let sched : Region := ⟨s.gpr .x2, 240⟩
    let scratch : Region := ⟨s.gpr .x3, 512⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    ((s.gpr .x1).toNat = 16 ∨ (s.gpr .x1).toNat = 24 ∨ (s.gpr .x1).toNat = 32)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) (16 * (Spec.Aes.rounds ((s.gpr .x1).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers the code uses, in the order of `savedRegs`. -/
def sreg : Nat → Reg
  | 0 => .x19 | 1 => .x20 | 2 => .x21 | 3 => .x22 | 4 => .x23 | 5 => .x24 | 6 => .x25
  | 7 => .x26 | 8 => .x27 | _ => .x28

def saveCfg : Cfg := { base := sb, slots := 59, ext := sb, exts := 0 }

def saveEnv : Env Nat :=
  { reg := fun r => (List.range 10).find? (fun i => sreg i == r), slot := fun _ => none }

def savePost (e : Env Nat) : Bool := (List.range 10).all fun i => e.slot (48 + i) == some i

theorem save_check : check (names 64) saveCfg (fun _ => none) saveRegs saveEnv savePost = true := by
  decide +kernel

def restoreEnv : Env Nat :=
  { reg := fun _ => none, slot := fun k => if 48 ≤ k ∧ k < 58 then some (k - 48) else none }

def restorePost (e : Env Nat) : Bool := (List.range 10).all fun i => e.reg (sreg i) == some i

theorem restore_check :
    check (names 64) saveCfg (fun _ => none) restoreRegs restoreEnv restorePost = true := by
  decide +kernel

theorem saveCfg_ok {s : State} {b : Addr} {n : Nat} (hw : (⟨b, n⟩ : Region) ∈ s.wr)
    (hb : s.gpr sb = b) (hn : 8 * 59 ≤ n) : Ok saveCfg s :=
  Ok.of_region hw hb.symm hn (by simp [saveCfg]) rfl

/-- The saved registers are in slots 48–57. -/
def Saved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 10, m.readW (wordAddr b (48 + i)) 64 = s₀.gpr (sreg i)

theorem save_ok {s : State} {b : Addr} {n : Nat} (hw : (⟨b, n⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hn : 8 * 59 ≤ n) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b, 8 * 59⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ save_check
  let V : Nat → BitVec 64 := fun i => s.gpr (sreg i)
  have hrel : Rel (NameRel V) saveCfg (fun _ => none) saveEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ hk _ => by simp [saveCfg] at hk),
      (fun _ _ h => by cases h)⟩
    simp only [saveEnv] at h
    have h1 := List.find?_some h
    simp only [beq_iff_eq] at h1; subst h1; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) (saveCfg_ok hw hb hn) hrel he
  refine ⟨s', hs', fun i hi => ?_, funext fun r => p.other r ?_, p.rd, p.wr, ?_⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    have h := p.rel.slot (48 + i) i (by simp [saveCfg]; omega) this
    rw [p.base] at h
    simp only [saveCfg, hb] at h
    exact h
  · have : (saveRegs.all fun i => dstOf i != some r) = true := by
      simp [saveRegs, savedRegs, stS, dstOf]
    simp [this]
  · have := p.frame
    simpa [slotRegion, saveCfg, hb] using this

theorem restore_ok {s₀ s : State} {b : Addr} {n : Nat} (hw : (⟨b, n⟩ : Region) ∈ s.wr)
    (hb : s.gpr sb = b) (hn : 8 * 59 ≤ n) (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      Frame [⟨b, 8 * 59⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ restore_check
  let V : Nat → BitVec 64 := fun i => s₀.gpr (sreg i)
  have hrel : Rel (NameRel V) saveCfg (fun _ => none) restoreEnv s := by
    refine ⟨(fun r a h => by cases h), fun k a hk h => ?_, (fun _ _ hk _ => by simp [saveCfg] at hk),
      (fun _ _ h => by cases h)⟩
    simp only [restoreEnv] at h
    split at h
    · cases h
      rename_i hk'
      have := hs (k - 48) (by omega)
      rw [show 48 + (k - 48) = k by omega] at this
      simp only [NameRel, saveCfg, hb]
      exact this
    · cases h
  obtain ⟨s', hs', p⟩ := run (names_sound V) (saveCfg_ok hw hb hn) hrel he
  refine ⟨s', hs', fun i hi => ?_, ?_⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    exact p.rel.reg _ i this
  · have := p.frame
    simpa [slotRegion, saveCfg, hb] using this

/-! ## The counter block -/

/-- The memory after `ctrSetup`: the counter block's slots, and the final
counter written back. -/
def setupMem (m : Mem) (b ctr : Addr) (N : BitVec 64) : Mem :=
  let m₁ := m.writeW (b + BitVec.ofNat 64 (8 * 59)) (m.readW (ctr + BitVec.ofNat 64 0) 64)
  let m₂ := m₁.writeW (b + BitVec.ofNat 64 (8 * 60))
    ((m₁.readW (ctr + BitVec.ofNat 64 8) 32).setWidth 64)
  let c := rev32 (m₂.readW (ctr + BitVec.ofNat 64 12) 32)
  let m₃ := m₂.writeW (b + BitVec.ofNat 64 (8 * 61)) c
  m₃.writeW (ctr + BitVec.ofNat 64 12) (rev32 (c + N.setWidth 32))

set_option simprocs false in
theorem ctrSetup_ok {s : State} {b ctr : Addr} (hb : s.gpr .x5 = b) (hc : s.gpr .x2 = ctr)
    (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) (hcw : (⟨ctr, 16⟩ : Region) ∈ s.wr) :
    ∃ s', runBlock isa ctrSetup s = some s' ∧ s'.mem = setupMem s.mem b ctr (s.gpr .x4) ∧
      (∀ r, r ≠ .x6 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw' := List.mem_append_right s.rd hw
  have hcw' := List.mem_append_right s.rd hcw
  have l0 := in_off hcw' (off := 0) (n := 8) (by omega) (by omega)
  have l8 := in_off hcw' (off := 8) (n := 4) (by omega) (by omega)
  have l12 := in_off hcw' (off := 12) (n := 4) (by omega) (by omega)
  have w12 := in_off hcw (off := 12) (n := 4) (by omega) (by omega)
  have w59 := in_off hw (off := 8 * 59) (n := 8) (by omega) (by omega)
  have w60 := in_off hw (off := 8 * 60) (n := 8) (by omega) (by omega)
  have w61 := in_off hw (off := 8 * 61) (n := 4) (by omega) (by omega)
  refine ⟨_, by
    simp (config := {decide := true}) only [ctrSetup, stS, q, sb, cLo, cHi, cNum,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bytes,
      Size.bits, State.read, State.write, hb, hc, ite_false, ite_true, l0, l8, l12, w12, w59, w60, w61,
      Option.map_some, Option.bind_some, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨?_, fun r h => by simp [h], rfl, rfl⟩
  simp only [setupMem, Mem.writeW, Mem.readW, BitVec.setWidth_eq, sw_32]

theorem c_off (base : Addr) {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n :=
  Offset.contains_base base h ho

theorem out_of_disj {r₁ r₂ : Region} (hd : r₁.Disjoint r₂) {x a : Addr} {n : Nat} (hx : r₁.Contains x 1)
    (ha : r₂.Contains a n) : ¬ (x - a).toNat < n := fun h => hd x hx (ha.byte h)

section Setup

variable {m : Mem} {b ctr : Addr} {N : BitVec 64}

theorem setupMem_eq (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) :
    setupMem m b ctr N =
      (((m.writeW (b + BitVec.ofNat 64 (8 * 59)) (m.readW (ctr + BitVec.ofNat 64 0) 64)).writeW
        (b + BitVec.ofNat 64 (8 * 60)) ((m.readW (ctr + BitVec.ofNat 64 8) 32).setWidth 64)).writeW
        (b + BitVec.ofNat 64 (8 * 61)) (rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32))).writeW
        (ctr + BitVec.ofNat 64 12)
          (rev32 (rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) + N.setWidth 32)) := by
  have s8 : Mem.Sep (ctr + BitVec.ofNat 64 8) (32 / 8) (b + BitVec.ofNat 64 (8 * 59)) (64 / 8) :=
    hd.sep (c_off ctr (by omega) (by omega)) (c_off b (by omega) (by omega))
  have s12a : Mem.Sep (ctr + BitVec.ofNat 64 12) (32 / 8) (b + BitVec.ofNat 64 (8 * 59)) (64 / 8) :=
    hd.sep (c_off ctr (by omega) (by omega)) (c_off b (by omega) (by omega))
  have s12b : Mem.Sep (ctr + BitVec.ofNat 64 12) (32 / 8) (b + BitVec.ofNat 64 (8 * 60)) (64 / 8) :=
    hd.sep (c_off ctr (by omega) (by omega)) (c_off b (by omega) (by omega))
  simp only [setupMem]
  rw [Mem.readW_writeW_sep s8 (by decide), Mem.readW_writeW_sep s12b (by decide),
    Mem.readW_writeW_sep s12a (by decide)]

theorem setup_frame (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) :
    Frame [⟨b + BitVec.ofNat 64 (8 * 59), 20⟩, ⟨ctr, 16⟩] m (setupMem m b ctr N) := by
  rw [setupMem_eq hd]
  have h₀ : (⟨b + BitVec.ofNat 64 (8 * 59), 20⟩ : Region) ∈
      [(⟨b + BitVec.ofNat 64 (8 * 59), 20⟩ : Region), ⟨ctr, 16⟩] := by simp
  have h₁ : (⟨ctr, 16⟩ : Region) ∈ [(⟨b + BitVec.ofNat 64 (8 * 59), 20⟩ : Region), ⟨ctr, 16⟩] := by
    simp
  exact ((((Frame.refl _ _).writeW h₀ _ (off_contains b (by omega) (by omega) (by omega))).writeW h₀ _
    (off_contains b (by omega) (by omega) (by omega))).writeW h₀ _
    (off_contains b (by omega) (by omega) (by omega))).writeW h₁ _ (c_off ctr (by omega) (by omega))

theorem setup_slots (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) :
    cloW (setupMem m b ctr N) b = m.readW (ctr + BitVec.ofNat 64 0) 64 ∧
    chiW (setupMem m b ctr N) b = (m.readW (ctr + BitVec.ofNat 64 8) 32).setWidth 64 ∧
    numW (setupMem m b ctr N) b = rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) := by
  rw [setupMem_eq hd]
  have t : ∀ {k w}, 8 * k + w / 8 ≤ 2048 → Mem.Sep (b + BitVec.ofNat 64 (8 * k)) (w / 8)
      (ctr + BitVec.ofNat 64 12) (32 / 8) := fun h =>
    hd.symm.sep (c_off b h (by omega)) (c_off ctr (by omega) (by omega))
  refine ⟨?_, ?_, ?_⟩
  · rw [cloW, Mem.readW_writeW_sep (t (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep b (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep b (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [chiW, Mem.readW_writeW_sep (t (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep b (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [numW, Mem.readW_writeW_sep (t (by omega)) (by decide), Mem.readW_writeW_self32]

theorem writeW_apply {m : Mem} {a x : Addr} {w : Nat} (v : BitVec w) :
    m.writeW a v x = if (x - a).toNat < w / 8 then
      (v.setWidth (8 * (w / 8))).extractLsb' (8 * (x - a).toNat) 8 else m x := rfl

theorem setup_ctr (hd : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2048⟩) {k : Nat} (hk : k < 16) :
    setupMem m b ctr N (ctr + BitVec.ofNat 64 k) =
      if k < 12 then m (ctr + BitVec.ofNat 64 k)
      else (rev32 (rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) + N.setWidth 32)).extractLsb'
        (8 * (k - 12)) 8 := by
  rw [setupMem_eq hd, writeW_apply, off_toNat ctr (by omega) (by omega)]
  have hx : (⟨ctr, 16⟩ : Region).Contains (ctr + BitVec.ofNat 64 k) 1 := c_off ctr (by omega) (by omega)
  by_cases h : k < 12
  · rw [ite_eq_right (show ¬ 12 ≤ k by omega), ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega),
      ite_eq_left h, writeW_apply, ite_eq_right (out_of_disj hd hx (c_off b (by omega) (by omega))),
      writeW_apply, ite_eq_right (out_of_disj hd hx (c_off b (by omega) (by omega))),
      writeW_apply, ite_eq_right (out_of_disj hd hx (c_off b (by omega) (by omega)))]
  · rw [ite_eq_left (show 12 ≤ k by omega), ite_eq_left (show k - 12 < 32 / 8 by omega),
      ite_eq_right h, BitVec.setWidth_eq]

end Setup

/-! ## The counter block and the data, as blocks -/

/-- The counter, as the slot holds it. -/
theorem icb_lo (m : Mem) (ctr : Addr) :
    rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) = (Spec.Gcm.blockAt m ctr).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have e : t = 8 * (t / 8) + t % 8 := by omega
  rw [e, rev32_bit _ (by omega) (by omega), BitVec.getLsbD_extractLsb', Nat.zero_add,
    decide_eq_true (by omega : 8 * (t / 8) + t % 8 < 32), Bool.true_and,
    show 8 * (t / 8) + t % 8 = 8 * (15 - (15 - t / 8)) + t % 8 by omega,
    blockAt_bit _ _ (by omega) (by omega)]
  have hb := Mem.readW_byte m (ctr + BitVec.ofNat 64 12) (i := 3 - t / 8) (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 12 + (3 - t / 8) = 15 - t / 8 by omega] at hb
  rw [hb, BitVec.getLsbD_extractLsb']
  simp [show t % 8 < 8 by omega]

theorem ctr_after {m m' : Mem} {ctr : Addr} {n : Nat}
    (h : ∀ k < 16, m' (ctr + BitVec.ofNat 64 k) = if k < 12 then m (ctr + BitVec.ofNat 64 k)
      else (rev32 (rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) +
        (BitVec.ofNat 64 n).setWidth 32)).extractLsb' (8 * (k - 12)) 8) :
    Spec.Gcm.blockAt m' ctr = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt m ctr) := by
  refine block_ext fun k hk => ?_
  rw [toBytes_blockAt _ _ hk, h k hk, ctrBlock_byte _ _ hk]
  split
  · rw [toBytes_blockAt _ _ hk]
  · rw [icb_lo, show (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n by
      apply BitVec.eq_of_toNat_eq; simp]
    refine byte_ext fun j hj => ?_
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', rev32_bit _ (by omega) hj]
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega

theorem ctr32_of_dataInv {m₀ m : Mem} {D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (h : DataInv m₀ m D n n (keyStream R w icb)) :
    Spec.Gcm.blocksAt m D n =
      Spec.Gcm.ctr32 (Spec.Gcm.aesWith R w) icb (Spec.Gcm.blocksAt m₀ D n) := by
  unfold Spec.Gcm.ctr32 Spec.Gcm.keystream Spec.Gcm.blocksAt
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, List.length_map,
    List.length_range]
  simp only [List.length_map, List.length_range] at h1
  refine block_ext fun k hk => ?_
  rw [toBytes_xor _ _ hk, toBytes_blockAt _ _ hk, toBytes_blockAt _ _ hk, BitVec.add_assoc,
    ← BitVec.ofNat_add, h _ (by omega), ite_eq_left (by omega)]
  refine congrArg (_ ^^^ ·) ?_
  unfold Spec.Gcm.aesWith
  rw [toBytes_ofBytes (by simp) hk, keyStream, show (16 * i + k) / 16 = i by omega,
    show (16 * i + k) % 16 = k by omega, getD_eq _ hk, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hk, Option.getD_some]
  rfl

/-! ## Setting up the loops -/

theorem shl4 (x : BitVec 64) : x <<< 4 = BitVec.ofNat 64 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem keySetup_ok (s : State) :
    ∃ s', runBlock isa keySetup s = some s' ∧ s'.gpr .x2 = s.gpr .x1 + 1 ∧
      s'.gpr .x0 = s.gpr .x0 + s.gpr .x1 <<< 4 ∧
      s'.gpr .x1 = s.gpr sb + BitVec.ofNat 64 1920 ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x6 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [keySetup, q, sb, lastKey, runBlock_cons, runStep_some,
      runBlock_nil, exec, ite_true]
    rfl, ?_⟩
  refine ⟨by simp [State.write, State.read], by simp [State.write, State.read],
    by simp [State.write, State.read, sb], fun r h1 h2 h3 h4 => by simp [State.write, h1, h2, h3, h4],
    rfl, rfl, rfl⟩

theorem keyDone_ok (s : State) :
    ∃ s', runBlock isa keyDone s = some s' ∧ s'.gpr .x0 = s.gpr .x1 + 64 ∧
      (∀ r, r ≠ .x0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by rw [keyDone, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  exact ⟨by simp [State.write, State.read], fun r h => by simp [State.write, h], rfl, rfl, rfl⟩

/-! ## The whole function -/

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

/-- A frame within the writable regions. -/
theorem frame_wr {rs : List Region} {m m' : Mem} {C D b : Addr} {len : Nat} (hf : Frame rs m m')
    (h : ∀ r ∈ rs, Region.Sub r ⟨C, 16⟩ ∨ Region.Sub r ⟨D, len⟩ ∨ Region.Sub r ⟨b, 2048⟩) :
    Frame [⟨C, 16⟩, ⟨D, len⟩, ⟨b, 2048⟩] m m' :=
  hf.sub fun r hr => by
    rcases h r hr with h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩

theorem saved_frame {s₀ : State} {b : Addr} {m m' : Mem} {rs : List Region} (h : Saved s₀ b m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 384, 88⟩ r) :
    Saved s₀ b m' := fun i hi => by
  rw [← h i hi]
  exact hf.readW (off_contains b (by omega) (by omega) (by omega)) hd (by decide)

theorem notKeyWrites : ∀ r ∈ [Reg.x3, .x4, .x5], r ∉ keyWrites := by decide

theorem correct {s₀ : State} (hp : Proof.Aes.ctr32AArch64.pre s₀) :
    WP isa Impl.Aes.AArch64.ctr32 s₀ fun s' =>
      (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ Proof.Aes.ctr32AArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dSC, dSD, dSS, dCD, dCS, dDS, hwrap, hR⟩ := hp
  have hwC : (⟨s₀.gpr .x2, 16⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwD : (⟨s₀.gpr .x3, 16 * (s₀.gpr .x4).toNat⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwS : (⟨s₀.gpr .x5, 2048⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hrS : (⟨s₀.gpr .x0, 240⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  have n16 : 16 * (s₀.gpr .x4).toNat < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hc => dCD (s₀.gpr .x2) (by simp [Region.Contains]) ?_
    simp only [Region.Contains]
    have := (s₀.gpr .x2 - s₀.gpr .x3).isLt
    omega
  have hR14 : (s₀.gpr .x1).toNat ≤ 14 := by omega
  -- The prologue.
  unfold Impl.Aes.AArch64.ctr32
  refine WP.seq ?_
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  obtain ⟨s₁, h₁, sv₁, g₁, rd₁, wr₁, f₁⟩ := save_ok hwS rfl (by decide)
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  obtain ⟨s₂, h₂, m₂, o₂, rd₂, wr₂⟩ :=
    ctrSetup_ok (s := s₁) (b := s₀.gpr .x5) (ctr := s₀.gpr .x2) (by rw [g₁]) (by rw [g₁])
      (wr₁ ▸ hwS) (wr₁ ▸ hwC)
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  obtain ⟨s₃, h₃, x2₃, x0₃, x1₃, o₃, m₃, rd₃, wr₃⟩ := keySetup_ok s₂
  refine WP.of_runBlock ⟨s₃, h₃, ?_⟩
  -- Registers and memory after the prologue.
  have g₃ : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x6 → s₃.gpr r = s₀.gpr r :=
    fun r h1 h2 h3 h4 => by rw [o₃ r h1 h2 h3 h4, o₂ r h4, g₁]
  have hb₃ : s₃.gpr sb = s₀.gpr .x5 := g₃ _ (by decide) (by decide) (by decide) (by decide)
  have fS : Frame [⟨s₀.gpr .x5 + BitVec.ofNat 64 (8 * 59), 20⟩, ⟨s₀.gpr .x2, 16⟩] s₁.mem s₃.mem := by
    rw [m₃, m₂, g₁]; exact setup_frame dCS
  have f₀₃ : Frame [⟨s₀.gpr .x5, 2048⟩, ⟨s₀.gpr .x2, 16⟩] s₀.mem s₃.mem := by
    refine (f₁.sub fun r hr => ⟨⟨s₀.gpr .x5, 2048⟩, by simp, ?_⟩).trans
      (fS.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨s₀.gpr .x5, 2048⟩, by simp, scr_sub _ (by omega)⟩
      · exact ⟨⟨s₀.gpr .x2, 16⟩, by simp, sub_refl _⟩
  let R := (s₀.gpr .x1).toNat
  let w := Spec.Aes.bytesAt s₀.mem (s₀.gpr .x0) (16 * (R + 1))
  have hk : KSetup s₃ (s₀.gpr .x5) (s₀.gpr .x0) R w :=
    { scr := by rw [wr₃, wr₂, wr₁]; exact hwS
      base := hb₃
      sch := List.mem_append_left _ (by rw [rd₃, rd₂, rd₁]; exact hrS)
      sep := dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₃.bytes (R := ⟨s₀.gpr .x0, 240⟩) (fun r hr => ?_) (by simp) (by simp only; omega)).symm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dSS
        · exact dSC }
  have hi₃ : KInv s₃ (s₀.gpr .x5) (s₀.gpr .x0) R w R s₃ :=
    { hj := Nat.le_refl _
      x2 := by
        rw [x2₃, o₂ _ (by decide), g₁]
        simp only [R]
        exact Offset.add_one_eq _
      x0 := by rw [x0₃, o₂ _ (by decide), o₂ _ (by decide), g₁, shl4]
      x1 := by rw [x1₃, o₂ _ (by decide), g₁]; simp [keyAddr, sb]
      rd := rfl
      wr := rfl
      sp := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega) }
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₃) fun s₄ d₄ => ?_)
  refine WP.seq ?_
  obtain ⟨s₅, h₅, x0₅, o₅, m₅, rd₅, wr₅⟩ := keyDone_ok s₄
  refine WP.of_runBlock ⟨s₅, h₅, ?_⟩
  have g₅ : ∀ r ∈ [Reg.x3, .x4, .x5], s₅.gpr r = s₃.gpr r := fun r hr => by
    rw [o₅ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide),
      d₄.keep r (notKeyWrites r hr)]
  have x4₅ : s₅.gpr .x4 = s₀.gpr .x4 := by
    rw [g₅ _ (by simp), g₃ _ (by decide) (by decide) (by decide) (by decide)]
  have x3₅ : s₅.gpr .x3 = s₀.gpr .x3 := by
    rw [g₅ _ (by simp), g₃ _ (by decide) (by decide) (by decide) (by decide)]
  have hb₅ : s₅.gpr .x5 = s₀.gpr .x5 := by rw [g₅ _ (by simp)]; exact hb₃
  have hK0 : s₅.gpr .x0 = s₀.gpr .x5 + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [x0₅, d₄.x1]; simp only [keyAddr, Nat.sub_zero, BitVec.sub_add_cancel]
  have fK : Frame [⟨s₀.gpr .x5 + BitVec.ofNat 64 0, 384⟩, ⟨s₀.gpr .x5 + BitVec.ofNat 64 1024, 1024⟩]
      s₃.mem s₅.mem := m₅ ▸ d₄.frame
  have kd : ∀ {x lx}, 384 ≤ x → x + lx ≤ 1024 → ∀ r ∈ [(⟨s₀.gpr .x5 + BitVec.ofNat 64 0, 384⟩ : Region),
      ⟨s₀.gpr .x5 + BitVec.ofNat 64 1024, 1024⟩], Region.Disjoint ⟨s₀.gpr .x5 + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h1 h2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have cd : ∀ {x lx}, x + lx ≤ 16 → ∀ r ∈ [(⟨s₀.gpr .x5, 8 * 59⟩ : Region)],
      Region.Disjoint ⟨s₀.gpr .x2 + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (dCS.sub_right (Region.sub_prefix (by omega))).sub_left (Offset.sub_base _ h)
  obtain ⟨sl₁, sl₂, sl₃⟩ := setup_slots (m := s₁.mem) (N := s₁.gpr .x4) dCS
  rw [← m₂, ← m₃] at sl₁ sl₂ sl₃
  have clo₅ : cloW s₅.mem (s₀.gpr .x5) = s₀.mem.readW (s₀.gpr .x2) 64 := by
    rw [cloW, fK.readW (Region.contains_self _ _) (kd (by omega) (by omega)) (by decide), ← cloW, sl₁,
      f₁.readW (Region.contains_self _ _) (cd (by omega)) (by decide)]
    simp
  have chi₅ : chiW s₅.mem (s₀.gpr .x5) = (s₀.mem.readW (s₀.gpr .x2 + BitVec.ofNat 64 8) 32).setWidth 64 := by
    rw [chiW, fK.readW (Region.contains_self _ _) (kd (by omega) (by omega)) (by decide), ← chiW, sl₂,
      f₁.readW (Region.contains_self _ _) (cd (by omega)) (by decide)]
  have num₅ : numW s₅.mem (s₀.gpr .x5) = rev32 (s₀.mem.readW (s₀.gpr .x2 + BitVec.ofNat 64 12) 32) := by
    rw [numW, fK.readW (Region.contains_self _ _) (kd (by omega) (by omega)) (by decide), ← numW, sl₃,
      f₁.readW (Region.contains_self _ _) (cd (by omega)) (by decide)]
  let icb := Spec.Gcm.blockAt s₀.mem (s₀.gpr .x2)
  let n := (s₀.gpr .x4).toNat
  have hs : GSetup s₅ (s₀.gpr .x5) (s₀.gpr .x3) n R w icb :=
    { scr := by rw [wr₅, d₄.wr, wr₃, wr₂, wr₁]; exact hwS
      dat := by rw [wr₅, d₄.wr, wr₃, wr₂, wr₁]; exact hwD
      hn := n16
      sep := dDS
      rounds := hR
      keys := fun j hj => keyRel_congr (d₄.keys j hj) fun k hk => by
        rw [m₅, keyAddr, BitVec.add_assoc, ← BitVec.ofNat_add, show 1920 - 64 * R + 64 * j =
          1920 - 64 * (R - j) by omega]
      lo := fun i hi j hj => by
        rw [clo₅, readW_bit _ _ hi hj, blockAt_bit _ _ (by omega) hj]
      hi := fun i hi j hj => by
        rw [chi₅, BitVec.getLsbD_setWidth, show 8 * (7 - i) + j = 8 * (15 - (8 + i)) + j by omega,
          blockAt_bit _ _ (by omega) hj, BitVec.ofNat_add, ← BitVec.add_assoc,
          Mem.readW_byte s₀.mem (s₀.gpr .x2 + BitVec.ofNat 64 8) hi, BitVec.getLsbD_extractLsb']
        simp [hj, show 8 * i + j < 64 by omega]
      hi' := fun p hp => by
        rw [chi₅, BitVec.getLsbD_setWidth]
        simp [BitVec.getLsbD_of_ge _ _ hp] }
  -- The data is as on entry.
  have dd : ∀ r ∈ [(⟨s₀.gpr .x5, 2048⟩ : Region), ⟨s₀.gpr .x2, 16⟩],
      Region.Disjoint ⟨s₀.gpr .x3, 16 * n⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dDS
    · exact dCD.symm
  have data₅ : DataInv s₀.mem s₅.mem (s₀.gpr .x3) n 0 (keyStream R w icb) :=
    dataInv_frame fK (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact dDS.sub_right (scr_sub _ (by omega))) n16
      (dataInv_frame f₀₃ dd n16 fun i hi => by simp)
  refine WP.seq (WP.mono (Q := GDone s₀.mem s₅ (s₀.gpr .x5) (s₀.gpr .x3) n R w icb) ?_
    fun s₆ gd => ?_)
  · refine WP.ite (s₀.gpr .x4 == 0) (by simp [AArch64.eval, State.read, x4₅]) (fun h0 => ?_)
      (fun h0 => ?_)
    · have hn0 : n = 0 := by simp only [beq_iff_eq] at h0; simp [n, h0]
      exact WP.block_nil ⟨hb₅, rfl, rfl, Frame.refl _ _, fun i hi => by omega⟩
    · have hn0 : n ≠ 0 := by
        simp only [beq_eq_false_iff_ne, ne_eq] at h0
        intro h; apply h0; exact BitVec.eq_of_toNat_eq (by simpa [n] using h)
      refine groups_ok hs ⟨by omega, ?_, ?_, hb₅, hK0, rfl, rfl, Frame.refl _ _, ?_, data₅⟩
      · rw [x3₅]; simp
      · rw [x4₅]; simp [n]
      · rw [num₅, icb_lo]; simp [icb]
  -- The epilogue.
  have sv : Saved s₀ (s₀.gpr .x5) s₆.mem := by
    refine saved_frame (saved_frame (saved_frame sv₁ fS ?_) fK ?_) gd.frame ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact (dCS.sub_right (scr_sub _ (by omega))).symm
    · exact kd (by omega) (by omega)
    · intro r hr
      simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (scr_disj _ (by omega) (by omega)).symm
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact (dDS.sub_right (scr_sub _ (by omega))).symm
  obtain ⟨s₇, h₇, rg₇, fR⟩ :=
    restore_ok (by rw [gd.wr, wr₅, d₄.wr, wr₃, wr₂, wr₁]; exact hwS) gd.base (by decide) sv
  refine WP.of_runBlock ⟨s₇, h₇, ?_⟩
  have fsub : ∀ {x lx}, x + lx ≤ 2048 → Region.Sub ⟨s₀.gpr .x5 + BitVec.ofNat 64 x, lx⟩ ⟨s₀.gpr .x5, 2048⟩ :=
    fun h => scr_sub _ h
  refine ⟨rg₇, ?_, ?_⟩
  · exact ctr32_of_dataInv (dataInv_frame fR (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dDS.sub_right (Region.sub_prefix (by omega))) n16 gd.data)
  · refine ctr_after fun k hk => ?_
    have hC : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨s₀.gpr .x2, 16⟩ r) →
        m' (s₀.gpr .x2 + BitVec.ofNat 64 k) = m (s₀.gpr .x2 + BitVec.ofNat 64 k) :=
      fun hf hd => hf.bytes hd (by simp) hk
    rw [hC fR (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dCS.sub_right (Region.sub_prefix (by omega))),
      hC gd.frame (fun r hr => by
        simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dCS.sub_right (Region.sub_prefix (by omega))
        · exact dCS.sub_right (fsub (by omega))
        · exact dCD),
      hC fK (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact dCS.sub_right (fsub (by omega))),
      m₃, m₂, setup_ctr dCS hk, g₁,
      f₁.readW (Region.contains_self _ _) (cd (by omega)) (by decide)]
    split
    · exact hC f₁ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dCS.sub_right (Region.sub_prefix (by omega))
    · simp

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | .x5 => 0x4000
    | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 2048⟩]

theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32AArch64.pre s) :
    ∃ t s', Exec isa Impl.Aes.AArch64.ctr32 s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32AArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ :=
    WP.gprs (rs := [.x30]) (correct hs) (by decide +kernel) (by decide +kernel)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)
  · exact h₁ 9 (by omega)
  · exact h₃ _ (by simp)

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32AArch64.pre Proof.Aes.ctr32AArch64.pub
    Impl.Aes.AArch64.ctr32 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem ctr32_verified :
    Verified AArch64.target Impl.Aes.AArch64.ctr32 (Spec.Gcm.ctr32Contract AArch64.abi) :=
  Verified.of_correct ctr32_correct ctr32_ct (by
    sig_implies [Spec.Gcm.ctr32Contract, Spec.Gcm.ctr32Sig, Proof.Aes.ctr32AArch64, AArch64.abi,
      AArch64.argRegs] [Proof.Aes.AArch64.satState] using Proof.Aes.AArch64.satState)

end VG.Proof.Aes.AArch64
