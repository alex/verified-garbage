import VerifiedGarbage.Proof.Aes.Arm.Group
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Gcm.Contract

/-!
# AES counter mode on ARMv7: the whole function

The prologue saves the callee-saved registers (checked by evaluation in the
naming domain, as is the epilogue restoring them), copies the counter block
to its slots and writes back the final counter; the key loop
(`Keys.lean`) and the group loop (`Group.lean`) do the rest.
-/

namespace VG.Proof.Aes

open Spec.Gcm

open VG.Arm in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
32-bit ARM contract for `vg_aes_ctr32(schedule = r0, rounds = r1,
counter = r2, data = r3, n = [sp], scratch = [sp, #4])`: XORs the AES
counter-mode keystream from the counter block at `counter` into the `n`
blocks at `data`, and advances the counter block by `n`.

The code may read `schedule` (240 bytes) and the arguments on the stack (8
bytes at `sp`), and read and write `counter` (16 bytes), `data` (`16 n`
bytes) and `scratch` (2048 bytes, whose contents on exit are unspecified).
These may not overlap each other, and none may wrap around the end of the
(32-bit) address space. `rounds` is 10, 12 or 14. The pointers, `rounds` and
`n` are public; the key schedule, the counter block and the data are
secret. -/
def ctr32Arm : Contract Arm.isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let counter : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r3), 16 * (stackArg s 0).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 2048⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [sched, args] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    counter.Disjoint args ∧ data.Disjoint args ∧ scratch.Disjoint args ∧
    (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + 16 * (stackArg s 0).toNat ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 2048 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
    ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    let ciph := aesWith (s.gpr .r1).toNat
      (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0)) (16 * ((s.gpr .r1).toNat + 1)))
    blocksAt s'.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat =
        ctr32 ciph (blockAt s.mem (State.addr (s.gpr .r2)))
          (blocksAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat) ∧
      blockAt s'.mem (State.addr (s.gpr .r2)) =
        Nat.repeat inc32 (stackArg s 0).toNat (blockAt s.mem (State.addr (s.gpr .r2)))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.Aes

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_cmp wp_rev
  wp_ldr wp_str wp_ldrSp)
open VG.Proof.Aes (ctrBlock_byte toBytes_getD getD_eq byte_ext block_ext toBytes_blockAt blockAt_bit
  toBytes_xor toBytes_ofBytes)

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers the code uses, in the order of `savedRegs`. -/
def sreg : Nat → Reg
  | 0 => .r4 | 1 => .r5 | 2 => .r6 | 3 => .r7 | 4 => .r8 | 5 => .r9 | 6 => .r10 | 7 => .r11
  | _ => .lr

def saveCfg (b : Reg) : Cfg := { base := b, slots := 41, ext := b, exts := 0 }

def saveEnv : Env Nat :=
  { reg := fun r => (List.range 9).find? (fun i => sreg i == r), slot := fun _ => none }

def savePost (e : Env Nat) : Bool := (List.range 9).all fun i => e.slot (32 + i) == some i

theorem save_check12 :
    check (names 32) (saveCfg .r12) (fun _ => none) (saveRegs .r12) saveEnv savePost = true := by
  decide +kernel

theorem save_check8 :
    check (names 32) (saveCfg .r8) (fun _ => none) (saveRegs .r8) saveEnv savePost = true := by
  decide +kernel

def restoreEnv : Env Nat :=
  { reg := fun _ => none, slot := fun k => if 32 ≤ k ∧ k < 41 then some (k - 32) else none }

def restorePost (e : Env Nat) : Bool := (List.range 9).all fun i => e.reg (sreg i) == some i

theorem restore_check :
    check (names 32) (saveCfg .r12) (fun _ => none) (restoreRegs .r12) restoreEnv restorePost = true := by
  decide +kernel

/-- The saved registers are in slots 32–40. -/
def Saved (s₀ : State) (B : Addr) (m : Mem) : Prop :=
  ∀ i < 9, m.readW (slotA B (32 + i)) 32 = s₀.gpr (sreg i)

theorem saveCfg_ok {s : State} {b : BitVec 32} {br : Reg} {L : Nat} (hL : 4 * 41 ≤ L)
    (hw : (⟨State.addr b, L⟩ : Region) ∈ s.wr)
    (hfit : b.toNat + L ≤ 2 ^ 32) (hb : s.gpr br = b) : Ok (saveCfg br) s :=
  Ok.of_off (off := 0) hw hfit (by simp [saveCfg, hb]) (by simp [saveCfg]; omega) rfl

theorem save_ok {s : State} {b : BitVec 32} {br : Reg} {L : Nat} (hL : 4 * 41 ≤ L)
    (hw : (⟨State.addr b, L⟩ : Region) ∈ s.wr) (hfit : b.toNat + L ≤ 2 ^ 32) (hb : s.gpr br = b)
    (hchk : check (names 32) (saveCfg br) (fun _ => none) (saveRegs br) saveEnv savePost = true) :
    ∃ s', runBlock isa (saveRegs br) s = some s' ∧ Saved s (State.addr b) s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨State.addr b, 4 * 41⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  let V : Nat → BitVec 32 := fun i => s.gpr (sreg i)
  have hrel : Rel (NameRel V) (saveCfg br) (fun _ => none) saveEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ hk _ => by simp [saveCfg] at hk),
      (fun _ _ h => by cases h)⟩
    simp only [saveEnv] at h
    have h1 := List.find?_some h
    simp only [beq_iff_eq] at h1; subst h1; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) (saveCfg_ok hL hw hfit hb) hrel he
  refine ⟨s', hs', fun i hi => ?_, funext fun r => p.other r ?_, p.rd, p.wr, p.sp, ?_⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    have h := p.rel.slot (32 + i) i (by simp [saveCfg]; omega) this
    rw [p.base] at h
    simp only [saveCfg, hb] at h
    rw [← slot_addr' hfit (by omega)]
    exact h
  · have : ((saveRegs br).all fun i => dstOf i != some r) = true := by
      simp [saveRegs, savedRegs, dstOf]
    simp [this]
  · have := p.frame
    simpa [slotRegion, saveCfg, hb] using this

theorem restore_ok {s₀ s : State} {b : BitVec 32} {L : Nat} (hL : 4 * 41 ≤ L)
    (hw : (⟨State.addr b, L⟩ : Region) ∈ s.wr) (hfit : b.toNat + L ≤ 2 ^ 32) (hb : s.gpr .r12 = b) (hs : Saved s₀ (State.addr b) s.mem) :
    ∃ s', runBlock isa (restoreRegs .r12) s = some s' ∧ (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      Frame [⟨State.addr b, 4 * 41⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ restore_check
  let V : Nat → BitVec 32 := fun i => s₀.gpr (sreg i)
  have hrel : Rel (NameRel V) (saveCfg .r12) (fun _ => none) restoreEnv s := by
    refine ⟨(fun r a h => by cases h), fun k a hk h => ?_, (fun _ _ hk _ => by simp [saveCfg] at hk),
      (fun _ _ h => by cases h)⟩
    simp only [restoreEnv] at h
    split at h
    · cases h
      rename_i hk'
      have := hs (k - 32) (by omega)
      rw [show 32 + (k - 32) = k by omega, ← slot_addr' hfit (by simp [saveCfg] at hk; omega)] at this
      simp only [NameRel, saveCfg, hb]
      exact this
    · cases h
  obtain ⟨s', hs', p⟩ := run (names_sound V) (saveCfg_ok hL hw hfit hb) hrel he
  refine ⟨s', hs', fun i hi => ?_, ?_⟩
  · have := List.all_eq_true.mp hpost i (List.mem_range.mpr hi)
    simp only [beq_iff_eq] at this
    exact p.rel.reg _ i this
  · have := p.frame
    simpa [slotRegion, saveCfg, hb] using this

/-! ## The prologue -/

/-- The memory after the counter part of the prologue: the counter block's
slots, and the final counter written back. -/
def setupMem (m : Mem) (B C : Addr) (N : BitVec 32) : Mem :=
  ((((m.writeW (slotA B (cW 0)) (m.readW C 32)).writeW (slotA B (cW 1))
    (m.readW (C + BitVec.ofNat 64 4) 32)).writeW (slotA B (cW 2))
    (m.readW (C + BitVec.ofNat 64 8) 32)).writeW (slotA B cNum)
    (rev (m.readW (C + BitVec.ofNat 64 12) 32))).writeW (C + BitVec.ofNat 64 12)
    (rev (rev (m.readW (C + BitVec.ofNat 64 12) 32) + N))

/-- What the prologue needs: the scratch buffer at `b`, the counter block
at `c` (16 bytes), disjoint and not wrapping around. -/
structure PSetup (s : State) (b c : BitVec 32) : Prop where
  scr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr
  fit : b.toNat + 2048 ≤ 2 ^ 32
  ctr : (⟨State.addr c, 16⟩ : Region) ∈ s.wr
  fitC : c.toNat + 16 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr c, 16⟩ ⟨State.addr b, 2048⟩
  args : Region.Disjoint ⟨stackArgAddr s 0, 4⟩ ⟨State.addr b, 2048⟩
  r2 : s.gpr .r2 = c

theorem ctr_addr {c : BitVec 32} (hfit : c.toNat + 16 ≤ 2 ^ 32) {k : Nat} (hk : k < 16) :
    State.addr (c + BitVec.ofNat 32 k) = State.addr c + BitVec.ofNat 64 k := addr_add (by omega)

theorem sep_ctr_slot {b c : BitVec 32} (hd : Region.Disjoint ⟨State.addr c, 16⟩ ⟨State.addr b, 2048⟩)
    {x k : Nat} (hx : x + 4 ≤ 16) (hk : k < 512) :
    Mem.Sep (State.addr c + BitVec.ofNat 64 x) (32 / 8) (slotA (State.addr b) k) (32 / 8) :=
  hd.sep (by
    simp only [Region.Contains]
    rw [show State.addr c + BitVec.ofNat 64 x - State.addr c = BitVec.ofNat 64 x by bv_omega,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega) (by
    simp only [Region.Contains, slotA]
    rw [show State.addr b + BitVec.ofNat 64 (4 * k) - State.addr b = BitVec.ofNat 64 (4 * k) by bv_omega,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega)

/-- The counter part of the prologue. -/
theorem ctrSetup_wp {s : State} {b c : BitVec 32} (hp : PSetup s b c) (hb : s.gpr .r12 = b)
    {is : List Instr} {Q : State → Prop}
    (h : ∀ s', s'.mem = setupMem s.mem (State.addr b) (State.addr c) (stackArg s 0) →
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      WP isa (.block is) s' Q)
    (hsp : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4) :
    WP isa (.block (([.ldr t0 .r2 0, .str t0 .r12 (4 * cW 0), .ldr t0 .r2 4, .str t0 .r12 (4 * cW 1),
      .ldr t0 .r2 8, .str t0 .r12 (4 * cW 2),
      .ldr t0 .r2 12, .rev t0 t0, .str t0 .r12 (4 * cNum),
      .ldrSp t1 0, .dp .add t0 t0 (.reg t1), .rev t0 t0, .str t0 .r2 12] : List Instr) ++ is)) s Q := by
  have hfit := hp.fit
  have hfitC := hp.fitC
  have ca : ∀ {k : Nat}, k < 16 → ∀ s' : State, s'.gpr .r2 = c →
      State.addr (s'.gpr .r2 + BitVec.ofNat 32 k) = State.addr c + BitVec.ofNat 64 k :=
    fun hk s' h => by rw [h]; exact ctr_addr hfitC hk
  have sa : ∀ {k : Nat}, k < 512 → ∀ s' : State, s'.gpr .r12 = b →
      State.addr (s'.gpr .r12 + BitVec.ofNat 32 (4 * k)) = slotA (State.addr b) k :=
    fun hk s' h => by rw [h]; exact slot_addr hfit hk
  have cin : ∀ {x : Nat}, x + 4 ≤ 16 → ∀ rs, (⟨State.addr c, 16⟩ : Region) ∈ rs →
      InRegions rs (State.addr c + BitVec.ofNat 64 x) 4 := fun hx rs hr => by
    rw [← ctr_addr hfitC (by omega)]; exact in_off hr hfitC hx (by omega)
  have sin : ∀ {k : Nat}, k < 512 → InRegions s.wr (slotA (State.addr b) k) 4 :=
    fun hk => slot_in hp.scr hfit hk
  simp only [List.cons_append, List.nil_append]
  refine wp_ldr (by omega) (ca (k := 0) (by omega) s hp.r2) (cin (by omega) _
    (List.mem_append_right _ hp.ctr)) fun s₁ u₁ => ?_
  refine wp_str (by decide) (sa (by decide) s₁ (by rw [u₁.other _ (by decide), hb]))
    (by rw [u₁.wr]; exact sin (by decide)) fun s₂ u₂ => ?_
  have r2₂ : s₂.gpr .r2 = c := by rw [u₂.gpr, u₁.other _ (by decide), hp.r2]
  have r12₂ : s₂.gpr .r12 = b := by rw [u₂.gpr, u₁.other _ (by decide), hb]
  have wr₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  refine wp_ldr (by omega) (ca (k := 4) (by omega) s₂ r2₂) (cin (by omega) _
    (List.mem_append_right _ (wr₂ ▸ hp.ctr))) fun s₃ u₃ => ?_
  refine wp_str (by decide) (sa (by decide) s₃ (by rw [u₃.other _ (by decide), r12₂]))
    (by rw [u₃.wr, wr₂]; exact sin (by decide)) fun s₄ u₄ => ?_
  have r2₄ : s₄.gpr .r2 = c := by rw [u₄.gpr, u₃.other _ (by decide), r2₂]
  have r12₄ : s₄.gpr .r12 = b := by rw [u₄.gpr, u₃.other _ (by decide), r12₂]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, wr₂]
  refine wp_ldr (by omega) (ca (k := 8) (by omega) s₄ r2₄) (cin (by omega) _
    (List.mem_append_right _ (wr₄ ▸ hp.ctr))) fun s₅ u₅ => ?_
  refine wp_str (by decide) (sa (by decide) s₅ (by rw [u₅.other _ (by decide), r12₄]))
    (by rw [u₅.wr, wr₄]; exact sin (by decide)) fun s₆ u₆ => ?_
  have r2₆ : s₆.gpr .r2 = c := by rw [u₆.gpr, u₅.other _ (by decide), r2₄]
  have r12₆ : s₆.gpr .r12 = b := by rw [u₆.gpr, u₅.other _ (by decide), r12₄]
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, wr₄]
  refine wp_ldr (by omega) (ca (k := 12) (by omega) s₆ r2₆) (cin (by omega) _
    (List.mem_append_right _ (wr₆ ▸ hp.ctr))) fun s₇ u₇ => ?_
  refine wp_rev fun s₈ u₈ => ?_
  refine wp_str (by decide) (sa (by decide) s₈ (by rw [u₈.other _ (by decide), u₇.other _ (by decide), r12₆]))
    (by rw [u₈.wr, u₇.wr, wr₆]; exact sin (by decide)) fun s₉ u₉ => ?_
  refine wp_ldrSp (by omega) (a := stackArgAddr s 0) (by
      rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]; simp [stackArgAddr])
    (by rw [u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, wr₆]
        rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; exact hsp) fun s₁₀ u₁₀ => ?_
  refine wp_add (op2_reg _ _) fun s₁₁ u₁₁ => ?_
  refine wp_rev fun s₁₂ u₁₂ => ?_
  refine wp_str (by omega) (a := State.addr c + BitVec.ofNat 64 12)
    (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide)]; exact ca (by omega) s₆ r2₆)
    (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆]; exact cin (by omega) _ hp.ctr)
    fun s₁₃ u₁₃ => h s₁₃ ?_ (fun r h1 h2 => ?_) ?_ ?_ ?_
  · -- The memory.
    have m₂ : s₂.mem = s.mem.writeW (slotA (State.addr b) (cW 0)) (s.mem.readW (State.addr c) 32) := by
      rw [u₂.mem, u₁.gpr, u₁.mem]; simp
    have m₄ : s₄.mem = s₂.mem.writeW (slotA (State.addr b) (cW 1))
        (s.mem.readW (State.addr c + BitVec.ofNat 64 4) 32) := by
      rw [u₄.mem, u₃.gpr, u₃.mem, m₂, Mem.readW_writeW_sep (sep_ctr_slot hp.sep (by omega) (by decide))
        (by decide)]
    have m₆ : s₆.mem = s₄.mem.writeW (slotA (State.addr b) (cW 2))
        (s.mem.readW (State.addr c + BitVec.ofNat 64 8) 32) := by
      rw [u₆.mem, u₅.gpr, u₅.mem, m₄, Mem.readW_writeW_sep (sep_ctr_slot hp.sep (by omega) (by decide))
        (by decide), m₂, Mem.readW_writeW_sep (sep_ctr_slot hp.sep (by omega) (by decide)) (by decide)]
    have w₁₂ : s₆.mem.readW (State.addr c + BitVec.ofNat 64 12) 32 =
        s.mem.readW (State.addr c + BitVec.ofNat 64 12) 32 := by
      rw [m₆, Mem.readW_writeW_sep (sep_ctr_slot hp.sep (by omega) (by decide)) (by decide), m₄,
        Mem.readW_writeW_sep (sep_ctr_slot hp.sep (by omega) (by decide)) (by decide), m₂,
        Mem.readW_writeW_sep (sep_ctr_slot hp.sep (by omega) (by decide)) (by decide)]
    have m₉ : s₉.mem = s₆.mem.writeW (slotA (State.addr b) cNum)
        (rev (s.mem.readW (State.addr c + BitVec.ofNat 64 12) 32)) := by
      rw [u₉.mem, u₈.gpr, u₇.gpr, u₈.mem, u₇.mem, w₁₂]
    have sa0 : ∀ {k : Nat}, k < 512 → Mem.Sep (stackArgAddr s 0) (32 / 8) (slotA (State.addr b) k) (32 / 8) :=
      fun {k} hk => hp.args.sep (Region.contains_self _ _) (by
        simp only [Region.Contains, slotA]
        rw [show State.addr b + BitVec.ofNat 64 (4 * k) - State.addr b = BitVec.ofNat 64 (4 * k) by bv_omega,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega)
    have v₁₀ : s₉.mem.readW (stackArgAddr s 0) 32 = stackArg s 0 := by
      rw [m₉, Mem.readW_writeW_sep (sa0 (by decide)) (by decide), m₆,
        Mem.readW_writeW_sep (sa0 (by decide)) (by decide), m₄,
        Mem.readW_writeW_sep (sa0 (by decide)) (by decide), m₂,
        Mem.readW_writeW_sep (sa0 (by decide)) (by decide)]
      rfl
    rw [u₁₃.mem, u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.gpr,
      u₁₂.mem, u₁₁.mem, u₁₀.mem, v₁₀, m₉, w₁₂, m₆, m₄, m₂]
    rfl
  · rw [u₁₃.gpr, u₁₂.other _ h1, u₁₁.other _ h1, u₁₀.other _ h2, u₉.gpr, u₈.other _ h1,
      u₇.other _ h1, u₆.gpr, u₅.other _ h1, u₄.gpr, u₃.other _ h1, u₂.gpr, u₁.other _ h1]
  · rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆]
  · rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

section Setup

variable {m : Mem} {b c : BitVec 32} {N : BitVec 32}

theorem c_off (C : Addr) {x n : Nat} (h : x + n ≤ 16) :
    (⟨C, 16⟩ : Region).Contains (C + BitVec.ofNat 64 x) n := by
  simp only [Region.Contains]
  rw [show C + BitVec.ofNat 64 x - C = BitVec.ofNat 64 x by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem s_off {B : Addr} {L : Nat} (hL : L < 2 ^ 64) {k : Nat} (h : 4 * k + 4 ≤ L) :
    (⟨B, L⟩ : Region).Contains (slotA B k) 4 := by
  simp only [Region.Contains, slotA]
  rw [show B + BitVec.ofNat 64 (4 * k) - B = BitVec.ofNat 64 (4 * k) by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem slots_frame (B : Addr) {k : Nat} (h1 : 41 ≤ k) (h2 : k < 45) :
    (⟨B + BitVec.ofNat 64 164, 16⟩ : Region).Contains (slotA B k) (32 / 8) := by
  simp only [Region.Contains, slotA]
  rw [show B + BitVec.ofNat 64 (4 * k) - (B + BitVec.ofNat 64 164) = BitVec.ofNat 64 (4 * k - 164) by
    bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem setup_frame :
    Frame [⟨State.addr b + BitVec.ofNat 64 164, 16⟩, ⟨State.addr c, 16⟩] m
      (setupMem m (State.addr b) (State.addr c) N) := by
  have h₀ : (⟨State.addr b + BitVec.ofNat 64 164, 16⟩ : Region) ∈
      [(⟨State.addr b + BitVec.ofNat 64 164, 16⟩ : Region), ⟨State.addr c, 16⟩] := by simp
  have h₁ : (⟨State.addr c, 16⟩ : Region) ∈
      [(⟨State.addr b + BitVec.ofNat 64 164, 16⟩ : Region), ⟨State.addr c, 16⟩] := by simp
  exact (((((Frame.refl _ _).writeW h₀ _ (slots_frame _ (by decide) (by decide))).writeW h₀ _
    (slots_frame _ (by decide) (by decide))).writeW h₀ _ (slots_frame _ (by decide) (by decide))).writeW
    h₀ _ (slots_frame _ (by decide) (by decide))).writeW h₁ _ (c_off _ (by omega))

theorem setup_cw (hd : Region.Disjoint ⟨State.addr c, 16⟩ ⟨State.addr b, 2048⟩) {k : Nat} (hk : k < 3) :
    cwW (setupMem m (State.addr b) (State.addr c) N) (State.addr b) k =
      m.readW (State.addr c + BitVec.ofNat 64 (4 * k)) 32 := by
  have t : Mem.Sep (slotA (State.addr b) (cW k)) (32 / 8) (State.addr c + BitVec.ofNat 64 12) (32 / 8) :=
    hd.symm.sep (s_off (by decide) (by simp [cW]; omega)) (c_off _ (by omega))
  simp only [cwW, setupMem]
  rw [Mem.readW_writeW_sep t (by decide),
    readW_writeW_slot _ _ (by simp [cW]; omega) (by decide) (by simp [cW, cNum]; omega)]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · rw [readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    simp
  · rw [readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

theorem setup_num (hd : Region.Disjoint ⟨State.addr c, 16⟩ ⟨State.addr b, 2048⟩) :
    numW (setupMem m (State.addr b) (State.addr c) N) (State.addr b) =
      rev (m.readW (State.addr c + BitVec.ofNat 64 12) 32) := by
  have t : Mem.Sep (slotA (State.addr b) cNum) (32 / 8) (State.addr c + BitVec.ofNat 64 12) (32 / 8) :=
    hd.symm.sep (s_off (by decide) (by decide)) (c_off _ (by omega))
  simp only [numW, setupMem]
  rw [Mem.readW_writeW_sep t (by decide), Mem.readW_writeW_self32]

theorem writeW_apply {m : Mem} {a x : Addr} {w : Nat} (v : BitVec w) :
    m.writeW a v x = if (x - a).toNat < w / 8 then
      (v.setWidth (8 * (w / 8))).extractLsb' (8 * (x - a).toNat) 8 else m x := rfl

theorem setup_ctr (hd : Region.Disjoint ⟨State.addr c, 16⟩ ⟨State.addr b, 2048⟩) {k : Nat} (hk : k < 16) :
    setupMem m (State.addr b) (State.addr c) N (State.addr c + BitVec.ofNat 64 k) =
      if k < 12 then m (State.addr c + BitVec.ofNat 64 k)
      else (rev (rev (m.readW (State.addr c + BitVec.ofNat 64 12) 32) + N)).extractLsb'
        (8 * (k - 12)) 8 := by
  simp only [setupMem]
  rw [writeW_apply, off_toNat _ (by omega) (by omega)]
  have hx : (⟨State.addr c, 16⟩ : Region).Contains (State.addr c + BitVec.ofNat 64 k) 1 :=
    c_off _ (by omega)
  by_cases h : k < 12
  · rw [ite_eq_right (show ¬ 12 ≤ k by omega), ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega),
      ite_eq_left h, writeW_apply, ite_eq_right (out_of_disj hd hx (s_off (by decide) (by decide))),
      writeW_apply, ite_eq_right (out_of_disj hd hx (s_off (by decide) (by decide))),
      writeW_apply, ite_eq_right (out_of_disj hd hx (s_off (by decide) (by decide))),
      writeW_apply, ite_eq_right (out_of_disj hd hx (s_off (by decide) (by decide)))]
  · rw [ite_eq_left (show 12 ≤ k by omega), ite_eq_left (show k - 12 < 32 / 8 by omega),
      ite_eq_right h, BitVec.setWidth_eq]

end Setup

/-! ## The counter block and the data, as blocks -/

/-- The counter, as the slot holds it. -/
theorem icb_lo (m : Mem) (C : Addr) :
    rev (m.readW (C + BitVec.ofNat 64 12) 32) = (Spec.Gcm.blockAt m C).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have e : t = 8 * (t / 8) + t % 8 := by omega
  rw [e, rev_bit _ (by omega) (by omega), BitVec.getLsbD_extractLsb', Nat.zero_add,
    decide_eq_true (by omega : 8 * (t / 8) + t % 8 < 32), Bool.true_and,
    show 8 * (t / 8) + t % 8 = 8 * (15 - (15 - t / 8)) + t % 8 by omega,
    blockAt_bit _ _ (by omega) (by omega)]
  have hb := Mem.readW_byte m (C + BitVec.ofNat 64 12) (i := 3 - t / 8) (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 12 + (3 - t / 8) = 15 - t / 8 by omega] at hb
  rw [hb, BitVec.getLsbD_extractLsb']
  simp [show t % 8 < 8 by omega]

theorem ctr_after {m m' : Mem} {C : Addr} {n : Nat}
    (h : ∀ k < 16, m' (C + BitVec.ofNat 64 k) = if k < 12 then m (C + BitVec.ofNat 64 k)
      else (rev (rev (m.readW (C + BitVec.ofNat 64 12) 32) + BitVec.ofNat 32 n)).extractLsb' (8 * (k - 12)) 8) :
    Spec.Gcm.blockAt m' C = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt m C) := by
  refine block_ext fun k hk => ?_
  rw [toBytes_blockAt _ _ hk, h k hk, ctrBlock_byte _ _ hk]
  split
  · rw [toBytes_blockAt _ _ hk]
  · rw [icb_lo]
    refine byte_ext fun j hj => ?_
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', rev_bit _ (by omega) hj]
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega

theorem ctr32_of_dataInv {m₀ m : Mem} {D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (h : DataInv m₀ m D n (4 * n) (keyStream R w icb)) :
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

/-! ## The whole function -/

section
variable (s₀ : State)

abbrev scP : BitVec 32 := s₀.gpr .r0
abbrev ctP : BitVec 32 := s₀.gpr .r2
abbrev dP : BitVec 32 := s₀.gpr .r3
abbrev nB : Nat := (stackArg s₀ 0).toNat
abbrev bP : BitVec 32 := stackArg s₀ 1
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨State.addr (scP s₀), 240⟩, argR s₀]
  wr : s₀.wr = [⟨State.addr (ctP s₀), 16⟩, ⟨State.addr (dP s₀), 16 * nB s₀⟩, ⟨State.addr (bP s₀), 2048⟩]
  dSC : Region.Disjoint ⟨State.addr (scP s₀), 240⟩ ⟨State.addr (ctP s₀), 16⟩
  dSD : Region.Disjoint ⟨State.addr (scP s₀), 240⟩ ⟨State.addr (dP s₀), 16 * nB s₀⟩
  dSS : Region.Disjoint ⟨State.addr (scP s₀), 240⟩ ⟨State.addr (bP s₀), 2048⟩
  dCD : Region.Disjoint ⟨State.addr (ctP s₀), 16⟩ ⟨State.addr (dP s₀), 16 * nB s₀⟩
  dCS : Region.Disjoint ⟨State.addr (ctP s₀), 16⟩ ⟨State.addr (bP s₀), 2048⟩
  dDS : Region.Disjoint ⟨State.addr (dP s₀), 16 * nB s₀⟩ ⟨State.addr (bP s₀), 2048⟩
  dCA : Region.Disjoint ⟨State.addr (ctP s₀), 16⟩ (argR s₀)
  dDA : Region.Disjoint ⟨State.addr (dP s₀), 16 * nB s₀⟩ (argR s₀)
  dSA : Region.Disjoint ⟨State.addr (bP s₀), 2048⟩ (argR s₀)
  fitS : (scP s₀).toNat + 240 ≤ 2 ^ 32
  fitC : (ctP s₀).toNat + 16 ≤ 2 ^ 32
  fitD : (dP s₀).toNat + 16 * nB s₀ ≤ 2 ^ 32
  fitB : (bP s₀).toNat + 2048 ≤ 2 ^ 32
  fitSp : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rounds : (s₀.gpr .r1).toNat = 10 ∨ (s₀.gpr .r1).toNat = 12 ∨ (s₀.gpr .r1).toNat = 14

theorem pre_of {s₀ : State} (h : Proof.Aes.ctr32Arm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem argAddr_one (s : State) (h : s.sp.toNat + 8 ≤ 2 ^ 32) :
    stackArgAddr s 1 = stackArgAddr s 0 + BitVec.ofNat 64 4 := by
  simp only [stackArgAddr]
  rw [show (4 * 0 : Nat) = 0 from rfl, BitVec.add_zero, addr_add (by omega)]

theorem arg_in {s : State} (hsp : s.sp.toNat + 8 ≤ 2 ^ 32) (hr : argR s ∈ s.rd) {i : Nat} (hi : i < 2) :
    InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4 := by
  refine ⟨argR s, List.mem_append_left _ hr, ?_⟩
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simp [Region.Contains]
  · rw [argAddr_one s hsp]
    simp only [Region.Contains]
    rw [show stackArgAddr s 0 + BitVec.ofNat 64 4 - stackArgAddr s 0 = BitVec.ofNat 64 4 by bv_omega]
    decide

/-- The stack arguments are as on entry. -/
theorem stackArg_frame {s s' : State} {rs : List Region} (hf : Frame rs s.mem s'.mem) (hsp : s'.sp = s.sp)
    (h8 : s.sp.toNat + 8 ≤ 2 ^ 32) (hd : ∀ r ∈ rs, Region.Disjoint (argR s) r) {i : Nat} (hi : i < 2) :
    stackArg s' i = stackArg s i := by
  simp only [stackArg, stackArgAddr, hsp]
  refine hf.readW ?_ hd (by decide)
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simp [Region.Contains, stackArgAddr]
  · have := argAddr_one s h8
    simp only [stackArgAddr] at this
    rw [show 4 * 1 = 4 from rfl, this]
    simp only [Region.Contains, stackArgAddr]
    rw [show State.addr (s.sp + BitVec.ofNat 32 (4 * 0)) + BitVec.ofNat 64 4 -
      State.addr (s.sp + BitVec.ofNat 32 (4 * 0)) = BitVec.ofNat 64 4 by bv_omega]
    decide

theorem shl4 (x : BitVec 32) : x <<< 4 = BitVec.ofNat 32 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem off_disjoint' (B : Addr) {x lx y ly : Nat} (h : x + lx ≤ y ∨ y + ly ≤ x)
    (hx : x + lx < 2 ^ 64) (hy : y + ly < 2 ^ 64) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 x, lx⟩ ⟨B + BitVec.ofNat 64 y, ly⟩ := off_disjoint B h hx hy

theorem sub_scr (B : Addr) {x lx : Nat} (h : x + lx ≤ 2048) :
    Region.Sub ⟨B + BitVec.ofNat 64 x, lx⟩ ⟨B, 2048⟩ := scr_sub B h

theorem keyArea_sub (b : BitVec 32) : Region.Sub (keyArea b) ⟨State.addr b, 2048⟩ := sub_scr _ (by omega)

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Aes.Arm.ctr32 s₀ fun s' =>
      (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ Proof.Aes.ctr32Arm.post s₀ s' := by
  have hR14 : (s₀.gpr .r1).toNat ≤ 14 := by rcases hp.rounds with h | h | h <;> omega
  have hfit := hp.fitB
  have hwS : (⟨State.addr (bP s₀), 2048⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have hwC : (⟨State.addr (ctP s₀), 16⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have hwD : (⟨State.addr (dP s₀), 16 * nB s₀⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have hrS : (⟨State.addr (scP s₀), 240⟩ : Region) ∈ s₀.rd := by rw [hp.rd]; simp
  have hrA : argR s₀ ∈ s₀.rd := by rw [hp.rd]; simp
  let b := bP s₀
  let B := State.addr b
  -- The prologue.
  unfold Impl.Aes.Arm.ctr32
  refine WP.seq ?_
  simp only [prologue, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldrSp (by omega) (a := stackArgAddr s₀ 1) rfl (arg_in hp.fitSp hrA (by omega))
    fun s₁ u₁ => ?_
  have hb₁ : s₁.gpr .r12 = b := u₁.gpr
  rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₂, h₂, sv₂, g₂, rd₂, wr₂, sp₂, f₂⟩ := save_ok (by decide) (by rw [u₁.wr]; exact hwS) hfit hb₁ save_check12
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  have sv₂' : Saved s₀ B s₂.mem := fun i hi => by
    rw [sv₂ i hi]
    have : sreg i ≠ .r12 := by revert hi; revert i; decide
    exact u₁.other _ this
  have f₀₂ : Frame [⟨B, 4 * 41⟩] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have sp₂' : s₂.sp = s₀.sp := by rw [sp₂, u₁.sp]
  have argD : ∀ {x lx : Nat}, x + lx ≤ 2048 →
      Region.Disjoint (argR s₀) ⟨State.addr (bP s₀) + BitVec.ofNat 64 x, lx⟩ := fun h =>
    (hp.dSA.sub_left (sub_scr _ h)).symm
  have argB : ∀ {lx : Nat}, lx ≤ 2048 → Region.Disjoint (argR s₀) ⟨State.addr (bP s₀), lx⟩ := fun h =>
    (hp.dSA.sub_left (Region.sub_prefix h)).symm
  have arg₂ : ∀ i < 2, stackArg s₂ i = stackArg s₀ i := fun i hi =>
    stackArg_frame f₀₂ sp₂' hp.fitSp (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact argB (by omega)) hi
  have ps : PSetup s₂ b (ctP s₀) :=
    { scr := by rw [wr₂, u₁.wr]; exact hwS
      fit := hfit
      ctr := by rw [wr₂, u₁.wr]; exact hwC
      fitC := hp.fitC
      sep := hp.dCS
      args := by
        simp only [stackArgAddr, sp₂']
        exact (argB (lx := 2048) (by omega)).sub_left (Region.sub_prefix (by omega))
      r2 := by rw [g₂, u₁.other _ (by decide)] }
  refine ctrSetup_wp ps (by rw [g₂, hb₁]) (fun s₃ m₃ o₃ rd₃ wr₃ sp₃ => ?_)
    (by rw [rd₂, wr₂, u₁.rd, u₁.wr]; simp only [stackArgAddr, sp₂']
        exact arg_in hp.fitSp hrA (i := 0) (by omega))
  -- The key loop's setup.
  have r0₃ : s₃.gpr .r0 = scP s₀ := by rw [o₃ _ (by decide) (by decide), g₂, u₁.other _ (by decide)]
  have r1₃ : s₃.gpr .r1 = s₀.gpr .r1 := by rw [o₃ _ (by decide) (by decide), g₂, u₁.other _ (by decide)]
  have r3₃ : s₃.gpr .r3 = dP s₀ := by rw [o₃ _ (by decide) (by decide), g₂, u₁.other _ (by decide)]
  have r12₃ : s₃.gpr .r12 = b := by rw [o₃ _ (by decide) (by decide), g₂, hb₁]
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (VG.Proof.MdStream.Arm.op2_lsl (by decide))
    fun s₅ u₅ => wp_add (op2_imm (by decide)) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ =>
    WP.block_nil ?_
  have m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, rd₂, u₁.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂, u₁.wr]
  have sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, sp₃, sp₂']
  let R := (s₀.gpr .r1).toNat
  let w := Spec.Aes.bytesAt s₀.mem (State.addr (scP s₀)) (16 * (R + 1))
  have f₂₃ : Frame [⟨B + BitVec.ofNat 64 164, 16⟩, ⟨State.addr (ctP s₀), 16⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact setup_frame
  have f₀₇ : Frame [⟨B, 2048⟩, ⟨State.addr (ctP s₀), 16⟩] s₀.mem s₇.mem := by
    rw [m₇]
    refine (f₀₂.sub fun r hr => ⟨⟨B, 2048⟩, by simp, ?_⟩).trans (f₂₃.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨B, 2048⟩, by simp, sub_scr _ (by omega)⟩
      · exact ⟨⟨State.addr (ctP s₀), 16⟩, by simp, fun _ h => h⟩
  have hk : KSetup s₇ b (scP s₀) R w :=
    { scr := by rw [wr₇]; exact hwS
      fit := hfit
      sch := List.mem_append_left _ (by rw [rd₇]; exact hrS)
      fitS := hp.fitS
      sep := hp.dSS
      rounds := hR14
      w := fun i hi => by
        simp only [w, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hi, Option.map_some, Option.getD_some]
        refine (f₀₇.bytes (R := ⟨State.addr (scP s₀), 240⟩) (fun r hr => ?_) (by simp)
          (by simp only; omega)).symm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.dSS
        · exact hp.dSC }
  have hi₇ : KInv s₇ b (scP s₀) R w R s₇ :=
    { hj := Nat.le_refl _
      lr := by
        rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), r1₃]
        simp only [R]; bv_omega
      r12 := by
        rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), r0₃,
          u₄.other _ (by decide), r1₃, shl4]
      kp := by
        rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, r12₃]
        simp [keyAddr, lastKey]
      rd := rfl
      wr := rfl
      sp := rfl
      keep := fun _ _ => rfl
      frame := Frame.refl _ _
      done := fun i h1 h2 => absurd h2 (by omega) }
  have r8₇ : s₇.gpr .r8 = dP s₀ := by rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
    u₄.other _ (by decide), r3₃]
  -- The key loop.
  refine WP.seq (WP.mono (keyLoop_ok hk hi₇) fun s₈ d₈ => ?_)
  have f₀₈ : Frame [⟨B, 2048⟩, ⟨State.addr (ctP s₀), 16⟩] s₀.mem s₈.mem :=
    f₀₇.trans (d₈.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨B, 2048⟩, by simp, keyArea_sub _⟩)
  have argv : ∀ (s : State), s.sp = s₀.sp →
      Frame [⟨B, 2048⟩, ⟨State.addr (ctP s₀), 16⟩] s₀.mem s.mem →
      ∀ i < 2, s.mem.readW (stackArgAddr s₀ i) 32 = stackArg s₀ i := fun s hsp hf i hi => by
    have := stackArg_frame hf hsp hp.fitSp (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact argB (by omega)
      · exact hp.dCA.symm) hi
    simp only [stackArg, stackArgAddr, hsp] at this
    exact this
  -- After the key loop.
  refine WP.seq ?_
  simp only [keyDone, List.cons_append, List.nil_append]
  have sp₈ : s₈.sp = s₀.sp := by rw [d₈.sp, sp₇]
  refine wp_add (op2_imm (by decide)) fun s₉ u₉ => wp_mov (op2_reg _ _) fun s₁₀ u₁₀ => ?_
  have sp₁₀ : s₁₀.sp = s₀.sp := by rw [u₁₀.sp, u₉.sp, sp₈]
  have rd₁₀ : s₁₀.rd = s₀.rd := by rw [u₁₀.rd, u₉.rd, d₈.rd, rd₇]
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, u₉.wr, d₈.wr, wr₇]
  have m₁₀ : s₁₀.mem = s₈.mem := by rw [u₁₀.mem, u₉.mem]
  refine wp_ldrSp (by omega) (a := stackArgAddr s₀ 0) (by simp [stackArgAddr, sp₁₀])
    (by rw [rd₁₀, wr₁₀]; exact arg_in hp.fitSp hrA (by omega)) fun s₁₁ u₁₁ => ?_
  refine wp_ldrSp (by omega) (a := stackArgAddr s₀ 1) (by simp [stackArgAddr, u₁₁.sp, sp₁₀])
    (by rw [u₁₁.rd, u₁₁.wr, rd₁₀, wr₁₀]; exact arg_in hp.fitSp hrA (by omega)) fun s₁₂ u₁₂ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₁₃ f₁₃ z₁₃ => WP.block_nil ?_
  have n₁₂ : s₁₂.gpr .r11 = stackArg s₀ 0 := by
    rw [u₁₂.other _ (by decide), u₁₁.gpr, m₁₀, argv s₈ sp₈ f₀₈ 0 (by omega)]
  have n₁₃ : s₁₃.gpr .r11 = stackArg s₀ 0 := by rw [f₁₃.gpr, n₁₂]
  have b₁₃ : s₁₃.gpr sb = b := by
    rw [f₁₃.gpr, u₁₂.gpr, u₁₁.mem, m₁₀, argv s₈ sp₈ f₀₈ 1 (by omega)]
  have d₁₃ : s₁₃.gpr .r10 = dP s₀ := by
    rw [f₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      d₈.keep _ (by decide), r8₇]
  have k₁₃ : s₁₃.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R) := by
    rw [f₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr,
      d₈.kp]
    simp only [keyAddr, Nat.sub_zero, BitVec.sub_add_cancel]
  have m₁₃ : s₁₃.mem = s₈.mem := by rw [f₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀]
  have rd₁₃ : s₁₃.rd = s₀.rd := by rw [f₁₃.rd, u₁₂.rd, u₁₁.rd, rd₁₀]
  have wr₁₃ : s₁₃.wr = s₀.wr := by rw [f₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀]
  have sp₁₃ : s₁₃.sp = s₀.sp := by rw [f₁₃.sp, u₁₂.sp, u₁₁.sp, sp₁₀]
  -- The counter block's slots.
  have fK : Frame [keyArea b] s₃.mem s₁₃.mem := by rw [m₁₃, ← m₇]; exact d₈.frame
  have kd : ∀ {x lx : Nat}, x + lx ≤ 1024 → ∀ r ∈ [keyArea b],
      Region.Disjoint ⟨B + BitVec.ofNat 64 x, lx⟩ r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact off_disjoint _ (by omega) (by omega) (by omega)
  have cd : ∀ {x lx : Nat}, x + lx ≤ 16 → ∀ r ∈ [(⟨B, 4 * 41⟩ : Region)],
      Region.Disjoint ⟨State.addr (ctP s₀) + BitVec.ofNat 64 x, lx⟩ r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    refine (hp.dCS.sub_right (Region.sub_prefix (by omega))).sub_left ?_
    exact VG.Proof.MdStream.Arm.sub_offset h (by omega)
  let icb := Spec.Gcm.blockAt s₀.mem (State.addr (ctP s₀))
  let n := nB s₀
  have cw₁₃ : ∀ k < 3, cwW s₁₃.mem B k = s₀.mem.readW (State.addr (ctP s₀) + BitVec.ofNat 64 (4 * k)) 32 := by
    intro k hk
    rw [cwW, fK.readW (Region.contains_self _ _) (kd (by simp [cW]; omega)) (by decide), ← cwW, m₃,
      setup_cw hp.dCS hk, f₀₂.readW (Region.contains_self _ _) (cd (by omega)) (by decide)]
  have num₁₃ : numW s₁₃.mem B = rev (s₀.mem.readW (State.addr (ctP s₀) + BitVec.ofNat 64 12) 32) := by
    rw [numW, fK.readW (Region.contains_self _ _) (kd (by decide)) (by decide), ← numW, m₃,
      setup_num hp.dCS, f₀₂.readW (Region.contains_self _ _) (cd (by omega)) (by decide)]
  have hs : GSetup s₁₃ b (dP s₀) n R w icb :=
    { scr := by rw [wr₁₃]; exact hwS
      fit := hfit
      dat := by rw [wr₁₃]; exact hwD
      fitD := hp.fitD
      sep := hp.dDS
      rounds := hp.rounds
      keys := fun j hj => keyRel_congr (d₈.keys j hj) fun k hk => by
        rw [m₁₃, keyAddr, add_ofNat_ofNat, show lastKey - 32 * R + 32 * j = lastKey - 32 * (R - j) by
          simp only [lastKey]; omega]
      words := fun k hk t ht j hj => by
        rw [cw₁₃ k hk, readW_bit _ _ ht hj, BitVec.add_assoc, ← BitVec.ofNat_add,
          blockAt_bit _ _ (by omega) hj] }
  -- The data is as on entry.
  have data₁₃ : DataInv s₀.mem s₁₃.mem (State.addr (dP s₀)) n 0 (keyStream R w icb) := by
    intro i hi
    simp only [Nat.mul_zero, Nat.not_lt_zero, ite_false]
    have xz : ∀ x : Byte, x ^^^ 0 = x := fun x => by ext i; simp
    rw [m₁₃, xz]
    refine f₀₈.bytes (R := ⟨State.addr (dP s₀), 16 * n⟩) (fun r hr => ?_)
      (by simp only; have := hp.fitD; omega) hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dDS
    · exact hp.dCD.symm
  refine WP.seq (WP.mono (Q := GDone s₀.mem s₁₃ b (dP s₀) n R w icb) ?_ fun s₁₄ gd => ?_)
  · have e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by bv_omega
    refine WP.ite (stackArg s₀ 0 == 0) (by simp only [Arm.eval, z₁₃, n₁₂, e0]) (fun h0 => ?_)
      (fun h0 => ?_)
    · have hn0 : n = 0 := by
        simp only [beq_iff_eq] at h0; show (stackArg s₀ 0).toNat = 0; rw [h0]; rfl
      exact WP.block_nil ⟨b₁₃, rfl, rfl, rfl, Frame.refl _ _, fun i hi => by omega⟩
    · have hn0 : n ≠ 0 := by
        simp only [beq_eq_false_iff_ne, ne_eq] at h0
        intro h; apply h0; exact BitVec.eq_of_toNat_eq (by simpa [n] using h)
      refine groups_ok hs ⟨by omega, by rw [d₁₃]; simp, ?_, k₁₃, b₁₃, rfl, rfl, rfl, Frame.refl _ _,
        by rw [num₁₃, icb_lo]; simp [icb], data₁₃⟩
      rw [n₁₃]; simp only [n, nB, Nat.mul_zero, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- The epilogue.
  have sv : Saved s₀ B s₁₄.mem := by
    intro i hi
    have c : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨slotA B (32 + i), 32 / 8⟩ r) →
        m'.readW (slotA B (32 + i)) 32 = m.readW (slotA B (32 + i)) 32 :=
      fun hf hd => hf.readW (Region.contains_self _ _) hd (by decide)
    rw [c gd.frame (slot_disj_regions hp.dDS (by omega) (by omega) (by omega)), m₁₃,
      c d₈.frame (kd (by omega)), m₇, c f₂₃ ?_, sv₂' i hi]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact off_disjoint _ (by omega) (by omega) (by omega)
    · exact (hp.dCS.sub_right (sub_scr (x := 4 * (32 + i)) (lx := 32 / 8) _ (by omega))).symm
  refine wp_ldrSp (by omega) (a := stackArgAddr s₀ 1) (by simp [stackArgAddr, gd.sp, sp₁₃])
    (by rw [gd.rd, gd.wr, rd₁₃, wr₁₃]; exact arg_in hp.fitSp hrA (by omega)) fun s₁₅ u₁₅ => ?_
  have f₀₁₄ : Frame [⟨B, 2048⟩, ⟨State.addr (ctP s₀), 16⟩, ⟨State.addr (dP s₀), 16 * n⟩]
      s₀.mem s₁₄.mem := by
    refine (f₀₈.mono fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp).trans ?_
    rw [← m₁₃]
    refine gd.frame.sub fun r hr => ?_
    simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨B, 2048⟩, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨B, 2048⟩, by simp, sub_scr _ (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have b₁₅ : s₁₅.gpr .r12 = b := by
    rw [u₁₅.gpr]
    have := stackArg_frame f₀₁₄ (by rw [gd.sp, sp₁₃]) hp.fitSp (i := 1) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact argB (by omega)
      · exact hp.dCA.symm
      · exact hp.dDA.symm) (by omega)
    simp only [stackArg, stackArgAddr, gd.sp, sp₁₃] at this
    exact this
  obtain ⟨s₁₆, h₁₆, rg₁₆, fR⟩ := restore_ok (s₀ := s₀) (by decide) (by rw [u₁₅.wr, gd.wr, wr₁₃]; exact hwS) hfit
    b₁₅ (by rw [u₁₅.mem]; exact sv)
  refine WP.of_runBlock ⟨s₁₆, h₁₆, rg₁₆, ?_, ?_⟩
  · -- The data.
    rw [u₁₅.mem] at fR
    exact ctr32_of_dataInv (dataInv_frame fR (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.dDS.sub_right (Region.sub_prefix (by omega))) (by have := hp.fitD; omega) gd.data)
  · -- The counter block.
    rw [u₁₅.mem] at fR
    refine ctr_after fun k hk => ?_
    have hC : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨State.addr (ctP s₀), 16⟩ r) →
        m' (State.addr (ctP s₀) + BitVec.ofNat 64 k) = m (State.addr (ctP s₀) + BitVec.ofNat 64 k) :=
      fun hf hd => hf.bytes hd (by simp) hk
    rw [hC fR (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.dCS.sub_right (Region.sub_prefix (by omega))),
      hC gd.frame (fun r hr => by
        simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.dCS.sub_right (Region.sub_prefix (by omega))
        · exact hp.dCS.sub_right (sub_scr _ (by omega))
        · exact hp.dCD),
      m₁₃, hC d₈.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.dCS.sub_right (keyArea_sub _)),
      m₇, m₃, setup_ctr hp.dCS hk, arg₂ 0 (by omega),
      f₀₂.readW (Region.contains_self _ _) (cd (by omega)) (by decide)]
    split
    · exact hC f₀₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.dCS.sub_right (Region.sub_prefix (by omega))
    · simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32Arm.pre s) :
    ∃ t s', Exec isa Impl.Aes.Arm.ctr32 s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32Arm.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of hs)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega)
  · exact h₁ 1 (by omega)
  · exact h₁ 2 (by omega)
  · exact h₁ 3 (by omega)
  · exact h₁ 4 (by omega)
  · exact h₁ 5 (by omega)
  · exact h₁ 6 (by omega)
  · exact h₁ 7 (by omega)
  · exact h₁ 8 (by omega)

/-! ## Constant time -/

/-- The initial taint: the pointers, `rounds` and the stack arguments are
public; `r2` and `r3` point at the counter block and the data. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [16, 0, 2048],
    bases := [(.r2, 0), (.r3, 1)], argLen := 8, argBases := [(4, 2)] }

theorem wf₀ {s : State} (h : Proof.Aes.ctr32Arm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have e : (⟨State.addr s.sp, 8⟩ : Region) = argR s := by simp [argR, stackArgAddr]
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hp.fitSp, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil]
    exact ⟨⟨hp.dCD, hp.dCS⟩, hp.dDS, fun _ h => h.elim, trivial⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    have := hp.fitC; have := hp.fitD; have := hp.fitB
    rintro r (rfl | rfl | rfl) <;> simp only [VG.Proof.MdStream.Arm.addr_toNat] <;> omega
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]
  · simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.dCA.symm
    · exact hp.dDA.symm
    · exact hp.dSA.symm
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Aes.ctr32Arm.pre s₁) (h₂ : Proof.Aes.ctr32Arm.pre s₂)
    (hpub : Proof.Aes.ctr32Arm.pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0, a1⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [ctP, dP, nB, bP, p2, p3, a0, a1]
  · simp only [τ₀] at hk
    rw [VG.Proof.MdStream.Arm.argByte_eq hp₁.fitSp hk, VG.Proof.MdStream.Arm.argByte_eq hp₂.fitSp hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : k / 4 = 0 ∨ k / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32Arm.pre Proof.Aes.ctr32Arm.pub Impl.Aes.Arm.ctr32 :=
  VG.Taint.constantTime (A := VG.Arm.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

/-- A state satisfying the precondition (with no data, and the scratch buffer at 0). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0, 2048⟩]

theorem ctr32_verified :
    Verified Arm.target Impl.Aes.Arm.ctr32 (Spec.Gcm.ctr32Contract Arm.abi) :=
  Verified.of_correct ctr32_correct ctr32_ct (by
    sig_implies [Spec.Gcm.ctr32Contract, Spec.Gcm.ctr32Sig, Proof.Aes.ctr32Arm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Aes.Arm.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
      using Proof.Aes.Arm.sat)

end VG.Proof.Aes.Arm
