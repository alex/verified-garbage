import VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheMeta
import VerifiedGarbage.Proof.Argon2.X86_64.AddressCallsPrepare
import VerifiedGarbage.Proof.Argon2.X86_64.AddressCalls

/-! Merged from `Proof.Argon2.X86_64.AddressGeneration`. -/
section
/-! Merged from `Proof.Argon2.X86_64.AddressCallsMx`. -/
section
/-! The baseline independent-address calls preserve all MXCSR bits. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCalls

theorem compression_noMx : VG.Impl.Argon2.X86_64.compress.allInstrs (fun i => !loadsMxcsr i) = true :=
  by lit_decide

theorem stage_noMx (x y out : Nat) : (stage x y out).allInstrs (fun i => !loadsMxcsr i) = true := by
  change ((Code.block (args x y out) : Prog isa).allInstrs (fun i => !loadsMxcsr i) &&
    VG.Impl.Argon2.X86_64.compress.allInstrs (fun i => !loadsMxcsr i)) = true
  rw [compression_noMx]
  rfl

theorem calls_noMx : calls.allInstrs (fun i => !loadsMxcsr i) = true := by
  change ((stage 7168 5120 4096).allInstrs (fun i => !loadsMxcsr i) &&
    (stage 7168 4096 6144).allInstrs (fun i => !loadsMxcsr i)) = true
  rw [stage_noMx, stage_noMx]
  rfl

theorem calls_mx_ok (p : Spec.Argon2.Params) (pass lane slice counter : Nat) (s : State) (h : Ready s)
    (zero : Spec.Argon2.blockAt s.mem (off (work s) 7168) = Spec.Argon2.zeroBlock)
    (input : Spec.Argon2.blockAt s.mem (off (work s) 5120) =
      Proof.Argon2.addressInput p pass lane slice counter) :
    WP isa calls s fun t => Generated s t p pass lane slice counter ∧ t.mxcsr = s.mxcsr :=
  WP.mono_mx calls_noMx (calls_ok p pass lane slice counter s h zero input)
    (fun _ generated mx => ⟨generated, mx⟩)

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! Complete independent-address generation against the reviewed algorithm. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCalls

theorem code_ok (p : Params) (pass lane slice counter : Nat) (s : State) (h : Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (words : AddressHeader.Words p pass lane slice counter s) :
    WP isa code s fun t => Generated s t p pass lane slice counter ∧ t.mxcsr = s.mxcsr := by
  unfold code
  refine WP.seq ((prepare_ok p pass lane slice counter s h reads words).mono ?_)
  intro a prepared
  have zero : blockAt a.mem (off (work a) 7168) = zeroBlock := by
    rw [prepared.stable.work_eq]; exact prepared.zero
  have input : blockAt a.mem (off (work a) 5120) = Proof.Argon2.addressInput p pass lane slice counter := by
    rw [prepared.stable.work_eq]; exact prepared.input
  refine (calls_mx_ok p pass lane slice counter a prepared.stable.ready zero input).mono ?_
  rintro t ⟨generated, mx⟩
  have frame := generated.frame
  rw [writes, prepared.stable.work_eq, prepared.stable.regs .rsp (by simp [calleeSaved])] at frame
  have firstFrame : Frame (writes s) s.mem a.mem :=
    prepared.stable.frame.mono (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simp [writes])
  refine ⟨⟨?_, generated.ready, generated.work.trans prepared.stable.work_eq,
    fun r hr => (generated.regs r hr).trans (prepared.stable.regs r hr),
    generated.rd.trans prepared.stable.rd, generated.wr.trans prepared.stable.wr,
    firstFrame.trans frame⟩, mx.trans prepared.stable.mxcsr⟩
  have block := generated.block
  rw [prepared.stable.work_eq] at block
  exact block

end VG.Proof.Argon2.X86_64.AddressCalls
end

/-! Merged from `Proof.Argon2.X86_64.AddressCacheSave`. -/
section
/-! Save the public cache counter without disturbing scratch or header fields. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCache

theorem save_ok (s : State) (hw : InRegions s.wr (off (s.gpr .rbp) 8) 8) :
    WP isa (.block save) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rbp) 8) (s.gpr .rax) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [save, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    ea_at, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

structure Saved (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .rbp) 8) (s.gpr .rax)
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  ready : AddressCalls.Ready t
  work_eq : AddressCalls.work t = AddressCalls.work s
  frame : Frame [⟨off (s.gpr .rbp) 8, 8⟩] s.mem t.mem

theorem save_ready (s : State) (h : AddressCalls.Ready s)
    (hw : InRegions s.wr (off (s.gpr .rbp) 8) 8) : WP isa (.block save) s (Saved s) := by
  refine (save_ok s hw).mono ?_
  rintro t ⟨mem, regs, rd, wr, mx⟩
  have work' : AddressCalls.work t = AddressCalls.work s := by
    unfold AddressCalls.work
    rw [regs, mem, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
  have ready : AddressCalls.Ready t := by
    constructor
    · rw [rd, wr, regs]; exact h.frameRead
    · rw [work', wr]; exact h.workWrite
    · rw [regs, work']; exact h.frameWork
    · rw [regs]; exact h.frameStack
    · rw [regs, work']; exact h.stackWork
  refine ⟨mem, regs, rd, wr, mx, ready, work', ?_⟩
  rw [mem]
  exact (Frame.refl _ _).writeW (r := ⟨off (s.gpr .rbp) 8, 8⟩) (by simp) _
    (Region.contains_self _ _)

theorem Saved.read {s t : State} (h : Saved s t) (d : Nat)
    (hd : d + 8 ≤ 8 ∨ 16 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [h.regs, h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ hd (by omega) (by decide)) (by decide)

theorem Saved.words {s t : State} {p : Params} {pass lane slice old counter : Nat}
    (h : Saved s t) (words : AddressHeader.Words p pass lane slice old s)
    (value : s.gpr .rax = BitVec.ofNat 64 counter) :
    AddressHeader.Words p pass lane slice counter t := by
  refine ⟨(h.read 0 (by decide) (by decide)).trans words.passWord,
    ?_, ?_, (h.read 240 (by decide) (by decide)).trans words.blocksWord,
    (h.read 72 (by decide) (by decide)).trans words.passesWord,
    (h.read 112 (by decide) (by decide)).trans words.variantWord, ?_⟩
  · rw [h.regs]; exact words.laneWord
  · rw [h.regs]; exact words.sliceWord
  · rw [h.regs, h.mem, Mem.readW_writeW_self64, value]

end VG.Proof.Argon2.X86_64.AddressCache
end

/-! Regenerate only when the public one-based block counter changes. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCache

def wanted (s : State) : Nat := (s.gpr .r15).toNat / 128 + 1

def writes (s : State) : List Region :=
  [⟨AddressCalls.work s, 8192⟩, below (s.gpr .rsp) 8, ⟨off (s.gpr .rbp) 8, 8⟩]

structure Ready (p : Params) (pass lane slice old : Nat) (s : State) : Prop where
  layout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  write : InRegions s.wr (off (s.gpr .rbp) 8) 8
  words : AddressHeader.Words p pass lane slice old s
  cached : counter (s.gpr .r15) = s.mem.readW (off (s.gpr .rbp) 8) 64 →
    blockAt s.mem (off (AddressCalls.work s) 6144) = addressBlock p pass lane slice (wanted s)

theorem ready_zero (p : Params) (pass lane slice : Nat) (s : State)
    (layout : AddressCalls.Ready s)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (write : InRegions s.wr (off (s.gpr .rbp) 8) 8)
    (words : AddressHeader.Words p pass lane slice 0 s) : Ready p pass lane slice 0 s :=
  ⟨layout, reads, write, words, fun same => False.elim
    (counter_ne_zero _ (same.trans words.counterWord))⟩

structure Selected (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  block : blockAt t.mem (off (AddressCalls.work s) 6144) = addressBlock p pass lane slice (wanted s)
  layout : AddressCalls.Ready t
  work_eq : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s) s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  counterWord : t.mem.readW (off (t.gpr .rbp) 8) 64 = counter (s.gpr .r15)

theorem check_stable {s a : State} (h : AddressCalls.Ready s) (k : Divide.Keeps [.rax] s a) :
    AddressCalls.Stable s a := by
  apply AddressCalls.stable_of_frame h _ k.rd k.wr _ k.mxcsr
  · intro r hr
    apply k.regs
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [k.mem]; exact Frame.refl _ _

theorem selected_ok (p : Params) (pass lane slice old : Nat) (s : State)
    (h : Ready p pass lane slice old s) :
    WP isa select s (Selected s · p pass lane slice) := by
  unfold select
  refine WP.seq ((check_ok s (h.reads 8 (by simp))).mono ?_)
  rintro a ⟨value, flag, keeps⟩
  have stableA := check_stable h.layout keeps
  refine WP.ite (decide (counter (s.gpr .r15) = s.mem.readW (off (s.gpr .rbp) 8) 64))
    (by simp only [eval, flag]) ?_ ?_
  · intro same
    have equal := of_decide_eq_true same
    apply WP.of_runBlock
    simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
    refine ⟨?_, stableA.ready, stableA.work_eq, stableA.regs, keeps.rd, keeps.wr,
      ?_, keeps.mxcsr, ?_⟩
    · rw [keeps.mem]; exact h.cached equal
    · rw [keeps.mem]; exact Frame.refl _ _
    · rw [stableA.regs .rbp (by simp [calleeSaved]), keeps.mem]; exact equal.symm
  · intro _
    have write : InRegions a.wr (off (a.gpr .rbp) 8) 8 := by
      rw [keeps.wr, stableA.regs .rbp (by simp [calleeSaved])]; exact h.write
    refine WP.seq ((save_ready a stableA.ready write).mono ?_)
    intro b saved
    have words : AddressHeader.Words p pass lane slice (wanted s) b := by
      apply saved.words (stableA.words h.layout h.words)
      rw [value, counter_nat]; rfl
    have reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (b.rd ++ b.wr) (off (b.gpr .rbp) d) 8 := by
      rw [saved.rd, saved.wr, saved.regs]; exact stableA.reads h.reads
    refine (AddressCalls.code_ok p pass lane slice (wanted s) b saved.ready reads words).mono ?_
    rintro t ⟨generated, mx⟩
    have workB : AddressCalls.work b = AddressCalls.work s := saved.work_eq.trans stableA.work_eq
    have regsB (r : Reg) (hr : r ∈ calleeSaved) : b.gpr r = s.gpr r :=
      (congrFun saved.regs r).trans (stableA.regs r hr)
    have regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r :=
      fun r hr => (generated.regs r hr).trans (regsB r hr)
    have firstFrame : Frame (writes s) s.mem b.mem := by
      have frame := saved.frame
      rw [stableA.regs .rbp (by simp [calleeSaved]), keeps.mem] at frame
      exact frame.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp [writes])
    have finalFrame : Frame (writes s) b.mem t.mem := by
      have frame := generated.frame
      rw [AddressCalls.writes, workB, regsB .rsp (by simp [calleeSaved])] at frame
      exact frame.mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp [writes])
    refine ⟨?_, generated.ready, generated.work.trans workB, regs,
      generated.rd.trans (saved.rd.trans keeps.rd), generated.wr.trans (saved.wr.trans keeps.wr),
      firstFrame.trans finalFrame, mx.trans (saved.mxcsr.trans keeps.mxcsr), ?_⟩
    · have block := generated.block
      rw [workB] at block
      exact block
    · have preserved : t.mem.readW (off (b.gpr .rbp) 8) 64 = b.mem.readW (off (b.gpr .rbp) 8) 64 :=
        generated.frame.readW (r := ⟨b.gpr .rbp, 272⟩)
          (Offset.contains_base _ (by decide) (by decide)) (by
            intro r hr
            simp only [AddressCalls.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact saved.ready.frameWork
            · exact saved.ready.frameStack) (by decide)
      rw [generated.regs .rbp (by simp [calleeSaved]), preserved, saved.regs, saved.mem,
        Mem.readW_writeW_self64, value]

end VG.Proof.Argon2.X86_64.AddressCache
