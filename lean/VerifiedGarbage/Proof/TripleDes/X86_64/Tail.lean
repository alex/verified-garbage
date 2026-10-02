import VerifiedGarbage.Proof.TripleDes.X86_64.Store
import VerifiedGarbage.Proof.TripleDes.X86_64.Save
import VerifiedGarbage.Proof.TripleDes.X86_64.WordState

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

structure TailPost (original origin : State) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (origin.gpr .rsi) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ savedRegs ++ [Reg.rdi], s.gpr r = original.gpr r
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : Frame [⟨origin.gpr .rsi, 8⟩] origin.mem s.mem

theorem blockTail_ok (original s : State) (x : BitVec 64)
    (hword : WordState x s) (hsaved : Saved original s)
    (hsavedRead : ∀ i < 7, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8)
    (hwrite : InRegions s.wr (s.gpr .rsi) 8) :
    WP isa (.block (blockStore ++ blockRestore ++ ([.store (memOp .rsi 0) .rax] : List Instr)))
      s (TailPost original s x) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, regs₁⟩ :=
    blockStore_ok s ((x >>> 32).setWidth 32) (x.setWidth 32) hword.left hword.right
  have word : s₁.gpr .rax = bswap64 (Spec.TripleDes.permute Spec.TripleDes.fp x) :=
    word₁.trans (congrArg (fun v => bswap64 (Spec.TripleDes.permute Spec.TripleDes.fp v))
      (VG.Proof.TripleDes.halves_append x))
  have saved₁ : Saved original s₁ := by
    intro i hi
    rw [regs₁ .rdx (by decide), mem₁]
    exact hsaved i hi
  have savedRead₁ : ∀ i < 7, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [rd₁, wr₁, regs₁ .rdx (by decide)]
    exact hsavedRead
  apply WP.block_append
  apply WP.block_append
  apply WP.of_runBlock
  refine ⟨s₁, run₁, ?_⟩
  apply WP.mono (blockRestore_ok original s₁ saved₁ savedRead₁)
  intro s₂ hs₂
  have hnonsaved : ∀ q ∈ [Reg.rax, .rsi, .rdx, .rsp], q ∉ savedRegs ++ [Reg.rdi] := by decide
  have hrax₂ : s₂.gpr .rax = bswap64 (Spec.TripleDes.permute Spec.TripleDes.fp x) :=
    (hs₂.2.reg .rax (hnonsaved .rax (by decide))).trans word
  have hregs₂ : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s₂.gpr q = s.gpr q := by
    intro q hq
    have hkeep : ∀ r ∈ [Reg.rsi, .rdx, .rsp], r ∈ [Reg.rax, .rsi, .rdx, .rsp] ∧
      r ∈ [Reg.rdi, .rsi, .rdx, .rsp] := by decide
    exact (hs₂.2.reg q (hnonsaved q (hkeep q hq).1)).trans (regs₁ q (hkeep q hq).2)
  have hwrite₂ : InRegions s₂.wr (s₂.gpr .rsi) 8 := by
    rw [hs₂.2.wr, wr₁, hregs₂ .rsi (by decide)]
    exact hwrite
  obtain ⟨s₃, run₃, mem₃, gpr₃, rd₃, wr₃⟩ := writeData_ok s₂ hwrite₂
  apply WP.of_runBlock
  refine ⟨s₃, run₃, ?_, ?_, rd₃.trans (hs₂.2.rd.trans rd₁),
    wr₃.trans (hs₂.2.wr.trans wr₁), ?_, ?_⟩
  · rw [mem₃, hs₂.2.mem, mem₁, hregs₂ .rsi (by decide), hrax₂]
    exact blockAt_writeW s.mem (s.gpr .rsi) (Spec.TripleDes.permute Spec.TripleDes.fp x)
  · intro r hr
    rw [gpr₃]
    exact hs₂.1 r hr
  · intro q hq
    rw [gpr₃]
    exact hregs₂ q hq
  · rw [mem₃, hs₂.2.mem, mem₁, hregs₂ .rsi (by decide)]
    exact countWrite_frame s.mem (s.gpr .rsi) (s₂.gpr .rax)

end VG.Proof.TripleDes.X86_64
