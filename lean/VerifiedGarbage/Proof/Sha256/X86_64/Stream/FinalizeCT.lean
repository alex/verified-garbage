import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Finalize

/-!
# Streaming SHA-256 on x86-64: `finalize` is constant time

Untrusted: everything here is checked by Lean.

This holds for any compression function `f` (`Callee.Ok`), so it is proven
once for every implementation, by relating two runs (`RelCT`) as for `update`
(`UpdateCT.lean`): the number of blocks to pad and the bytes buffered depend
only on `count`, so at every iteration correctness determines our registers
from the public arguments alone; between the calls the taint analysis proves
each piece constant time from that, and the calls are constant time by
`compressAt_rel`.
-/

namespace VG.Proof.Sha256.X86_64.Stream.Finalize

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Stream

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

theorem PubEq.kOf {s₀ s₀' : State} (hq : PubEq s₀ s₀') : kOf s₀ = kOf s₀' := by
  have e : cnt s₀ = cnt s₀' := congrArg BitVec.toNat hq.rsi
  simp only [Finalize.kOf, e]

theorem PubEq.cnt {s₀ s₀' : State} (hq : PubEq s₀ s₀') : cnt s₀ = cnt s₀' :=
  congrArg BitVec.toNat hq.rsi

/-- The registers the pieces between the calls use. -/
abbrev regs : List Reg := [.rbx, .r15, .rbp, .r12, .rsp, .r13, .r14]

theorem LInv.agree {s₀ s₀' : State} (hq : PubEq s₀ s₀') {k n : Nat} {s s' : State} (h : LInv s₀ k n s)
    (h' : LInv s₀' k n s') : ∀ r ∈ regs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [regs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx]; exact hq.rdi
  · rw [h.r15, h'.r15]; exact hq.rcx
  · rw [h.rbp, h'.rbp]; exact hq.rdx
  · rw [h.r12, h'.r12]; exact hq.rsi
  · rw [h.rsp, h'.rsp]; exact hq.rsp
  · rw [h.r13, h'.r13]
  · rw [h.r14, h'.r14]

section
variable {f : Callee} (hf : f.Ok) {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀')
  (hq : PubEq s₀ s₀')
include hf hp hp' hq

theorem body_rel {k n : Nat} :
    RelCT isa (fun s₁ s₂ => LInv s₀ k n s₁ ∧ LInv s₀' k n s₂) (finalizeBody f)
      fun s₁ s₂ => Step s₀ k s₁ ∧ Step s₀' k s₂ := by
  have pad : RelCT isa (fun s₁ s₂ => LInv s₀ k n s₁ ∧ LInv s₀' k n s₂) finalizePad
      fun s₁ s₂ => Mid f s₀ k s₁ ∧ Mid f s₀' k s₂ :=
    ((RelCT.taint (A := taint) (Taint.ofRegs regs) (P := fun s₁ s₂ => LInv s₀ k n s₁ ∧ LInv s₀' k n s₂)
      (fun _ _ h => Taint.agree_ofRegs (LInv.agree hq h.1 h.2)) (c := finalizePad) (by taint_decide)).wp
      fun _ _ h => ⟨pad_ok hf hp h.1, pad_ok hf hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cmp : RelCT isa (fun s₁ s₂ => Mid f s₀ k s₁ ∧ Mid f s₀' k s₂) (compressAt f)
      fun s₁ s₂ => WP isa (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]) s₁ (Step s₀ k) ∧
        WP isa (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]) s₂ (Step s₀' k) :=
    ((compressAt_rel hf fun s₁ s₂ ⟨⟨C₁, si₁, _⟩, ⟨C₂, si₂, _⟩⟩ =>
      ⟨⟨_, _, _, C₁.callOk hp si₁⟩, ⟨_, _, _, C₂.callOk hp' si₂⟩,
        by rw [C₁.rbx, C₂.rbx]; exact hq.rdi, by rw [C₁.r15, C₂.r15]; exact hq.rcx,
        by rw [si₁, si₂]; exact congrArg (· + 32) hq.rdi, by rw [C₁.rsp, C₂.rsp]; exact hq.rsp⟩).wp
      fun _ _ h => ⟨WP.seq_iff.mp h.1.2.2, WP.seq_iff.mp h.2.2.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have fin : RelCT isa (fun s₁ s₂ =>
        WP isa (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]) s₁ (Step s₀ k) ∧
        WP isa (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]) s₂ (Step s₀' k))
      (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)])
      fun s₁ s₂ => Step s₀ k s₁ ∧ Step s₀' k s₂ :=
    ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
      (c := .block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]) (by taint_decide)).wp
      fun _ _ h => h).mono (fun _ _ h => h) fun _ _ h => h.2
  exact pad.seq (cmp.seq fin)

theorem finalize_rel :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (finalize f) fun _ _ => True := by
  have pro : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') finalizeStart fun s₁ s₂ =>
      ∃ n, LInv s₀ (kOf s₀) n s₁ ∧ LInv s₀' (kOf s₀) n s₂ :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp])
      (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.rsp) (c := finalizeStart) (by taint_decide)).wp
      fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono
      (fun _ _ h => h) fun _ _ h => ⟨_, h.2.1, by rw [hq.kOf, hq.cnt]; exact h.2.2⟩
  have lp := RelCT.loop (M := isa) (body := finalizeBody f) (c := .e)
    (Q := fun s₁ s₂ => Done s₀ s₁ ∧ Done s₀' s₂)
    (fun m s₁ s₂ => ∃ n, LInv s₀ m n s₁ ∧ LInv s₀' m n s₂) (fun m => RelCT.exists_ fun n =>
      (body_rel hf hp hp' hq).mono (fun _ _ h => h) fun s₁ s₂ ⟨h₁, h₂⟩ => by
        rcases h₁ with ⟨rfl, z₁, D₁, -⟩ | ⟨rfl, z₁, L₁⟩ <;>
          rcases h₂ with ⟨h0, z₂, D₂, -⟩ | ⟨h1, z₂, L₂⟩
        · exact ⟨z₁.trans z₂.symm, fun _ => ⟨D₁, D₂⟩, fun h => absurd (z₁.symm.trans h) (by simp)⟩
        · cases h1
        · cases h0
        · exact ⟨z₁.trans z₂.symm, fun h => absurd (z₁.symm.trans h) (by simp),
            fun _ => ⟨0, by omega, 0, L₁, L₂⟩⟩) (kOf s₀)
  have epi : RelCT isa (fun s₁ s₂ => Done s₀ s₁ ∧ Done s₀' s₂)
      (.block ((List.range 8).flatMap (fun k =>
        [.mov32 .rax (.mem (Impl.Sha256.X86_64.at_ .rbx (4 * k))), .bswap32 .rax,
          .store32 (Impl.Sha256.X86_64.at_ .rbp (4 * k)) .rax]) ++ restore)) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.rbx, .rbp, .r15]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.1.rbx, h.2.1.rbx]; exact hq.rdi
      · rw [h.1.1.rbp, h.2.1.rbp]; exact hq.rdx
      · rw [h.1.1.r15, h.2.1.r15]; exact hq.rcx) (by taint_decide)
  exact pro.seq (lp.seq epi)

end

theorem pubEq_of {s₁ s₂ : State} (h : Proof.Sha256.finalizeX86_64.pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem constantTime {f : Callee} (hf : f.Ok) :
    ConstantTime isa Proof.Sha256.finalizeX86_64.pre Proof.Sha256.finalizeX86_64.pub (finalize f) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (finalize_rel hf (pre_of h₁) (pre_of h₂) (pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Sha256.X86_64.Stream.Finalize
