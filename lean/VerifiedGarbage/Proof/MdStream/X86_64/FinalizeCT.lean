import VerifiedGarbage.Proof.MdStream.X86_64.Finalize

/-!
# Streaming Merkle–Damgård hash functions on x86-64: `finalize` is constant time

Untrusted: everything here is checked by Lean.

This holds for any compression function (`CalleeOk`), so it is proven once
for every implementation, by relating two runs (`RelCT`) as for `update`
(`UpdateCT.lean`): the number of blocks to pad and the bytes buffered depend
only on `count`, so at every iteration correctness determines our registers
from the public arguments alone; between the calls the taint analysis proves
each piece constant time from that (`Taints`), and the calls are constant
time by `compressAt_rel`.
-/

namespace VG.Proof.MdStream.X86_64.Finalize

open VG VG.X86_64 VG.Impl.MdStream.X86_64

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

theorem PubEq.kOf {P : Params} {s₀ s₀' : State} (hq : PubEq s₀ s₀') : kOf P s₀ = kOf P s₀' := by
  have e : cnt s₀ = cnt s₀' := congrArg BitVec.toNat hq.rsi
  simp only [Finalize.kOf, e]

theorem PubEq.cnt {s₀ s₀' : State} (hq : PubEq s₀ s₀') : cnt s₀ = cnt s₀' :=
  congrArg BitVec.toNat hq.rsi

/-- The registers the pieces between the calls use. -/
abbrev regs : List Reg := [.rbx, .r15, .rbp, .r12, .rsp, .r13, .r14]

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem LInv.agree {s₀ s₀' : State} (hq : PubEq s₀ s₀') {k n : Nat} {s s' : State} (h : LInv H s₀ k n s)
    (h' : LInv H s₀' k n s') : ∀ r ∈ regs, s.gpr r = s'.gpr r := by
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

variable (hd : Dims P) (hs : Shape H) (ht : Taints P) {name : String} {code : Prog isa}
  (hf : CalleeOk H code) {s₀ s₀' : State} (hp : Pre P s₀) (hp' : Pre P s₀') (hq : PubEq s₀ s₀')
include hd hs ht hf hp hp' hq

theorem body_rel {k n : Nat} :
    RelCT isa (fun s₁ s₂ => LInv H s₀ k n s₁ ∧ LInv H s₀' k n s₂) (finalizeBody P name code)
      fun s₁ s₂ => Step H s₀ k s₁ ∧ Step H s₀' k s₂ := by
  obtain ⟨_, hpad⟩ := ht.finPad
  have pad : RelCT isa (fun s₁ s₂ => LInv H s₀ k n s₁ ∧ LInv H s₀' k n s₂) (finalizePad P)
      fun s₁ s₂ => Mid H name code s₀ k s₁ ∧ Mid H name code s₀' k s₂ :=
    ((RelCT.taint (A := taint) (Taint.ofRegs regs) (P := fun s₁ s₂ => LInv H s₀ k n s₁ ∧ LInv H s₀' k n s₂)
      (fun _ _ h => Taint.agree_ofRegs (LInv.agree hq h.1 h.2)) (c := finalizePad P) hpad).wp
      fun _ _ h => ⟨pad_ok hd hs hf hp h.1, pad_ok hd hs hf hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cmp : RelCT isa (fun s₁ s₂ => Mid H name code s₀ k s₁ ∧ Mid H name code s₀' k s₂) (compressAt name code)
      fun s₁ s₂ => WP isa (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]) s₁ (Step H s₀ k) ∧
        WP isa (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]) s₂ (Step H s₀' k) :=
    ((compressAt_rel H hf fun s₁ s₂ ⟨⟨C₁, si₁, _⟩, ⟨C₂, si₂, _⟩⟩ =>
      ⟨⟨_, _, _, C₁.callOk hd hp si₁⟩, ⟨_, _, _, C₂.callOk hd hp' si₂⟩,
        by rw [C₁.rbx, C₂.rbx]; exact hq.rdi, by rw [C₁.r15, C₂.r15]; exact hq.rcx,
        by rw [si₁, si₂]; exact congrArg (· + _) hq.rdi, by rw [C₁.rsp, C₂.rsp]; exact hq.rsp⟩).wp
      fun _ _ h => ⟨WP.seq_iff.mp h.1.2.2, WP.seq_iff.mp h.2.2.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have fin : RelCT isa (fun s₁ s₂ =>
        WP isa (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]) s₁ (Step H s₀ k) ∧
        WP isa (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]) s₂ (Step H s₀' k))
      (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)])
      fun s₁ s₂ => Step H s₀ k s₁ ∧ Step H s₀' k s₂ :=
    ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
      (c := .block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]) (by taint_decide)).wp
      fun _ _ h => h).mono (fun _ _ h => h) fun _ _ h => h.2
  exact pad.seq (cmp.seq fin)

theorem finalize_rel :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (finalize P name code) fun _ _ => True := by
  obtain ⟨_, hst⟩ := ht.finStart
  obtain ⟨_, hend⟩ := ht.finEnd
  have pro : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (finalizeStart P) fun s₁ s₂ =>
      ∃ n, LInv H s₀ (kOf P s₀) n s₁ ∧ LInv H s₀' (kOf P s₀) n s₂ :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp])
      (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.rsp) (c := finalizeStart P) hst).wp
      fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact ⟨prologue_ok (H := H) hd hp, prologue_ok (H := H) hd hp'⟩).mono
      (fun _ _ h => h) fun _ _ h => ⟨_, h.2.1, by rw [hq.kOf, hq.cnt]; exact h.2.2⟩
  have lp := RelCT.loop (M := isa) (body := finalizeBody P name code) (c := .e)
    (Q := fun s₁ s₂ => Done H s₀ s₁ ∧ Done H s₀' s₂)
    (fun m s₁ s₂ => ∃ n, LInv H s₀ m n s₁ ∧ LInv H s₀' m n s₂) (fun m => RelCT.exists_ fun n =>
      (body_rel hd hs ht hf hp hp' hq).mono (fun _ _ h => h) fun s₁ s₂ ⟨h₁, h₂⟩ => by
        rcases h₁ with ⟨rfl, z₁, D₁, -⟩ | ⟨rfl, z₁, L₁⟩ <;>
          rcases h₂ with ⟨h0, z₂, D₂, -⟩ | ⟨h1, z₂, L₂⟩
        · exact ⟨z₁.trans z₂.symm, fun _ => ⟨D₁, D₂⟩, fun h => absurd (z₁.symm.trans h) (by simp)⟩
        · cases h1
        · cases h0
        · exact ⟨z₁.trans z₂.symm, fun h => absurd (z₁.symm.trans h) (by simp),
            fun _ => ⟨0, by omega, 0, L₁, L₂⟩⟩) (kOf P s₀)
  have epi : RelCT isa (fun s₁ s₂ => Done H s₀ s₁ ∧ Done H s₀' s₂) (.block (P.out ++ restore P))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.rbx, .rbp, .r15]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.1.rbx, h.2.1.rbx]; exact hq.rdi
      · rw [h.1.1.rbp, h.2.1.rbp]; exact hq.rdx
      · rw [h.1.1.r15, h.2.1.r15]; exact hq.rcx) hend
  exact pro.seq (lp.seq epi)

end

theorem pubEq_of {P : Params} {H : Md P.B P.N P.L} {s₁ s₂ : State} (h : (finK H).pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem constantTime {P : Params} {H : Md P.B P.N P.L} (hd : Dims P) (hs : Shape H) (ht : Taints P)
    {name : String} {code : Prog isa} (hf : CalleeOk H code) :
    ConstantTime isa (finK H).pre (finK H).pub (finalize P name code) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (finalize_rel hd hs ht hf (pre_of h₁) (pre_of h₂) (pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- `finalize` is verified if it never loads MXCSR. -/
theorem verified {P : Params} {H : Md P.B P.N P.L} (hd : Dims P) (hs : Shape H) (ht : Taints P)
    {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hm : (finalize P name code).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (finalize P name code) (finK H) :=
  verified_of hd hs hf hm (constantTime hd hs ht hf)

end VG.Proof.MdStream.X86_64.Finalize
