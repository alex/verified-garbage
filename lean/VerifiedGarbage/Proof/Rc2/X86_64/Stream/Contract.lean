import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Verified
import VerifiedGarbage.Proof.Rc2.X86_64.Key
import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Copy

/-! # Streaming RC2-CBC on x86-64: the function-level contracts -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64

/-- `vg_rc2_cbc_init(key = rdi, key_len = rsi, effective_bits = rdx, iv = rcx,
iv_len = r8, ctx = r9, scratch = [rsp + 8])`, which calls key expansion. -/
def initContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let iv : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let ctx : Region := ⟨s.gpr .r9, 144⟩
    let buf : Region := ⟨stackArg s 0, 576⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    8 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧
      s.rd = [key, iv, args] ∧ s.wr = [ctx, buf] ∧
      key.Disjoint ctx ∧ key.Disjoint buf ∧ iv.Disjoint ctx ∧ iv.Disjoint buf ∧ ctx.Disjoint buf ∧
      ctx.Disjoint args ∧ buf.Disjoint args ∧
      ret.Disjoint key ∧ ret.Disjoint iv ∧ ret.Disjoint ctx ∧ ret.Disjoint buf ∧ ret.Disjoint args ∧
      stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint ctx ∧ stack.Disjoint buf ∧ stack.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 144 ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 576 ≤ 2 ^ 64
  post s s' :=
    ∀ direction, match Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Rc2.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) direction (s.gpr .rdx).toNat with
      | .ok c => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Rc2.contextAt s'.mem (s.gpr .r9) direction 0 = c
      | .error e => ((s'.gpr .rax).setWidth 32).toNat = e.code
  pub s₁ s₂ := PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] s₁ s₂ ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- The update functions (`ctx = rdi, pending_len = rsi, data = rdx,
len = rcx, out = r8, out_len = r9, scratch = [rsp + 8]`), which call CBC. -/
def updateContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .rdi, 144⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let out : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let buf : Region := ⟨stackArg s 0, 576⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧
      s.rd = [data, args] ∧ s.wr = [ctx, out, buf] ∧
      ctx.Disjoint data ∧ ctx.Disjoint out ∧ ctx.Disjoint buf ∧ ctx.Disjoint args ∧
      data.Disjoint out ∧ data.Disjoint buf ∧ out.Disjoint buf ∧ out.Disjoint args ∧ buf.Disjoint args ∧
      ret.Disjoint ctx ∧ ret.Disjoint data ∧ ret.Disjoint out ∧ ret.Disjoint buf ∧ ret.Disjoint args ∧
      stack.Disjoint ctx ∧ stack.Disjoint data ∧ stack.Disjoint out ∧ stack.Disjoint buf ∧ stack.Disjoint args ∧
      (s.gpr .rdi).toNat + 144 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 576 ≤ 2 ^ 64 ∧
      (s.gpr .rsi).toNat < 8 ∧ (s.gpr .r9).toNat = ((s.gpr .rsi).toNat + (s.gpr .rcx).toNat) / 8 * 8
  post s s' :=
    let result := Spec.Rc2.update (Spec.Rc2.contextAt s.mem (s.gpr .rdi) d (s.gpr .rsi).toNat)
      (Spec.Rc2.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    Spec.Rc2.contextAt s'.mem (s.gpr .rdi) d (((s.gpr .rsi).toNat + (s.gpr .rcx).toNat) % 8) = result.1 ∧
      Spec.Rc2.bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = result.2
  pub s₁ s₂ := PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] s₁ s₂ ∧ stackArg s₁ 0 = stackArg s₂ 0

def updateSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x40 else 0
  rd := [⟨0x2000, 0⟩, ⟨0x6008, 8⟩]
  wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩, ⟨0x4000, 576⟩]

def initSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rcx => 0x2000 | .r9 => 0x3000 | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x40 else 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x6008, 8⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩]

theorem publicRegs_seven (s₁ s₂ : State) : PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] s₁ s₂ ↔
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp := by
  simp [PublicRegs]

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem args_getD (s : State) : (s.gpr .rdi :: s.gpr .rsi :: s.gpr .rdx :: s.gpr .rcx :: s.gpr .r8 :: s.gpr .r9 ::
    List.map (stackArg s) (List.range 1)).getD 6 0 = stackArg s 0 := rfl

theorem update_implies (d : Spec.Rc2.Direction) : (updateContract d).Implies (Spec.Rc2.cbcUpdateContract abi d 16) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argRegs, updateContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] at h
    sig_pre [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argRegs, updateContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argRegs, updateContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
  post := by sig_implies_post [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argRegs, updateContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argRegs, updateContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    sig_split h
    rename_i h1 h2 h3 h4 h5 h6 h7
    exact ⟨(publicRegs_seven _ _).2 ⟨h2, h3, h4, h5, h6, h7, h1⟩, h⟩
  sat := by sig_implies_sat [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, abi, argRegs, updateContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] [updateSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using updateSatState

theorem init_implies : initContract.Implies (Spec.Rc2.cbcInitContract abi 8) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] at h
    sig_pre [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
  post := by sig_implies_post [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    sig_split h
    rename_i h1 h2 h3 h4 h5 h6 h7
    exact ⟨(publicRegs_seven _ _).2 ⟨h2, h3, h4, h5, h6, h7, h1⟩, h⟩
  sat := by sig_implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, abi, argRegs, initContract, publicRegs_seven, args_getD, stackArgs_one, List.append_eq] [initSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using initSatState

end VG.Proof.Rc2.X86_64.Stream
