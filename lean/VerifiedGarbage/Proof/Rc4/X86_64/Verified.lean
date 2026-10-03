import VerifiedGarbage.Proof.Rc4.X86_64.Lit
import VerifiedGarbage.Proof.Rc4.X86_64.Apply
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc4.Contract

/-! # RC4 on x86-64: verified against the shared contracts -/

namespace VG.Proof.Rc4.X86_64
open VG VG.X86_64 VG.Impl.Rc4.X86_64 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly gprPreserved_of)

/-! ## Initialization -/

/-- The contract the proof of `vg_rc4_init` is written against. -/
def initX : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let ctx : Region := ⟨s.gpr .rdx, 258⟩
    let scratch : Region := ⟨s.gpr .rcx, 64⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [ctx, scratch] ∧ key.Disjoint ctx ∧ ret.Disjoint ctx ∧
      ret.Disjoint scratch
  post s s' :=
    match Spec.Rc4.init (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) with
    | .ok c => (s'.gpr .rax).setWidth 32 = 0 ∧ contextAt s'.mem (s.gpr .rdx) = c
    | .error .invalidKeyLength => (s'.gpr .rax).setWidth 32 = 1
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

/-- The registers the code writes. -/
def written : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

theorem init_correct (s : State) (hs : initX.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initX.post s s' := by
  obtain ⟨hrd, hwr, hkc, hrc, hrs⟩ := hs
  have hp : InRegions s.wr (s.gpr .rdx) 258 :=
    ⟨⟨s.gpr .rdx, 258⟩, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  have hk : InRegions (s.rd ++ s.wr) (s.gpr .rdi) (s.gpr .rsi).toNat :=
    ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Region.contains_self _ _⟩
  have hsep : Mem.Sep (s.gpr .rdi) (s.gpr .rsi).toNat (s.gpr .rdx) 256 :=
    fun x hx hy => hkc x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)
  obtain ⟨tr, t, he, ⟨hpost, hf⟩, hkeep⟩ := WP.keep written (init_ok s hp hk hsep) (by lit_decide)
  have hframe : Frame s.wr s.mem t.mem := by
    intro x hx
    refine hf x fun hlt => hx ⟨s.gpr .rdx, 258⟩ (by rw [hwr]; exact List.mem_cons_self) ?_
    simp only [Region.Contains]
    omega
  refine ⟨tr, t, he, abiPreserved_of_exec (by lit_decide) he
    (gprPreserved_of hkeep (by decide) hframe ?_), ?_⟩
  · intro r hr
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hrc
    · exact hrs
  · unfold initX
    dsimp only
    revert hpost
    cases Spec.Rc4.init (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) with
    | ok c => intro hpost; exact ⟨by rw [hpost.1]; rfl, hpost.2⟩
    | error e => cases e; intro hpost; rw [hpost]; rfl

theorem init_ct : ConstantTime isa initX.pre initX.pub init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩, ⟨0x3000, 64⟩]

theorem init_verified : Verified target init (Spec.Rc4.initContract abi) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Spec.Rc4.initContract, Spec.Rc4.initSig, initX, abi, argRegs] [initSat]
      using initSat)

/-! ## The stream function -/

/-- The contract the proof of `vg_rc4_apply` is written against. -/
def applyX : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .rdi, 258⟩
    let data : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let scratch : Region := ⟨s.gpr .rcx, 64⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [ctx, data, scratch] ∧ ctx.Disjoint data ∧ ret.Disjoint ctx ∧
      ret.Disjoint data ∧ ret.Disjoint scratch
  post s s' :=
    let result := update (contextAt s.mem (s.gpr .rdi))
      (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
    contextAt s'.mem (s.gpr .rdi) = result.1 ∧
      bytesAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat = result.2
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧
    [(s₁.mem (s₁.gpr .rdi + 256)).toNat] = [(s₂.mem (s₂.gpr .rdi + 256)).toNat]

theorem apply_correct (s : State) (hs : applyX.pre s) :
    ∃ t s', Exec isa apply s t s' ∧ abiPreserved s s' ∧ applyX.post s s' := by
  obtain ⟨_, hwr, hcd, hrc, hrd, hrs⟩ := hs
  have hp : InRegions s.wr (s.gpr .rdi) 258 :=
    ⟨⟨s.gpr .rdi, 258⟩, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
  have hd : InRegions s.wr (s.gpr .rsi) (s.gpr .rdx).toNat :=
    ⟨⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩, by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self,
      Region.contains_self _ _⟩
  have hsep : Mem.Sep (s.gpr .rdi) 258 (s.gpr .rsi) (s.gpr .rdx).toNat :=
    fun x hx hy => hcd x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)
  obtain ⟨tr, t, he, ⟨hpost, hf⟩, hkeep⟩ := WP.keep written (apply_ok s hp hd hsep) (by lit_decide)
  have hframe : Frame s.wr s.mem t.mem := by
    intro x hx
    refine hf x (fun hlt => hx ⟨s.gpr .rdi, 258⟩ (by rw [hwr]; exact List.mem_cons_self) ?_)
      (fun hlt => hx ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
        (by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self) ?_)
    · simp only [Region.Contains]; omega
    · simp only [Region.Contains]; omega
  refine ⟨tr, t, he, abiPreserved_of_exec (by lit_decide) he
    (gprPreserved_of hkeep (by decide) hframe ?_), hpost⟩
  intro r hr
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hrc
  · exact hrd
  · exact hrs

structure EntryAgree (a b : State) : Prop where
  p : a.gpr .rdi = b.gpr .rdi
  data : a.gpr .rsi = b.gpr .rsi
  len : a.gpr .rdx = b.gpr .rdx
  i : (contextAt a.mem (a.gpr .rdi)).i = (contextAt b.mem (b.gpr .rdi)).i

def ReadValid (s : State) : Prop := InRegions (s.rd ++ s.wr) (s.gpr .rdi) 258

def startBlock : List Instr :=
  [.movzx8 .rcx (at_ .rdi 256), .movzx8 .r8 (at_ .rdi 257), .alu .test .rdx (.reg .rdx)]

/-- The PRGA index `i` is loaded from the context, where the taint analysis
takes it for secret: it may leak, so it is public. -/
theorem apply_start_ct : RelCT isa (fun a b => ReadValid a ∧ ReadValid b ∧ EntryAgree a b)
    (.block startBlock) fun a b =>
      VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) a b ∧ a.zf = b.zf := by
  intro a b tr tr' a' b' ⟨hpa, hpb, hab⟩ ea eb
  have hct : RelCT isa (fun a b => EntryAgree a b) (.block startBlock) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx]) (fun a b h => by
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.p
      · exact h.data
      · exact h.len) (by taint_decide)
  obtain ⟨htrace, -⟩ := hct a b tr tr' a' b' hab ea eb
  obtain ⟨_, u, eu, hau⟩ := apply_start a hpa
  obtain ⟨_, rfl⟩ := Exec.det eu ea
  obtain ⟨_, v, ev, hbv⟩ := apply_start b hpb
  obtain ⟨_, rfl⟩ := Exec.det ev eb
  obtain ⟨_, _, _, ha0, ha1, ha2, ha12, _, haz⟩ := hau
  obtain ⟨_, _, _, hb0, hb1, hb2, hb12, _, hbz⟩ := hbv
  refine ⟨htrace, Taint.agree_ofRegs fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ha0.trans (hab.p.trans hb0.symm)
    · exact ha1.trans (hab.data.trans hb1.symm)
    · exact ha2.trans (hab.len.trans hb2.symm)
    · rw [ha12, hb12, hab.i]
  · rw [haz, hbz, hab.len]

theorem apply_ct : ConstantTime isa ReadValid EntryAgree apply := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold apply
  refine RelCT.seq apply_start_ct (RelCT.ite ?_ ?_ ?_)
  · intro a b ⟨_, hz⟩
    simp only [eval, hz]
  · exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
      (by taint_decide)
  · exact RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) (fun _ _ h => h.1.1)
      (by taint_decide)

theorem apply_ct' : ConstantTime isa applyX.pre applyX.pub apply := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  have hv (s : State) (h : applyX.pre s) : ReadValid s :=
    ⟨⟨s.gpr .rdi, 258⟩, List.mem_append_right _ (by rw [h.2.1]; exact List.mem_cons_self),
      Region.contains_self _ _⟩
  exact apply_ct s₁ s₂ tr₁ tr₂ t₁ t₂ (hv s₁ h₁) (hv s₂ h₂)
    ⟨hp.1, hp.2.1, hp.2.2.1, BitVec.eq_of_toNat_eq (List.cons.inj hp.2.2.2).1⟩ e₁ e₂

def applySat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 1 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 258⟩, ⟨0x2000, 1⟩, ⟨0x3000, 64⟩]

theorem apply_verified : Verified target apply (Spec.Rc4.applyContract abi) :=
  Verified.of_correct apply_correct apply_ct' (by
    sig_implies [Spec.Rc4.applyContract, Spec.Rc4.applySig, applyX, abi, argRegs] [applySat]
      using applySat)

end VG.Proof.Rc4.X86_64
