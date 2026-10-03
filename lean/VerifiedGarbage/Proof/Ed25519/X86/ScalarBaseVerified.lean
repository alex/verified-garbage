import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTSetup
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline

/-! Merged from `Proof.Ed25519.X86.ScalarBaseCT`. -/
section
/-! Merged from `Proof.Ed25519.X86.ScalarBaseCTFinish`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def BaseSaved (s₀ t₀ s t : State) : Prop := Saved s₀ (arg s₀ 2) s ∧ Saved t₀ (arg t₀ 2) t

theorem scalarBaseFinish_ct (s₀ t₀ : State) (hs : scalarBaseLocal.pre s₀) (ht : scalarBaseLocal.pre t₀)
    (hp : scalarBaseLocal.pub s₀ t₀) : RelCT isa (BaseSaved s₀ t₀) (.block (finishWords 96)) (fun _ _ => True) := by
  obtain ⟨ps, _, _⟩ := scalarBase_pre hs
  obtain ⟨pt, _, _⟩ := scalarBase_pre ht
  have loadct : RelCT isa (BaseSaved s₀ t₀)
      (.block [.mov .esi (.mem (Impl.X25519.X86.at_ .esp 4))]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.esp]) _ (by taint_decide)
    intro s t h
    exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
      (h.1.esp.trans (hp.1.trans h.2.esp.symm)))
  have hh := ctWithRuns loadct (fun _ _ h => ⟨loadArg_ok (i := 0) ps h.1 (by decide),
    loadArg_ok (i := 0) pt h.2 (by decide)⟩)
  have tailct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi)
      (.block (outputWords 96 8 ++ Impl.X25519.X86.restore)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by taint_decide)
    intro s t h
    apply regsTaint_agree
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.1, h.2]
  simp only [finishWords, List.append_assoc]
  refine ctBlockAppend (hh.mono (fun _ _ h => h) ?_) tailct
  intro s t ⟨_, a, b, _, ha, hb⟩
  exact ⟨ha.1.edi.trans (hp.2.2.2.trans hb.1.edi.symm), ha.2.1.trans (hp.2.1.trans hb.2.1.symm)⟩

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem baseWr_agree {s t : State} (hs : scalarBaseLocal.pre s) (ht : scalarBaseLocal.pre t)
    (hp : scalarBaseLocal.pub s t) : s.wr = t.wr := by
  rw [hs.2.1, ht.2.1, hp.2.1, hp.2.2.2]

def BaseCTReady (s₀ s : State) : Prop :=
  Saved s₀ (arg s₀ 2) s ∧ MulCTInput (arg s₀ 2) (baseScalar s₀) 16 s

theorem scalarBaseTail_ct (s₀ t₀ : State) (hs : scalarBaseLocal.pre s₀) (ht : scalarBaseLocal.pre t₀)
    (hp : scalarBaseLocal.pub s₀ t₀) :
    RelCT isa (fun s t => BaseCTReady s₀ s ∧ BaseCTReady t₀ t)
      (.seq (pointMultiply 16) (.seq pointEncode (.block (finishWords 96)))) (fun _ _ => True) := by
  have hwr := baseWr_agree hs ht hp
  have mulct := (pointMultiply_ct (arg s₀ 2) (baseScalar s₀) (baseScalar t₀) 16 (Or.inl rfl)).mono
    (P' := fun (s t : State) => BaseCTReady s₀ s ∧ BaseCTReady t₀ t)
    (fun _ _ h => ⟨h.1.2, hp.2.2.2.symm ▸ h.2.2,
      h.1.1.wr.trans (hwr.trans h.2.1.wr.symm)⟩) (fun _ _ h => h)
  have mw (u s : State) (h : BaseCTReady u s) : WP isa (pointMultiply 16) s (Saved u (arg u 2)) := by
    refine WP.mono (pointMultiply_ok h.2.ctx.ctx (baseScalar u) 16 (by decide) (by decide)
      h.2.bound h.2.bits h.2.d) fun t ⟨kt, _, _⟩ => ?_
    exact h.1.mulkeep h.2.ctx.ctx.fit kt
  have mul := ctWithRuns mulct (fun s t h => ⟨mw s₀ s h.1, mw t₀ t h.2⟩)
  have encct := pointEncode_ct.mono (P' := BaseSaved s₀ t₀)
    (fun _ _ h => h.1.edi.trans (hp.2.2.2.trans h.2.edi.symm)) (fun _ _ h => h)
  have ew (u s : State) (hu : scalarBaseLocal.pre u) (h : Saved u (arg u 2) s) :
      WP isa pointEncode s (Saved u (arg u 2)) := by
    have pu := (scalarBase_pre hu).1
    refine WP.mono (pointEncode_ok (h.ctx pu.fit pu.wr)) fun t ⟨kt, _⟩ => ?_
    exact h.ikeep pu.fit kt
  have enc := ctWithRuns encct (fun s t h => ⟨ew s₀ s hs h.1, ew t₀ t ht h.2⟩)
  refine VG.RelCT.seq (mul.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
    (VG.RelCT.seq (enc.mono (fun _ _ h => h) (fun _ _ ⟨_, _, _, _, ha, hb⟩ => ⟨ha, hb⟩))
      (scalarBaseFinish_ct s₀ t₀ hs ht hp))

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  have start := ctWithRuns scalarBaseStart_ct
    (fun _ _ h => ⟨scalarBaseStart_ok h.1, scalarBaseStart_ok h.2.1⟩)
  rw [scalarBase]
  refine VG.RelCT.seq start ?_
  intro s t ts tt s' t' ⟨_, u, v, hp, hu, hv⟩ es et
  exact scalarBaseTail_ct u v hp.1 hp.2.1 hp.2.2 _ _ _ _ _ _ ⟨hu, hv⟩ es et

end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def baseSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

def baseSatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := baseSatMem
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩]

theorem scalarBase_ok (s : State) (h : scalarBaseLocal.pre s) :
    ∃ tr t, Exec isa scalarBase s tr t ∧ abiPreserved s t ∧ scalarBaseLocal.post s t :=
  scalarBase_correct h

def scalarBaseWide : Contract isa :=
  { scalarBaseLocal with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let input : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [input] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧
      input.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 }

def scalarBaseRd (s : State) : List Region := [⟨(arg s 1).setWidth 64, 32⟩, ⟨argAddr s 0, 12⟩]
def scalarBaseWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 32⟩, ⟨(arg s 2).setWidth 64, 8192⟩]

theorem scalarBaseWide_pre (s : State) (h : scalarBaseWide.pre s) :
    scalarBaseLocal.pre (s.withRegions (scalarBaseRd s) (scalarBaseWr s)) := by
  simp only [scalarBaseLocal, scalarBaseRd, scalarBaseWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem scalarBaseWide_implies : scalarBaseWide.Implies (Spec.Ed25519.scalarBaseContract X86.abi) := by
    have a0 : arg baseSatState 0 = 0x1000 := by decide
    have a1 : arg baseSatState 1 = 0x2000 := by decide
    have a2 : arg baseSatState 2 = 0x4000 := by decide
    have e : argAddr baseSatState 0 = 0x8004 := by decide
    have esp : baseSatState.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig,
      Spec.Ed25519.scratchWords, scalarBaseWide, scalarBaseLocal, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, e, esp] using baseSatState

theorem scalarBase_verified : Verified X86.target scalarBase (Spec.Ed25519.scalarBaseContract X86.abi) := by
  have hsat := scalarBaseWide_implies.sat_left
  have satLocal : ∃ s, scalarBaseLocal.pre s := hsat.elim fun s h => ⟨_, scalarBaseWide_pre s h⟩
  have verifiedLocal : Verified X86.target scalarBase scalarBaseLocal :=
    Verified.of_correct scalarBase_ok scalarBase_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal scalarBaseRd scalarBaseWr scalarBaseWide_pre
    ?_ ?_ ?_ ?_ hsat) scalarBaseWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [scalarBaseRd, scalarBaseWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [scalarBaseWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [scalarBaseWide, scalarBaseLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [scalarBaseWide, scalarBaseLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed25519.X86
