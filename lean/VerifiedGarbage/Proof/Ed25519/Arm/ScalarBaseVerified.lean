import VerifiedGarbage.Impl.Ed25519.Arm.ScalarBase
import VerifiedGarbage.Proof.Ed25519.Arm.PointFromScalar
import VerifiedGarbage.Proof.Ed25519.Arm.PointEncode
import VerifiedGarbage.Proof.Ed25519.Arm.InitFields
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTFrom
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarABI
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarFinish
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarCodec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseEngine`. -/
section
/-! All input scalar bits, exact point multiplication, and canonical encoding compose. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def encodedValue (p : Spec.Ed25519.Point) : Nat :=
  (p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val +
    ((p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val % 2) * 2 ^ 255

theorem encodedValue_spec (p : Spec.Ed25519.Point) :
    Spec.Ed25519.encodePoint p = Spec.Ed25519.encodeLE 32 (encodedValue p) := rfl

theorem scalarBaseEngine_ok {s : State} {base ptr : BitVec 32} (hc : Ctx base s)
    (hp : s.gpr .r12 = ptr) (hfit : ptr.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa scalarBaseEngine s fun t => PointKeep base s t ∧ Lim t.mem (State.addr base) FR ∧
      V t.mem (State.addr base) FR = encodedValue
        (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32)) Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono (initFields_ok hc) fun a ⟨ak, al, _⟩ => ?_)
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.basePoint) (ak.ctx hc) al)
    fun u ⟨uk, ul, ue⟩ => ?_)
  have ku := ak.trans uk
  have up : u.gpr .r12 = ptr := (ku.rest.gpr _ (by decide)).trans hp
  have ur : ∀ i < 32, InRegions (u.rd ++ u.wr) (State.addr ptr + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [ku.rest.rd, ku.rest.wr]
    exact hr i hi
  have uv : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (State.addr ptr) 32) =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) := by
    rw [← packedDigits_decode _ _ 16, ← packedDigits_decode _ _ 16]
    exact packedDigits_frame ku.frame (by decide) fun r hm => by
      rw [List.mem_singleton.mp hm]
      exact hsep.sub_right (Offset.sub_base _ (by decide))
  have upp : point (env u.mem base) 0 1 2 3 = Spec.Ed25519.basePoint :=
    (congrArg (fun e => point e 0 1 2 3) ue).trans (constPoint_eval _ _)
  refine WP.seq (WP.mono (pointFromScalar_ok (ku.ctx hc) ul up 16 (by decide) (by decide) hfit ur hsep)
    fun v ⟨vk, vl, _, vp⟩ => ?_)
  have ksv := (PointKeep.of_keep ku).trans vk
  refine WP.mono (pointEncode_ok (ksv.ctx hc) vl) fun t ⟨tk, tl, tv⟩ => ?_
  refine ⟨ksv.trans (PointKeep.of_ikeep tk), tl, ?_⟩
  change V t.mem (State.addr base) FR = encodedValue (point (env v.mem base) 0 1 2 3) at tv
  exact tv.trans (congrArg encodedValue
    (vp.trans (congrArg₂ Spec.Ed25519.pointMul uv upp)))

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseCTEngine`. -/
section
/-! Initialization, secret scalar multiplication, and encoding have public traces. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def BaseCTPre (b p : BitVec 32) (s : State) : Prop :=
  Ctx b s ∧ s.gpr .r12 = p ∧ p.toNat + 32 ≤ 2 ^ 32 ∧
    (∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1) ∧
    (⟨State.addr p, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩

def basePrepareCT : Prog isa := .seq (.block initFields) (constPoint Spec.Ed25519.basePoint)

materialize_code basePrepareCT

theorem basePrepareCT_ok {s : State} {base ptr : BitVec 32} (h : BaseCTPre base ptr s) :
    WP isa basePrepareCT s (FromCTPre base ptr 16) := by
  obtain ⟨hc, hp, hfit, hr, hsep⟩ := h
  refine WP.seq (WP.mono (initFields_ok hc) fun a ⟨ak, al, _⟩ => ?_)
  refine WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.basePoint) (ak.ctx hc) al)
    fun u ⟨uk, ul, _⟩ => ?_
  have ku := ak.trans uk
  refine ⟨ku.ctx hc, ul, (ku.rest.gpr _ (by decide)).trans hp, hfit, ?_, hsep⟩
  intro i hi
  rw [ku.rest.rd, ku.rest.wr]
  exact hr i hi

theorem scalarBaseEngine_ct (base ptr : BitVec 32) :
    CT (fun x y => BaseCTPre base ptr x ∧ BaseCTPre base ptr y)
      scalarBaseEngine (fun _ _ => True) := by
  have hp : CT (fun x y => BaseCTPre base ptr x ∧ BaseCTPre base ptr y)
      basePrepareCT (fun x y => FromCTPre base ptr 16 x ∧ FromCTPre base ptr 16 y) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    · exact fun _ h => basePrepareCT_ok h
  have hm := (pointFromScalar_ct base ptr 16 (.inl rfl)).wpDep (fun x y h =>
    ⟨pointFromScalar_ok h.1.1 h.1.2.1 h.1.2.2.1 16 (by decide) (by decide)
      h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2,
     pointFromScalar_ok h.2.1 h.2.2.1 h.2.2.2.1 16 (by decide) (by decide)
      h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2⟩)
  have hm' := hm.mono (fun _ _ h => h) (fun x y ⟨_, a, b, h, hx, hy⟩ =>
    And.intro (hx.1.ctx h.1.1).r0 (hy.1.ctx h.2.1).r0)
  have he : CT (fun (x y : State) => x.gpr .r0 = base ∧ y.gpr .r0 = base)
      pointEncode (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.trans h.2.symm
  intro x y tx ty u v h ex ey
  cases ex with
  | seq ei ex =>
    cases ex with
    | seq ep em =>
      cases ey with
      | seq fi ey =>
        cases ey with
        | seq fp fm =>
          obtain ⟨ht, hh⟩ := hp _ _ _ _ _ _ h (Exec.seq ei ep) (Exec.seq fi fp)
          have hm := (RelCT.seq hm' he _ _ _ _ _ _ hh em fm).1
          exact ⟨by simpa only [List.append_assoc] using
            congrArg₂ (fun (a b : List Leak) => a ++ b) ht hm, trivial⟩

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseSetup`. -/
section
/-! The base-point multiplication wrapper's local contract and scratch setup. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def scalarBaseLocal : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 32⟩
    let scalar : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let ws : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    s.rd = [scalar] ∧ s.wr = [out, ws] ∧ out.Disjoint scalar ∧ out.Disjoint ws ∧
      scalar.Disjoint ws ∧ (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  post s t := Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2

structure ScalarBasePre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 32⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r2), 8192⟩]
  out_scalar : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 32⟩
  out_ws : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  scalar_ws : (⟨State.addr (s.gpr .r1), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  f0 : (s.gpr .r0).toNat + 32 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 32 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32

theorem ScalarBasePre.of {s : State} (h : scalarBaseLocal.pre s) : ScalarBasePre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem scalarBaseSetup_ok {s : State} (h : ScalarBasePre s) :
    WP isa (.block scalarBaseSetup) s fun t =>
      Ctx (s.gpr .r2) t ∧ t.gpr .r12 = s.gpr .r1 ∧
      ScalarSaved (State.addr (s.gpr .r2)) s.gpr t.mem ∧
      t.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 48) 32 = s.gpr .r0 ∧
      Rest [.r0, .r12] s t ∧ Frame [⟨State.addr (s.gpr .r2), 52⟩] s.mem t.mem := by
  have hw : (⟨State.addr (s.gpr .r2), 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  rw [scalarBaseSetup]
  refine WP.append (scalarSave_ok rfl h.f2 hw) fun u ⟨su, fu, gu, ku⟩ => ?_
  refine wp_str (a := State.addr (s.gpr .r2) + BitVec.ofNat 64 48) (by decide)
    (by rw [gu]; exact addr_add (by have := h.f2; omega))
    (by rw [ku.wr]; exact in_base hw (by decide) (by decide)) fun v hv => ?_
  refine wp_mov (op2_reg _ _) fun w hw' => wp_mov (op2_reg _ _) fun t ht => WP.block_nil ?_
  have kt : Rest [.r0, .r12] s t :=
    (ku.mono (by decide)).trans ((hv.rest _).trans ((hw'.rest (by decide)).trans (ht.rest (by decide))))
  have mt : t.mem = u.mem.writeW (State.addr (s.gpr .r2) + BitVec.ofNat 64 48) (s.gpr .r0) := by
    rw [ht.mem, hw'.mem, hv.mem, gu]
  refine ⟨⟨?_, h.f2, by rw [kt.wr]; exact hw⟩, ?_, ?_, ?_, kt, ?_⟩
  · rw [ht.other _ (by decide), hw'.gpr, hv.gpr, gu]
  · rw [ht.gpr, hw'.other _ (by decide), hv.gpr, gu]
  · intro i hi
    rw [mt, Mem.readW_writeW_sep (Offset.sep _ (d := 4 * i) (e := 48) (n := 4) (k := 4) (by omega) (by omega) (by omega)) (by decide)]
    exact su i hi
  · rw [mt, Mem.readW_writeW_self32]
  · rw [mt]
    exact (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseCT`. -/
section
/-! The public ABI pointers survive the secret base-point computation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def BaseWrapCTPre (b p out : BitVec 32) (s : State) : Prop :=
  scalarBaseLocal.pre s ∧ s.gpr .r0 = out ∧ s.gpr .r1 = p ∧ s.gpr .r2 = b

def BaseWorkCTPre (b p out : BitVec 32) (s : State) : Prop :=
  BaseCTPre b p s ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 48) 32 = out

def BaseFinishCTPre (b out : BitVec 32) (s : State) : Prop :=
  Ctx b s ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 48) 32 = out

theorem scalarBaseSetup_ct (b p out : BitVec 32) :
    CT (fun x y => BaseWrapCTPre b p out x ∧ BaseWrapCTPre b p out y)
      (.block scalarBaseSetup) (fun x y => BaseWorkCTPre b p out x ∧ BaseWorkCTPre b p out y) := by
  apply ctBoth
  · apply ctRegs [.r0, .r1, .r2] _ (by taint_decide)
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  · intro s ⟨h, ho, hp, hb⟩
    have hs := ScalarBasePre.of h
    refine WP.mono (scalarBaseSetup_ok hs) fun t ⟨hc, hptr, _, hout, hr, _⟩ => ?_
    have hi : (⟨State.addr (s.gpr .r1), 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hs.rd]; simp
    have ht : BaseWorkCTPre (s.gpr .r2) (s.gpr .r1) (s.gpr .r0) t := by
      refine ⟨⟨hc, hptr, hs.f1, ?_, hs.scalar_ws⟩, hout⟩
      intro i hib
      rw [hr.rd, hr.wr]
      exact in_base hi (by omega) (by omega)
    rw [ho, hp, hb] at ht
    exact ht

theorem scalarBaseWork_ct (b p out : BitVec 32) :
    CT (fun x y => BaseWorkCTPre b p out x ∧ BaseWorkCTPre b p out y)
      scalarBaseEngine (fun x y => BaseFinishCTPre b out x ∧ BaseFinishCTPre b out y) := by
  apply ctBoth
  · exact (scalarBaseEngine_ct b p).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h)
  · intro s ⟨⟨hc, hp, hf, hr, hsep⟩, ho⟩
    refine WP.mono (scalarBaseEngine_ok hc hp hf hr hsep) fun t ⟨tk, _, _⟩ => ?_
    exact ⟨tk.ctx hc, (tk.word 48 (.inl rfl) (by decide)).trans ho⟩

theorem scalarBaseFinish_ct (b out : BitVec 32) :
    CT (fun x y => BaseFinishCTPre b out x ∧ BaseFinishCTPre b out y)
      (.block scalarBaseFinish) (fun _ _ => True) := by
  have hh : CT (fun x y => BaseFinishCTPre b out x ∧ BaseFinishCTPre b out y)
      (.block [.ldr .r12 .r0 48])
      (fun x y => (x.gpr .r0 = b ∧ x.gpr .r12 = out) ∧ (y.gpr .r0 = b ∧ y.gpr .r12 = out)) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    · intro s ⟨hc, ho⟩
      refine ldr0_ok hc (by decide) fun t ht => WP.block_nil ?_
      exact ⟨(ht.other _ (by decide)).trans hc.r0, ht.gpr.trans ho⟩
  change CT _ (.block (([.ldr .r12 .r0 48] : List Instr) ++ (packField FR 0 ++ scalarRestore))) _
  refine ctBlockAppend hh ?_
  apply ctRegs [.r0, .r12] _ (by taint_decide)
  intro x y h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  have hct (b p out : BitVec 32) :
      CT (fun x y => BaseWrapCTPre b p out x ∧ BaseWrapCTPre b p out y) scalarBase (fun _ _ => True) :=
    RelCT.seq (scalarBaseSetup_ct b p out) (RelCT.seq (scalarBaseWork_ct b p out) (scalarBaseFinish_ct b out))
  intro s t tx ty u v hs ht ⟨_, h0, h1, h2⟩ ex ey
  exact (hct (s.gpr .r2) (s.gpr .r1) (s.gpr .r0) _ _ _ _ _ _
    ⟨⟨hs, rfl, rfl, rfl⟩, ⟨ht, h0.symm, h1.symm, h2.symm⟩⟩ ex ey).1

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseMain`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarBaseFinish`. -/
section
/-! Canonical point output and restoration of the saved registers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarBaseFinish_ok {b p : BitVec 32} {s : State} (hc : Ctx b s)
    (hl : Lim s.mem (State.addr b) FR) (hp : s.mem.readW (State.addr b + BitVec.ofNat 64 48) 32 = p)
    (hfit : p.toNat + 32 ≤ 2 ^ 32) (hw : (⟨State.addr p, 32⟩ : Region) ∈ s.wr)
    (hsep : (⟨State.addr p, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    {g : Reg → BitVec 32} (hs : ScalarSaved (State.addr b) g s.mem) :
    WP isa (.block scalarBaseFinish) s fun t =>
      (∀ i < 8, t.gpr (scalarSavedReg i) = g (scalarSavedReg i)) ∧ Rest scalarFinishClob s t ∧
      Frame [⟨State.addr p, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr p) 32 = Spec.Ed25519.encodeLE 32 (V s.mem (State.addr b) FR) := by
  rw [scalarBaseFinish, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine ldr0_ok hc (by decide) fun u hu => ?_
  have hcu := hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  refine WP.append (packField_ok (p := p) (a := FR) (dst := 0) hcu (by decide) (hu.mem ▸ hl) (by decide)
    (hu.gpr.trans hp) (by omega)
    (fun i hi => by rw [hu.wr]; simpa only [Nat.zero_add] using in_base hw (by omega) (by omega))
    (by simpa only [BitVec.add_zero] using
      hsep.symm.sub_left (Offset.sub_base _ (by decide : FR + 64 ≤ 8192))))
    fun v ⟨kv, fv, vv⟩ => ?_
  have hcv := hcu.of_rest kv (by decide)
  have hs' : ScalarSaved (State.addr b) g v.mem :=
    (hu.mem ▸ hs).frame fv fun r hr i hi => by
      rw [List.mem_singleton.mp hr, BitVec.add_zero]
      exact hsep.symm.sub_left (Offset.sub_base _ (by omega))
  refine WP.mono (scalarRestore_ok hcv hs') fun t ⟨saved, kt, mt⟩ => ?_
  refine ⟨saved, (hu.rest (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide))), ?_, ?_⟩
  · rw [mt, ← hu.mem]; simpa only [BitVec.add_zero] using fv
  · rw [mt, scalar_packed_encode, ← hu.mem]
    have e : packedV v.mem (State.addr p) = V u.mem (State.addr b) FR := by
      simpa only [BitVec.add_zero] using vv
    exact congrArg (Spec.Ed25519.encodeLE 32) e

end VG.Proof.Ed25519.Arm
end

/-! Base-point multiplication, output encoding, and the complete ARM ABI. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarBase_correct {s : State} (h : ScalarBasePre s) :
    WP isa scalarBase s fun t => abiPreserved s t ∧ scalarBaseLocal.post s t := by
  refine WP.seq (WP.mono (scalarBaseSetup_ok h) fun u ⟨hcu, pu, su, ou, ku, fu⟩ => ?_)
  have input : (⟨State.addr (s.gpr .r1), 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine WP.seq (WP.mono (scalarBaseEngine_ok hcu pu h.f1
    (fun n hn => by rw [ku.rd, ku.wr]; exact in_base input (by omega) (by omega)) h.scalar_ws)
    fun v ⟨kv, lv, vv⟩ => ?_)
  have sv : ScalarSaved (State.addr (s.gpr .r2)) s.gpr v.mem :=
    su.frame kv.frame fun r hr i hi => by
      simp only [pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  have ov : v.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 48) 32 = s.gpr .r0 :=
    (kv.word 48 (.inl rfl) (by decide)).trans ou
  refine WP.mono (scalarBaseFinish_ok (kv.ctx hcu) lv ov h.f0
    (by rw [kv.rest.wr, ku.wr, h.wr]; simp) h.out_ws sv) fun t ⟨gt, kt, _, bt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [kt.sp, kv.rest.sp, ku.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact gt 0 (by decide)
    · exact gt 1 (by decide)
    · exact gt 2 (by decide)
    · exact gt 3 (by decide)
    · exact gt 4 (by decide)
    · exact gt 5 (by decide)
    · exact gt 6 (by decide)
    · exact gt 7 (by decide)
    · rw [kt.gpr _ (by decide), kv.rest.gpr _ (by decide), ku.gpr _ (by decide)]
  · have hb : Spec.Ed25519.bytesAt u.mem (State.addr (s.gpr .r1)) 32 =
        Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32 := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun n hn => fu.bytes (R := ⟨State.addr (s.gpr .r1), 32⟩)
        (fun r hr => ?_) (by decide : 32 ≤ 2 ^ 64) (List.mem_range.mp hn)
      rw [List.mem_singleton.mp hr]
      exact h.scalar_ws.sub_right (Region.sub_prefix (by decide))
    change Spec.Ed25519.bytesAt t.mem _ 32 = Spec.Ed25519.scalarBase _
    rw [bt, vv, hb, Spec.Ed25519.scalarBase, encodedValue_spec]

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarBaseLit`. -/
section
namespace VG.Impl.Ed25519.Arm
materialize_code scalarBase
end VG.Impl.Ed25519.Arm
end

/-! The complete base-point multiplier meets the merged specification,
preserves the ABI, and keeps all scalar bytes secret. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def baseSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩]

theorem scalarBase_ok (s : State) (hs : scalarBaseLocal.pre s) :
    ∃ t s', Exec isa scalarBase s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s' :=
  scalarBase_correct (ScalarBasePre.of hs)

theorem scalarBase_verified : Verified Arm.target scalarBase
    (Spec.Ed25519.scalarBaseContract Arm.abi) :=
  Verified.of_correct scalarBase_ok scalarBase_ct (by
    sig_implies [Spec.Ed25519.scalarBaseContract, Spec.Ed25519.scalarBaseSig,
      Spec.Ed25519.scratchWords, scalarBaseLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [baseSatState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using baseSatState)

end VG.Proof.Ed25519.Arm
