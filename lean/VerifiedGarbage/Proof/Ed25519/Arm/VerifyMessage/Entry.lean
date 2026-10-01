import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Args
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm

def verifyMessageLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨State.addr (s.gpr .r0),32⟩
    let msg : Region := ⟨State.addr (s.gpr .r1),(s.gpr .r2).toNat⟩
    let sig : Region := ⟨State.addr (s.gpr .r3),64⟩
    let scr : Region := ⟨State.addr (stackArg s 0),8192⟩
    let args : Region := ⟨State.addr s.sp,4⟩
    let stk : Region := ⟨State.addr s.sp - 280,280⟩
    s.rd = [pk,msg,sig,args] ∧ s.wr = [scr] ∧
    pk.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
    stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
    (s.gpr .r0).toNat+32≤2^32 ∧ (s.gpr .r1).toNat+(s.gpr .r2).toNat≤2^32 ∧
    (s.gpr .r3).toNat+64≤2^32 ∧ (stackArg s 0).toNat+8192≤2^32 ∧
    280≤s.sp.toNat ∧ s.sp.toNat+4≤2^32
  post s t := t.gpr .r0 = if Spec.Ed25519.verify (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r0)) 32)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r3)) 64) then 1 else 0
  pub s t := s.sp=t.sp ∧ s.gpr .r0=t.gpr .r0 ∧ s.gpr .r1=t.gpr .r1 ∧
    s.gpr .r2=t.gpr .r2 ∧ s.gpr .r3=t.gpr .r3 ∧ stackArg s 0=stackArg t 0 ∧
    Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r0)) 32 = Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r0)) 32 ∧
    Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r1)) (t.gpr .r2).toNat ∧
    Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r3)) 64 = Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r3)) 64

def lay (s : State) : Lay := ⟨s.gpr .r0,s.gpr .r1,s.gpr .r2,s.gpr .r3,stackArg s 0,Whole.base s⟩

theorem entry_below {s : State} (h : verifyMessageLocal.pre s) : 280≤s.sp.toNat := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hb,_⟩ := h
  exact hb

theorem entry_top {s : State} (h : verifyMessageLocal.pre s) : s.sp.toNat+4≤2^32 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,ht⟩ := h
  exact ht

theorem original_args {s : State} (hb : 280 ≤ s.sp.toNat) :
    (lay s).ORIGINALARGS = ⟨State.addr s.sp,4⟩ := by
  unfold Lay.ORIGINALARGS lay
  rw [Whole.base_addr hb, BitVec.sub_add_cancel]

theorem stack_eq {s : State} (hb : 280 ≤ s.sp.toNat) :
    Whole.stack s = ⟨State.addr s.sp-280,280⟩ := by
  unfold Whole.stack
  rw [Whole.base_addr hb]

theorem entry_writes {s : State} (h : verifyMessageLocal.pre s) :
    ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  have hb := entry_below h
  obtain ⟨_,hw,_,_,_,_,_,_,_,hc,_⟩ := h
  intro r hr
  rw [hw,List.mem_singleton] at hr
  subst r
  rw [stack_eq hb]
  exact hc

theorem lay_ok {s : State} (h : verifyMessageLocal.pre s) : (lay s).Ok := by
  obtain ⟨_,_,pc,mc,sc,ac,kp,km,ks,kc,np,nm,ns,nc,hb,_⟩ := h
  have fr : Region.Sub (Whole.FR (Whole.base s)) (Whole.stack s) := Region.sub_prefix (by decide)
  have ar : Region.Sub (Whole.ARGS (Whole.base s)) (Whole.stack s) := Offset.sub_base _ (by decide)
  rw [← stack_eq hb] at kp km ks kc
  refine ⟨?_,?_,?_,kc.sub_left fr,np,nm,ns,nc⟩
  · have he := Whole.base_top (s := s) hb
    have hs := s.sp.isLt
    change (Whole.base s).toNat+272≤2^32
    omega
  · simp only [Lay.inputs,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact pc
    · exact mc
    · exact sc
    · rw [original_args hb]; exact ac
    · exact kc.sub_left ar
  · simp only [Lay.inputs,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact kp.sub_left fr
    · exact km.sub_left fr
    · exact ks.sub_left fr
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.base_disjoint _ (by decide) (by decide)

theorem entry_ctx {s p : State} (h : verifyMessageLocal.pre s) (hp : Whole.Saved (Whole.entered s) 5 p) :
    Ctx (lay s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs _
  simp only [Lay.inputs, original_args (entry_below h)]
  simpa only [Whole.bodyRd,h.1,Whole.bodyWr,h.2.1,Lay.outputs,
    Lay.PK,Lay.MSG,Lay.SIG,Lay.SCR,Lay.ARGS,Whole.ARGS,show BitVec.ofNat 64 248 = (248 : Addr) from rfl,lay,List.cons_append,List.nil_append] using hc

theorem entry_regions {s : State} (h : verifyMessageLocal.pre s) :
    (lay s).inputs = Whole.bodyRd s ∧ (lay s).outputs = s.wr := by
  simp only [Lay.inputs, original_args (entry_below h)]
  simp only [Whole.bodyRd, h.1, Lay.outputs, h.2.1,
    Lay.SIG, Lay.PK, Lay.MSG, Lay.SCR, Lay.ARGS, Whole.ARGS,
    show BitVec.ofNat 64 248 = (248 : Addr) from rfl, lay, List.cons_append, List.nil_append]
  exact ⟨trivial, trivial⟩

theorem entry_args {s p : State} (h : verifyMessageLocal.pre s)
    (hp : Whole.Saved (Whole.entered s) 5 p) : Arguments (lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words (entry_below h) (by decide : 5 ≤ 6) (entry_top h) hp hj
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
    simpa only [Whole.originalWord, Impl.Ed25519.Arm.Whole.argReg, Nat.reduceLT, ite_true, ite_false,
      Nat.reduceSub, Nat.mul_zero, BitVec.add_zero, Lay.value, lay,
      stackArg, stackArgAddr] using hw

theorem entry_read {s : State} (h : verifyMessageLocal.pre s) : ∀ j < 5, 4 ≤ j →
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4*(j-4)))) 4 := by
  intro j hj h4
  have : j = 4 := by omega
  subst j
  simp only [Nat.reduceSub,Nat.mul_zero,BitVec.add_zero]
  exact ⟨⟨State.addr s.sp,4⟩, List.mem_append_left _ (by rw [h.1]; simp), by simp [Region.Contains]⟩

theorem entry_input {s : State} (h : verifyMessageLocal.pre s) {m : Mem}
    (hf : Frame [Whole.stack s] s.mem m) {r : Region} (hr : r ∈ s.rd) (hn : r.len≤2^64) :
    Spec.Ed25519.bytesAt m r.base r.len = Spec.Ed25519.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR]
  have hb := entry_below h
  obtain ⟨hrd,_,_,_,_,_,kp,km,ks,_⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rw [← stack_eq hb] at kp km ks
  rcases hr with rfl | rfl | rfl | rfl
  · exact kp.symm
  · exact km.symm
  · exact ks.symm
  · rw [← original_args hb]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm

end VG.Proof.Ed25519.Arm.VerifyMessage
