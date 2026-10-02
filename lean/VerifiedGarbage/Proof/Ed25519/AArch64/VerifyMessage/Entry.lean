import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Args
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64

def verifyMessageLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .x0,32⟩
    let msg : Region := ⟨s.gpr .x1,(s.gpr .x2).toNat⟩
    let sig : Region := ⟨s.gpr .x3,64⟩
    let scr : Region := ⟨s.gpr .x4,8192⟩
    let stk : Region := below s.sp 352
    s.rd = [pk,msg,sig] ∧ s.wr = [scr] ∧
    pk.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧
    stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
    (s.gpr .x0).toNat+32≤2^64 ∧ (s.gpr .x1).toNat+(s.gpr .x2).toNat≤2^64 ∧
    (s.gpr .x3).toNat+64≤2^64 ∧ (s.gpr .x4).toNat+8192≤2^64 ∧ 352≤s.sp.toNat
  post s t := t.gpr .x0 = if Spec.Ed25519.verify (Spec.Ed25519.bytesAt s.mem (s.gpr .x0) 32)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .x3) 64) then 1 else 0
  pub s t := s.sp=t.sp ∧ s.gpr .x0=t.gpr .x0 ∧ s.gpr .x1=t.gpr .x1 ∧
    s.gpr .x2=t.gpr .x2 ∧ s.gpr .x3=t.gpr .x3 ∧ s.gpr .x4=t.gpr .x4 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .x0) 32 = Spec.Ed25519.bytesAt t.mem (t.gpr .x0) 32 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.Ed25519.bytesAt t.mem (t.gpr .x1) (t.gpr .x2).toNat ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .x3) 64 = Spec.Ed25519.bytesAt t.mem (t.gpr .x3) 64

def lay (s : State) : Lay := ⟨s.gpr .x0,s.gpr .x1,s.gpr .x2,s.gpr .x3,s.gpr .x4,Whole.base s⟩

theorem entry_below {s : State} (h : verifyMessageLocal.pre s) : 352≤s.sp.toNat := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hb⟩ := h
  exact hb

theorem entry_writes {s : State} (h : verifyMessageLocal.pre s) :
    ∀ r ∈ s.wr, (below s.sp 352).Disjoint r := by
  obtain ⟨_,hw,_,_,_,_,_,_,hc,_⟩ := h
  intro r hr
  rw [hw,List.mem_singleton] at hr
  subst r
  exact hc

theorem lay_ok {s : State} (h : verifyMessageLocal.pre s) : (lay s).Ok := by
  obtain ⟨_,_,pc,mc,sc,kp,km,ks,kc,np,nm,ns,nc,hb⟩ := h
  have stk := Whole.stk_sub s
  have fr : Region.Sub (Whole.FR (Whole.base s)) (below s.sp 352) :=
    fun a h => stk a ((Region.sub_prefix (by decide) : Region.Sub (Whole.FR (Whole.base s)) ⟨Whole.base s, 336⟩) a h)
  have ar : Region.Sub (Whole.ARGS (Whole.base s)) (below s.sp 352) :=
    fun a h => stk a ((Offset.sub_base _ (by decide) : Region.Sub (Whole.ARGS (Whole.base s)) ⟨Whole.base s, 336⟩) a h)
  have ck := Whole.ck_sub s
  refine ⟨?_,?_,?_,kc.sub_left fr,np,nm,ns,nc,Whole.base_16 hb,?_,kc.sub_left ck⟩
  · change (s.sp-336#64).toNat+304≤2^64
    rw [BitVec.toNat_sub_of_le (by change 336≤s.sp.toNat; omega)]
    have hs := s.sp.isLt
    change s.sp.toNat-336+304≤2^64
    omega
  · simp only [Lay.inputs,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact pc
    · exact mc
    · exact sc
    · exact kc.sub_left ar
  · simp only [Lay.inputs,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact kp.sub_left fr
    · exact km.sub_left fr
    · exact ks.sub_left fr
    · exact Offset.base_disjoint _ (by decide) (by decide)
  · simp only [Lay.inputs,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact kp.sub_left ck
    · exact km.sub_left ck
    · exact ks.sub_left ck
    · exact Whole.ck_frame (by decide : 256 + 48 ≤ 304)

theorem entry_ctx {s p : State} (h : verifyMessageLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Ctx (lay s) s.gpr s.v p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  simpa only [Whole.bodyRd,h.1,Whole.bodyWr,h.2.1,Ctx,Lay.inputs,Lay.outputs,
    Lay.PK,Lay.MSG,Lay.SIG,Lay.SCR,Lay.ARGS,lay,List.cons_append,List.nil_append] using hc

theorem entry_args {s p : State} (hp : Whole.Saved (Whole.entered s) 6 p) : Arguments (lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words hp (j := j) (by omega)
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl <;> exact hw

theorem entry_input {s : State} (h : verifyMessageLocal.pre s) {m : Mem}
    (hf : Frame [below s.sp 336] s.mem m) {r : Region} (hr : r ∈ s.rd) (hn : r.len≤2^64) :
    Spec.Ed25519.bytesAt m r.base r.len = Spec.Ed25519.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR]
  obtain ⟨hrd,_,_,_,_,kp,km,ks,_⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  have hb : Region.Sub (below s.sp 336) (below s.sp 352) := below_sub (by decide) (by decide)
  rcases hr with rfl | rfl | rfl
  · exact (kp.sub_left hb).symm
  · exact (km.sub_left hb).symm
  · exact (ks.sub_left hb).symm

end VG.Proof.Ed25519.AArch64.VerifyMessage
