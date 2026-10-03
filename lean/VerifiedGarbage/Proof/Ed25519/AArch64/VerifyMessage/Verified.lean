import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.CTReady
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Args
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Body
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverParity
import VerifiedGarbage.Proof.Framework.Contract

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.CTHashPipeline`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.CTHash`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole
open VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

def initValues : List (Reg × Value) := [(.x0,.caller 4 0)]
def prefixValues (source count : Nat) : List (Reg × Value) :=
  [(.x0,.caller 4 0),(.x1,.const count),(.x2,.caller source 0),(.x3,.const 32),(.x4,.caller 4 192)]
def messageValues : List (Reg × Value) :=
  [(.x0,.caller 4 0),(.x1,.const 64),(.x2,.caller 1 0),(.x3,.caller 2 0),(.x4,.caller 4 192)]
def finalizeValues : List (Reg × Value) :=
  [(.x0,.caller 4 0),(.x1,.caller 2 64),(.x2,.frame 192),(.x3,.caller 4 192)]

theorem init_call_ct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L initValues))
    (.call Spec.Sha512.init512Api.name (Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512))
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct (Proof.Sha512.AArch64.Stream.init_verified _).1
    (Proof.Sha512.AArch64.Stream.init_verified _).2.1 (Whole.depth_of_noFrames rfl)
  · intro g v m t _ hs
    have a0 := hs (.x0,.caller 4 0) (by simp [initValues])
    change t.gpr .x0 = L.scr+0#64 at a0
    exact init_ready (a0.trans (BitVec.add_zero _))
  · intro a b ar aw br bw h
    simp only [Proof.Sha512.initAArch64,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
    exact ⟨call_gpr_eq h (p := (.x0,.caller 4 0)) (by simp [initValues]) (by decide),two_sp h⟩

theorem update_call_ct (backend : Whole.Backend) {args : List (Reg × Value)}
    (ready : ∀ {t}, t.sp = L.E → OutArgs L args t →
      Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t)
    (hregs : ∀ r ∈ ([.x0,.x1,.x2,.x3,.x4] : List Reg), ∃ a, (r,a)∈args) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L args))
      (.call (Spec.Sha512.updateApi.name ++ backend.suffix) backend.update)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct backend.update_verified.1 backend.update_verified.2.1 (Whole.update_depth backend) (fun hc h => ready hc.sp h)
  intro a b ar aw br bw h
  have eq (r : Reg) (hr : r ∈ ([.x0,.x1,.x2,.x3,.x4] : List Reg)) : a.callEntry.gpr r=b.callEntry.gpr r := by
    obtain ⟨val,hval⟩ := hregs r hr
    exact call_gpr_eq h hval ((by decide : ∀ r ∈ ([.x0,.x1,.x2,.x3,.x4] : List Reg),r∉linkRegs) r hr)
  simp only [Proof.Sha512.updateAArch64,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
  exact ⟨eq .x0 (by simp),eq .x1 (by simp),eq .x2 (by simp),eq .x3 (by simp),eq .x4 (by simp),two_sp h⟩

theorem finalize_call_ct (backend : Whole.Backend) (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L finalizeValues))
      (.call (Spec.Sha512.finalizeApi.name ++ backend.suffix) backend.finalize)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct backend.finalize_verified.1 backend.finalize_verified.2.1 (Whole.finalize_depth backend)
  · intro g v m t hc hs
    have a0 := hs (.x0,.caller 4 0) (by simp [finalizeValues])
    have a2 := hs (.x2,.frame 192) (by simp [finalizeValues])
    have a3 := hs (.x3,.caller 4 192) (by simp [finalizeValues])
    change t.gpr .x0=L.scr+0#64 at a0
    exact finalize_ready hL hc.sp (a0.trans (BitVec.add_zero _)) a2 a3
  · intro a b ar aw br bw h
    simp only [Proof.Sha512.finalizeAArch64,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
    exact ⟨call_gpr_eq h (p := (.x0,.caller 4 0)) (by simp [finalizeValues]) (by decide),
      call_gpr_eq h (p := (.x1,.caller 2 64)) (by simp [finalizeValues]) (by decide),
      call_gpr_eq h (p := (.x2,.frame 192)) (by simp [finalizeValues]) (by decide),
      call_gpr_eq h (p := (.x3,.caller 4 192)) (by simp [finalizeValues]) (by decide),two_sp h⟩

def prefix_ready (hL : L.Ok) {source count : Nat}
    (hd : Region.Disjoint ⟨L.value source,32⟩ L.SCR)
    (hi : ∃ R ∈ L.inputs, Whole.Within ⟨L.value source,32⟩ R) {t : State} (hsp : t.sp = L.E)
    (hs : OutArgs L (prefixValues source count) t) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t := by
  have a0 := hs (.x0,.caller 4 0) (by simp [prefixValues])
  have a2 := hs (.x2,.caller source 0) (by simp [prefixValues])
  have a3 := hs (.x3,.const 32) (by simp [prefixValues])
  have a4 := hs (.x4,.caller 4 192) (by simp [prefixValues])
  change t.gpr .x0=L.scr+0#64 at a0
  change t.gpr .x2=L.value source+0#64 at a2
  exact update_ready hL hsp (a0.trans (BitVec.add_zero _)) (a2.trans (BitVec.add_zero _)) a3 a4 hd hi

def message_ready (hL : L.Ok) {t : State} (hsp : t.sp = L.E) (hs : OutArgs L messageValues t) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t := by
  have a0 := hs (.x0,.caller 4 0) (by simp [messageValues])
  have a2 := hs (.x2,.caller 1 0) (by simp [messageValues])
  have a3 := hs (.x3,.caller 2 0) (by simp [messageValues])
  have a4 := hs (.x4,.caller 4 192) (by simp [messageValues])
  change t.gpr .x0=L.scr+0#64 at a0
  change t.gpr .x2=L.msg+0#64 at a2
  change t.gpr .x3=L.len+0#64 at a3
  exact update_ready hL hsp (a0.trans (BitVec.add_zero _)) (a2.trans (BitVec.add_zero _))
    (a3.trans (BitVec.add_zero _)) a4 (hL.sc _ (by simp [Lay.inputs]))
    ⟨L.MSG,by simp [Lay.inputs],0,(BitVec.add_zero _).symm,by simp⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem hash_ct (backend : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hash backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have i := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb initValues
    (by decide) (by simp [initValues,Whole.valid]) (by simp [initValues,known])
    (by simp [initValues,preserved]) (by taint_decide)
  have r := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb (prefixValues 3 0)
    (by decide) (by simp [prefixValues,Whole.valid]) (by simp [prefixValues,known])
    (by simp [prefixValues,preserved]) (by taint_decide)
  have a := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb (prefixValues 0 32)
    (by decide) (by simp [prefixValues,Whole.valid]) (by simp [prefixValues,known])
    (by simp [prefixValues,preserved]) (by taint_decide)
  have m := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb messageValues
    (by decide) (by simp [messageValues,Whole.valid]) (by simp [messageValues,known])
    (by simp [messageValues,preserved]) (by taint_decide)
  have f := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb finalizeValues
    (by decide) (by simp [finalizeValues,Whole.valid]) (by simp [finalizeValues,known])
    (by simp [finalizeValues,preserved]) (by taint_decide)
  have rc := update_call_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (m₁ := m₁) (m₂ := m₂)
    backend (args := prefixValues 3 0) (prefix_ready hL (input_sig hL).1 (input_sig hL).2)
    (by simp [prefixValues])
  have ac := update_call_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (m₁ := m₁) (m₂ := m₂)
    backend (args := prefixValues 0 32) (prefix_ready hL (input_pk hL).1 (input_pk hL).2)
    (by simp [prefixValues])
  have mc := update_call_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (m₁ := m₁) (m₂ := m₂)
    backend (args := messageValues) (message_ready hL) (by simp [messageValues])
  exact (i.seq init_call_ct).seq ((r.seq rc).seq ((a.seq ac).seq ((m.seq mc).seq (f.seq (finalize_call_ct backend hL)))))

/-- Public inputs give a common digest for the equation check that follows. -/
theorem hash_result_ct (backend : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hm : hashInput L m₁ = hashInput L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hash backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+192) 64 =
        Spec.Sha512.sha512 (hashInput L m₁)) := by
  refine two_wp ((hash_ct backend hL ha hb).mono (fun _ _ h => h) (fun _ _ _ => trivial)) ?_ ?_
  · intro s hc _
    exact hash_ok backend hc hL ha
  · intro s hc _
    have h := hash_ok backend hc hL hb
    rw [← hm] at h
    exact h

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Entry`. -/
section
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
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.CT`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.CTScalars`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

def reduceValues : List (Reg × Value) := [(.x0,.frame 128),(.x1,.frame 192),(.x2,.caller 4 0)]

theorem reduce_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L reduceValues))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.AArch64.scalarReduce)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarReduce_ok scalarReduce_ct (Whole.depth_of_noFrames reduce_noFrames)
  · intro g v m t _ hs
    have a0 := hs (.x0,.frame 128) (by simp [reduceValues])
    have a1 := hs (.x1,.frame 192) (by simp [reduceValues])
    have a2 := hs (.x2,.caller 4 0) (by simp [reduceValues])
    change t.gpr .x2=L.scr+0#64 at a2
    exact reduce_ready hL ⟨a0,a1,a2.trans (BitVec.add_zero _)⟩
  · intro a b ar aw br bw h
    simp only [scalarReduceLocal,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
    exact ⟨two_sp h,call_gpr_eq h (p := (.x0,.frame 128)) (by simp [reduceValues]) (by decide),
      call_gpr_eq h (p := (.x1,.frame 192)) (by simp [reduceValues]) (by decide),
      call_gpr_eq h (p := (.x2,.caller 4 0)) (by simp [reduceValues]) (by decide)⟩

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+192) 64=digest)
      (callWith reduceArgs "vg_ed25519_scalar_reduce" Impl.Ed25519.AArch64.scalarReduce)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+128) 32=Spec.Ed25519.scalarReduce digest) := by
  have hs := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb reduceValues
    (by decide) (by simp [reduceValues,Whole.valid]) (by simp [reduceValues,known])
    (by simp [reduceValues,preserved]) (by taint_decide)
  refine two_wp ((hs.seq (reduce_call_ct hL)).mono
    (fun _ _ h => ⟨h.1,h.2.1,trivial,trivial⟩) (fun _ _ _ => trivial)) ?_ ?_
  · intro s hc hd
    exact WP.mono (reduce_step hc hL ha) fun t ⟨ht,_,hr⟩ => ⟨ht,by rw [hr,hd]⟩
  · intro s hc hd
    exact WP.mono (reduce_step hc hL hb) fun t ⟨ht,_,hr⟩ => ⟨ht,by rw [hr,hd]⟩

theorem extend_ct (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+128) 32=Spec.Ed25519.scalarReduce digest)
      (.block extendChallenge)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+128) 64=
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L)) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) (by taint_decide)) ?_ ?_
  · intro s hc hd
    exact extend_step hc hd
  · intro s hc hd
    exact extend_step hc hd

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.CTEquation`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem equation_setup_wp {g v m t} (hc : Ctx L g v m t) (hL : L.Ok) (ha : Arguments L m)
    {ch : List Byte} (hh : Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = ch) :
    WP isa (.block VerifyMessage.equationArgs) t fun u => Ctx L g v m u ∧ EqArgs L u ∧
      Spec.Ed25519.bytesAt u.mem (L.E + 128) 64 = ch := by
  refine WP.mono (args_ok hc hL ha
    (args := [(.x0,.caller 0 0),(.x1,.caller 3 0),(.x2,.frame 128),(.x3,.caller 4 0)])
    (by simp) (by simp [Whole.valid]) (by simp [known]) (by simp [preserved])) ?_
  intro u ⟨hu,hm,hav⟩
  have a0 := hav (.x0,.caller 0 0) (by simp)
  have a1 := hav (.x1,.caller 3 0) (by simp)
  have a2 := hav (.x2,.frame 128) (by simp)
  have a3 := hav (.x3,.caller 4 0) (by simp)
  change u.gpr .x0 = L.pk+0#64 at a0
  change u.gpr .x1 = L.sig+0#64 at a1
  change u.gpr .x3 = L.scr+0#64 at a3
  rw [BitVec.add_zero] at a0 a1 a3
  exact ⟨hu,⟨a0,a1,a2,a3⟩,hm ▸ hh⟩

theorem equation_call_ct (hL : L.Ok) {challenge : List Byte}
    (hpk : Spec.Ed25519.bytesAt m₁ L.pk 32 = Spec.Ed25519.bytesAt m₂ L.pk 32)
    (hsig : Spec.Ed25519.bytesAt m₁ L.sig 64 = Spec.Ed25519.bytesAt m₂ L.sig 64) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => EqArgs L t ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = challenge)
      (.call "vg_ed25519_verify_equation" verifyEquation)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct verify_ok verify_ct (Whole.depth_of_noFrames equation_noFrames) (fun _ h => equation_ready hL h.1)
  intro a b ar aw br bw h
  have hsp := two_sp h
  have aa := h.2.2.1.1
  have ab := h.2.2.2.1
  have pk₁ := Ctx.input_bytes h.1 hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  have pk₂ := Ctx.input_bytes h.2.1 hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  have sig₁ := Ctx.input_bytes h.1 hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide)
  have sig₂ := Ctx.input_bytes h.2.1 hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide)
  simp only [verifyLocal, State.withRegions_gpr, State.withRegions_mem, State.withRegions_sp,
    State.callEntry_mem, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    aa.1, aa.2.1, aa.2.2.1, aa.2.2.2, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2]
  exact ⟨hsp,trivial,trivial,trivial,trivial,pk₁.trans (hpk.trans pk₂.symm),
    sig₁.trans (hsig.trans sig₂.symm),h.2.2.1.2.trans h.2.2.2.2.symm⟩

theorem equation_step_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    {challenge : List Byte}
    (hpk : Spec.Ed25519.bytesAt m₁ L.pk 32 = Spec.Ed25519.bytesAt m₂ L.pk 32)
    (hsig : Spec.Ed25519.bytesAt m₁ L.sig 64 = Spec.Ed25519.bytesAt m₂ L.sig 64) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = challenge)
      (Whole.callWith VerifyMessage.equationArgs "vg_ed25519_verify_equation" verifyEquation)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hs : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = challenge)
      (.block VerifyMessage.equationArgs)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => EqArgs L t ∧ Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 = challenge) := by
    apply two_wp (Whole.block_rel (fun _ _ h => two_sp h) (by taint_decide))
    · intro t hc hh
      exact equation_setup_wp hc hL ha hh
    · intro t hc hh
      exact equation_setup_wp hc hL hb hh
  exact hs.seq (equation_call_ct hL hpk hsig)

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Correct`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage

theorem verifyMessage_ok (backend : Whole.Backend) {s : State} (h : verifyMessageLocal.pre s) :
    WP isa (code backend.code backend.suffix) s fun u => abiPreserved s u ∧ verifyMessageLocal.post s u := by
  have hw := Whole.wrap_ok (body_depth backend) (entry_below h) (entry_writes h)
    (P := fun m _ r => r = signWord (Spec.Ed25519.verify
      (Spec.Ed25519.bytesAt m (s.gpr .x0) 32)
      (Spec.Ed25519.bytesAt m (s.gpr .x1) (s.gpr .x2).toNat)
      (Spec.Ed25519.bytesAt m (s.gpr .x3) 64)))
    (fun p hp => WP.mono (body_ok backend (entry_ctx h hp) (lay_ok h) (entry_args hp))
      fun u ⟨hu,ho⟩ => ⟨by
        simpa only [Whole.bodyRd,h.1,Ctx,Lay.inputs,Lay.outputs,Lay.PK,Lay.MSG,Lay.SIG,
          Lay.SCR,Lay.ARGS,lay,h.2.1,List.cons_append,List.nil_append] using hu,ho⟩)
  refine WP.mono hw fun u ⟨hu,m,hf,hp⟩ => ⟨hu,?_⟩
  have pk := entry_input h hf (r := ⟨s.gpr .x0,32⟩) (by rw [h.1]; simp) (by change 32≤2^64; decide)
  have msg := entry_input h hf (r := ⟨s.gpr .x1,(s.gpr .x2).toNat⟩) (by rw [h.1]; simp)
    (by change (s.gpr .x2).toNat≤2^64; exact Nat.le_of_lt (s.gpr .x2).isLt)
  have sig := entry_input h hf (r := ⟨s.gpr .x3,64⟩) (by rw [h.1]; simp) (by change 64≤2^64; decide)
  change u.gpr .x0 = signWord _
  rw [hp,pk,msg,sig]

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem body_ct (backend : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hpk : Spec.Ed25519.bytesAt m₁ L.pk 32=Spec.Ed25519.bytesAt m₂ L.pk 32)
    (hmsg : Spec.Ed25519.bytesAt m₁ L.msg L.len.toNat=Spec.Ed25519.bytesAt m₂ L.msg L.len.toNat)
    (hsig : Spec.Ed25519.bytesAt m₁ L.sig 64=Spec.Ed25519.bytesAt m₂ L.sig 64) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (body backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hm : hashInput L m₁=hashInput L m₂ := by
    rw [hashInput_eq,hashInput_eq,hpk,hmsg,hsig]
  exact (hash_result_ct backend hL ha hb hm).seq
    ((reduce_ct hL ha hb _).seq ((extend_ct _).seq (equation_step_ct hL ha hb hpk hsig)))

theorem lay_eq {s t : State} (h : verifyMessageLocal.pub s t) : lay s=lay t := by
  obtain ⟨sp,h0,h1,h2,h3,h4,_⟩ := h
  simp only [lay,Whole.base,sp,h0,h1,h2,h3,h4]

theorem saved_inputs_eq {s t p q : State} (hs : verifyMessageLocal.pre s) (ht : verifyMessageLocal.pre t)
    (hp : verifyMessageLocal.pub s t) (hpa : Whole.Saved (Whole.entered s) 6 p)
    (hqb : Whole.Saved (Whole.entered t) 6 q) :
    Spec.Ed25519.bytesAt p.mem (lay s).pk 32 = Spec.Ed25519.bytesAt q.mem (lay s).pk 32 ∧
    Spec.Ed25519.bytesAt p.mem (lay s).msg (lay s).len.toNat =
      Spec.Ed25519.bytesAt q.mem (lay s).msg (lay s).len.toNat ∧
    Spec.Ed25519.bytesAt p.mem (lay s).sig 64 = Spec.Ed25519.bytesAt q.mem (lay s).sig 64 := by
  have fp := Whole.saved_frame hpa
  have fq := Whole.saved_frame hqb
  obtain ⟨_,h0,h1,h2,h3,_,pk,msg,sig⟩ := hp
  have epk := entry_input hs fp (r := ⟨s.gpr .x0,32⟩) (by rw [hs.1]; simp) (by change 32≤2^64; decide)
  have fpk := entry_input ht fq (r := ⟨t.gpr .x0,32⟩) (by rw [ht.1]; simp) (by change 32≤2^64; decide)
  have emsg := entry_input hs fp (r := ⟨s.gpr .x1,(s.gpr .x2).toNat⟩) (by rw [hs.1]; simp)
    (Nat.le_of_lt (s.gpr .x2).isLt)
  have fmsg := entry_input ht fq (r := ⟨t.gpr .x1,(t.gpr .x2).toNat⟩) (by rw [ht.1]; simp)
    (Nat.le_of_lt (t.gpr .x2).isLt)
  have esig := entry_input hs fp (r := ⟨s.gpr .x3,64⟩) (by rw [hs.1]; simp) (by change 64≤2^64; decide)
  have fsig := entry_input ht fq (r := ⟨t.gpr .x3,64⟩) (by rw [ht.1]; simp) (by change 64≤2^64; decide)
  change Spec.Ed25519.bytesAt p.mem (s.gpr .x0) 32=Spec.Ed25519.bytesAt q.mem (s.gpr .x0) 32 ∧
    Spec.Ed25519.bytesAt p.mem (s.gpr .x1) (s.gpr .x2).toNat=Spec.Ed25519.bytesAt q.mem (s.gpr .x1) (s.gpr .x2).toNat ∧
    Spec.Ed25519.bytesAt p.mem (s.gpr .x3) 64=Spec.Ed25519.bytesAt q.mem (s.gpr .x3) 64
  rw [epk,emsg,esig,h0,h1,h2,h3,fpk,fmsg,fsig]
  rw [h0] at pk
  rw [h1,h2] at msg
  rw [h3] at sig
  exact ⟨pk,msg,sig⟩

theorem verifyMessage_ct (backend : Whole.Backend) :
    ConstantTime isa verifyMessageLocal.pre verifyMessageLocal.pub (code backend.code backend.suffix) := by
  refine Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok backend (entry_ctx hs hp) (lay_ok hs) (entry_args hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p,q,hpa,hqb,rfl,rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr t.v q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args hqb
    obtain ⟨pk,msg,sig⟩ := saved_inputs_eq hs ht hp hpa hqb
    exact ⟨(body_ct backend (lay_ok hs) (entry_args hpa) hqa pk msg sig _ _ _ _ _ _
      ⟨entry_ctx hs hpa,hq,trivial,trivial⟩ ea eb).1,trivial⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Contract`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64

def verifySatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 64 | .x3 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000,32⟩,⟨0x2000,64⟩,⟨0x3000,64⟩]
  wr := [⟨0x4000,8192⟩]

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem verifyMessage_implies : verifyMessageLocal.Implies (Spec.Ed25519.verifyContract AArch64.abi 352) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, verifyMessageLocal, below,
      AArch64.abi,AArch64.argRegs]
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, AArch64.abi,AArch64.argRegs]
    change t.gpr .x0 = signWord _ at h
    rw [h]
    generalize Spec.Ed25519.verify (Spec.Ed25519.bytesAt s.mem (s.gpr .x0) 32)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .x3) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, AArch64.abi,AArch64.argRegs] at h
    obtain ⟨sp, bytes, pk, msg, len, sig, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    obtain ⟨first, middle⟩ := List.append_inj' first (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, len])
    exact ⟨sp, pk, msg, len, sig, base, first, middle, last⟩
  sat := by
    sig_implies_sat [Spec.Ed25519.verifyContract,Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords,verifyMessageLocal,below,AArch64.abi,AArch64.argRegs]
      [verifySatState] using verifySatState

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage

theorem verifyMessage_verified (backend : Whole.Backend) :
    Verified AArch64.target (code backend.code backend.suffix) (Spec.Ed25519.verifyContract AArch64.abi 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => verifyMessage_ok backend h) (verifyMessage_ct backend)
      (.refl verifyMessage_implies.sat_left)) verifyMessage_implies

end VG.Proof.Ed25519.AArch64.VerifyMessage
