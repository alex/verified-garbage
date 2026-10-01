import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.CTReady

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
    (Proof.Sha512.AArch64.Stream.init_verified _).2.1 rfl
  · intro g v m t _ hs
    have a0 := hs (.x0,.caller 4 0) (by simp [initValues])
    change t.gpr .x0 = L.scr+0#64 at a0
    exact init_ready (a0.trans (BitVec.add_zero _))
  · intro a b ar aw br bw h
    simp only [Proof.Sha512.initAArch64,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
    exact ⟨call_gpr_eq h (p := (.x0,.caller 4 0)) (by simp [initValues]) (by decide),two_sp h⟩

theorem update_call_ct (backend : Whole.Backend) {args : List (Reg × Value)}
    (ready : ∀ {t}, OutArgs L args t → Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t)
    (hregs : ∀ r ∈ ([.x0,.x1,.x2,.x3,.x4] : List Reg), ∃ a, (r,a)∈args) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L args))
      (.call (Spec.Sha512.updateApi.name ++ backend.suffix) backend.update)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct backend.update_verified.1 backend.updateCT (Whole.update_noFrames backend) (fun _ h => ready h)
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
  apply call_ct backend.finalize_verified.1 backend.finalizeCT (Whole.finalize_noFrames backend)
  · intro g v m t _ hs
    have a0 := hs (.x0,.caller 4 0) (by simp [finalizeValues])
    have a2 := hs (.x2,.frame 192) (by simp [finalizeValues])
    have a3 := hs (.x3,.caller 4 192) (by simp [finalizeValues])
    change t.gpr .x0=L.scr+0#64 at a0
    exact finalize_ready hL (a0.trans (BitVec.add_zero _)) a2 a3
  · intro a b ar aw br bw h
    simp only [Proof.Sha512.finalizeAArch64,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
    exact ⟨call_gpr_eq h (p := (.x0,.caller 4 0)) (by simp [finalizeValues]) (by decide),
      call_gpr_eq h (p := (.x1,.caller 2 64)) (by simp [finalizeValues]) (by decide),
      call_gpr_eq h (p := (.x2,.frame 192)) (by simp [finalizeValues]) (by decide),
      call_gpr_eq h (p := (.x3,.caller 4 192)) (by simp [finalizeValues]) (by decide),two_sp h⟩

def prefix_ready {t : State} {source count : Nat}
    (hd : Region.Disjoint ⟨L.value source,32⟩ L.SCR)
    (hi : ∃ R ∈ L.inputs, Whole.Within ⟨L.value source,32⟩ R)
    (hs : OutArgs L (prefixValues source count) t) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t := by
  have a0 := hs (.x0,.caller 4 0) (by simp [prefixValues])
  have a2 := hs (.x2,.caller source 0) (by simp [prefixValues])
  have a3 := hs (.x3,.const 32) (by simp [prefixValues])
  have a4 := hs (.x4,.caller 4 192) (by simp [prefixValues])
  change t.gpr .x0=L.scr+0#64 at a0
  change t.gpr .x2=L.value source+0#64 at a2
  exact update_ready (a0.trans (BitVec.add_zero _)) (a2.trans (BitVec.add_zero _)) a3 a4 hd hi

def message_ready (hL : L.Ok) {t : State} (hs : OutArgs L messageValues t) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t := by
  have a0 := hs (.x0,.caller 4 0) (by simp [messageValues])
  have a2 := hs (.x2,.caller 1 0) (by simp [messageValues])
  have a3 := hs (.x3,.caller 2 0) (by simp [messageValues])
  have a4 := hs (.x4,.caller 4 192) (by simp [messageValues])
  change t.gpr .x0=L.scr+0#64 at a0
  change t.gpr .x2=L.msg+0#64 at a2
  change t.gpr .x3=L.len+0#64 at a3
  exact update_ready (a0.trans (BitVec.add_zero _)) (a2.trans (BitVec.add_zero _))
    (a3.trans (BitVec.add_zero _)) a4 (hL.sc _ (by simp [Lay.inputs]))
    ⟨L.MSG,by simp [Lay.inputs],0,(BitVec.add_zero _).symm,by simp⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
