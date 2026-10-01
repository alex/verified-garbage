import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.CTCommon

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

def initValues : List (Reg × Value) := [(.r0, .caller 2 0)]
def updateValues : List (Reg × Value) := [(.r0, .caller 2 0), (.r2, .const 0), (.r3, .const 0)]
def updateStack : List Value := [.caller 1 0, .const 32, .caller 2 192]
def finalizeValues : List (Reg × Value) := [(.r0, .caller 2 0), (.r2, .const 32), (.r3, .const 0)]
def finalizeStack : List Value := [.frame 184, .caller 2 192]
def baseValues : List (Reg × Value) := [(.r0, .caller 0 0), (.r1, .frame 24), (.r2, .caller 2 0)]

variable {L : Lay} {t : State}

def init_ready (hL : L.Ok) (hs : Slots L initValues [] t) :
    Whole.CallReady (Proof.Sha512.initArm Spec.Sha512.H0_512) L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 2 0) (by simp [initValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨[], Whole.initWr L.scr, Whole.init_pre h0 hL.nc, Whole.covers_writes hw, hw⟩

def update_ready (hL : L.Ok) (he : t.sp = L.E) (hs : Slots L updateValues updateStack t) :
    Whole.CallReady Proof.Sha512.updateArm L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 2 0) (by simp [updateValues])
  have a0 := hs.2 0 (by decide)
  have a1 := hs.2 1 (by decide)
  have a2 := hs.2 2 (by decide)
  simp only [updateStack, argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 a0 a1 a2
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨Whole.updateRd L.E L.seed 32, Whole.hashWr L.scr,
    Whole.update_pre he h0 a0 a1 a2 hL.sc
      (hL.kc.sub_left (Region.sub_prefix (by decide : 12 ≤ 280))) hL.nc hL.ns
      (by have := hL.top; omega), update_covers L, hw⟩

def finalize_ready (hL : L.Ok) (he : t.sp = L.E) (hs : Slots L finalizeValues finalizeStack t) :
    Whole.CallReady Proof.Sha512.finalizeArm L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 2 0) (by simp [finalizeValues])
  have a0 := hs.2 0 (by decide)
  have a1 := hs.2 1 (by decide)
  simp only [finalizeStack, argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 a0 a1
  have hd : Region.Disjoint ⟨State.addr (L.E + 184), 64⟩ L.SCR := by
    rw [digest_addr hL]
    exact hL.kc.sub_left (Offset.sub_base _ (by decide : 184 + 64 ≤ 280))
  have ds : (Whole.CALLARGS L.E 8).Disjoint ⟨State.addr (L.E + 184), 64⟩ := by
    rw [digest_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)
  have nf : (L.E + 184).toNat + 64 ≤ 2 ^ 32 := by
    have ht := hL.top
    rw [BitVec.toNat_add_of_lt (by change L.E.toNat + 184 < 2 ^ 32; omega)]
    change L.E.toNat + 184 + 64 ≤ 2 ^ 32
    omega
  exact ⟨Whole.finalizeRd L.E, Whole.finalizeWr L.scr (L.E + 184),
    Whole.finalize_pre he h0 a0 a1 hd
      (hL.kc.sub_left (Region.sub_prefix (by decide : 8 ≤ 280))) ds hL.nc nf
      (by have := hL.top; omega), finalize_covers hL, finalize_writes hL⟩

def base_ready (hL : L.Ok) (hs : Slots L baseValues [] t) :
    Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs t := by
  have h0 := hs.1 (.r0, .caller 0 0) (by simp [baseValues])
  have h1 := hs.1 (.r1, .frame 24) (by simp [baseValues])
  have h2 := hs.1 (.r2, .caller 2 0) (by simp [baseValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  exact ⟨[⟨State.addr L.E + 24, 32⟩], L.outputs, base_pre hL ⟨h0, h1, h2⟩, base_covers L, base_writes L⟩

end VG.Proof.Ed25519.Arm.PublicKey
