import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.CTCommon

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

def initValues : List (Reg × Value) := [(.x0, .caller 2 0)]
def updateValues : List (Reg × Value) :=
  [(.x0, .caller 2 0), (.x1, .const 0), (.x2, .caller 1 0), (.x3, .const 32), (.x4, .caller 2 192)]
def finalizeValues : List (Reg × Value) :=
  [(.x0, .caller 2 0), (.x1, .const 32), (.x2, .frame 192), (.x3, .caller 2 192)]
def baseValues : List (Reg × Value) := [(.x0, .caller 0 0), (.x1, .frame 32), (.x2, .caller 2 0)]

variable {L : Lay} {t : State}

def init_ready (hs : Slots L initValues t) :
    Whole.CallReady (Proof.Sha512.initAArch64 Spec.Sha512.H0_512) L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 2 0) (by simp [initValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨[], Whole.initWr L.scr, Whole.init_pre h0, Whole.covers_writes hw, hw⟩

def update_ready (hL : L.Ok) (hs : Slots L updateValues t) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 2 0) (by simp [updateValues])
  have h2 := hs (.x2, .caller 1 0) (by simp [updateValues])
  have h3 := hs (.x3, .const 32) (by simp [updateValues])
  have h4 := hs (.x4, .caller 2 192) (by simp [updateValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h2 h3 h4
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine ⟨Whole.updateRd L.seed 32, Whole.hashWr L.scr, Whole.update_pre h0 h2 h3 h4 hL.sc, ?_, hw⟩
  intro a n hin
  obtain ⟨r, hr, hh⟩ := hin
  rcases List.mem_append.mp hr with hr | hr
  · simp only [Whole.updateRd, List.mem_singleton] at hr
    subst r
    exact ⟨L.SEED, List.mem_append_left _ (by simp [Lay.inputs]), hh⟩
  · exact Whole.covers_writes hw a n ⟨r, hr, hh⟩

def finalize_ready (hL : L.Ok) (hs : Slots L finalizeValues t) :
    Whole.CallReady Proof.Sha512.finalizeAArch64 L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 2 0) (by simp [finalizeValues])
  have h2 := hs (.x2, .frame 192) (by simp [finalizeValues])
  have h3 := hs (.x3, .caller 2 192) (by simp [finalizeValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h2 h3
  have hd : Region.Disjoint ⟨L.E + 192, 64⟩ L.SCR :=
    hL.kc.sub_left (Offset.sub_base _ (by decide : 192 + 64 ≤ 336))
  exact ⟨[], Whole.finalizeWr L.scr (L.E + 192), Whole.finalize_pre h0 h2 h3 hd,
    Whole.covers_writes (finalize_writes L), finalize_writes L⟩

def base_ready (hL : L.Ok) (hs : Slots L baseValues t) :
    Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 0 0) (by simp [baseValues])
  have h1 := hs (.x1, .frame 32) (by simp [baseValues])
  have h2 := hs (.x2, .caller 2 0) (by simp [baseValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  exact ⟨[⟨L.E + 32, 32⟩], L.outputs, base_pre hL ⟨h0, h1, h2⟩, base_covers L, base_writes L⟩

end VG.Proof.Ed25519.AArch64.PublicKey
