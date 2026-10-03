import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.CTCommon

/-! Merged from `Proof.Ed25519.AArch64.PublicKey.CT`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.PublicKey.CTReady`. -/
section
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

def update_ready (hL : L.Ok) (hsp : t.sp = L.E) (hs : Slots L updateValues t) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 2 0) (by simp [updateValues])
  have h2 := hs (.x2, .caller 1 0) (by simp [updateValues])
  have h3 := hs (.x3, .const 32) (by simp [updateValues])
  have h4 := hs (.x4, .caller 2 192) (by simp [updateValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h2 h3 h4
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine ⟨Whole.updateRd L.seed 32, Whole.hashWr L.scr, Whole.update_pre h0 h2 h3 h4 hL.sc
    (by rw [hsp]; exact hL.e16) (by rw [hsp]; exact hL.cc) (by rw [hsp]; exact hL.cs), ?_, hw⟩
  intro a n hin
  obtain ⟨r, hr, hh⟩ := hin
  rcases List.mem_append.mp hr with hr | hr
  · simp only [Whole.updateRd, List.mem_singleton] at hr
    subst r
    exact ⟨L.SEED, List.mem_append_left _ (by simp [Lay.inputs]), hh⟩
  · exact Whole.covers_writes hw a n ⟨r, hr, hh⟩

def finalize_ready (hL : L.Ok) (hsp : t.sp = L.E) (hs : Slots L finalizeValues t) :
    Whole.CallReady Proof.Sha512.finalizeAArch64 L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 2 0) (by simp [finalizeValues])
  have h2 := hs (.x2, .frame 192) (by simp [finalizeValues])
  have h3 := hs (.x3, .caller 2 192) (by simp [finalizeValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h2 h3
  have hd : Region.Disjoint ⟨L.E + 192, 64⟩ L.SCR :=
    hL.kc.sub_left (Offset.sub_base _ (by decide : 192 + 64 ≤ 336))
  exact ⟨[], Whole.finalizeWr L.scr (L.E + 192), Whole.finalize_pre h0 h2 h3 hd
    (by rw [hsp]; exact hL.e16) (by rw [hsp]; exact hL.cc)
    (by rw [hsp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)),
    Whole.covers_writes (finalize_writes L), finalize_writes L⟩

def base_ready (hL : L.Ok) (hs : Slots L baseValues t) :
    Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs t := by
  have h0 := hs (.x0, .caller 0 0) (by simp [baseValues])
  have h1 := hs (.x1, .frame 32) (by simp [baseValues])
  have h2 := hs (.x2, .caller 2 0) (by simp [baseValues])
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  exact ⟨[⟨L.E + 32, 32⟩], L.outputs, base_pre hL ⟨h0, h1, h2⟩, base_covers L, base_writes L⟩

end VG.Proof.Ed25519.AArch64.PublicKey
end

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

variable {L : Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem init_ct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L initValues))
    (.call Spec.Sha512.init512Api.name (Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512))
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct (Proof.Sha512.AArch64.Stream.init_verified _).1
    (Proof.Sha512.AArch64.Stream.init_verified _).2.1 (Whole.depth_of_noFrames rfl) (fun _ _ h => init_ready h)
  · intro a b ar aw br bw hsp hg
    exact ⟨hg (.x0, .caller 2 0) (by simp [initValues]), hsp⟩
  · simp [initValues, linkRegs]

theorem update_ct (v : Whole.Backend) (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L updateValues))
      (.call (Spec.Sha512.updateApi.name ++ v.suffix) v.update)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct v.update_verified.1 v.update_verified.2.1 (Whole.update_depth v) (fun _ hsp h => update_ready hL hsp h)
  · intro a b ar aw br bw hsp hg
    exact ⟨hg (.x0, .caller 2 0) (by simp [updateValues]), hg (.x1, .const 0) (by simp [updateValues]),
      hg (.x2, .caller 1 0) (by simp [updateValues]), hg (.x3, .const 32) (by simp [updateValues]),
      hg (.x4, .caller 2 192) (by simp [updateValues]), hsp⟩
  · simp [updateValues, linkRegs]

theorem finalize_ct (v : Whole.Backend) (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L finalizeValues))
      (.call (Spec.Sha512.finalizeApi.name ++ v.suffix) v.finalize)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct v.finalize_verified.1 v.finalize_verified.2.1 (Whole.finalize_depth v) (fun _ hsp h => finalize_ready hL hsp h)
  · intro a b ar aw br bw hsp hg
    exact ⟨hg (.x0, .caller 2 0) (by simp [finalizeValues]), hg (.x1, .const 32) (by simp [finalizeValues]),
      hg (.x2, .frame 192) (by simp [finalizeValues]), hg (.x3, .caller 2 192) (by simp [finalizeValues]), hsp⟩
  · simp [finalizeValues, linkRegs]

theorem base_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L baseValues))
    (.call "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarBase_ok scalarBase_ct (Whole.depth_of_noFrames base_noFrames) (fun _ _ h => base_ready hL h)
  · intro a b ar aw br bw hsp hg
    exact ⟨hsp, hg (.x0, .caller 0 0) (by simp [baseValues]), hg (.x1, .frame 32) (by simp [baseValues]),
      hg (.x2, .caller 2 0) (by simp [baseValues])⟩
  · simp [baseValues, linkRegs]

theorem prune_ct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block prune)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (by taint_decide)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (prune_step hc (digest := Spec.Ed25519.bytesAt t.mem (L.E + 192) 64) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (prune_step hc (digest := Spec.Ed25519.bytesAt t.mem (L.E + 192) 64) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block wipe)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (by taint_decide)) ?_ ?_
  · intro t ⟨hc, _⟩; exact WP.mono (wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩; exact WP.mono (wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem body_ct (v : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (body v.code v.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have i := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb initValues
    (by decide) (by simp [initValues, Whole.valid]) (by simp [initValues])
    (by simp [initValues, preserved]) (by taint_decide)
  have u := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb updateValues
    (by decide) (by simp [updateValues, Whole.valid]) (by simp [updateValues])
    (by simp [updateValues, preserved]) (by taint_decide)
  have f := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb finalizeValues
    (by decide) (by simp [finalizeValues, Whole.valid]) (by simp [finalizeValues])
    (by simp [finalizeValues, preserved]) (by taint_decide)
  have b := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb baseValues
    (by decide) (by simp [baseValues, Whole.valid]) (by simp [baseValues])
    (by simp [baseValues, preserved]) (by taint_decide)
  exact ((i.seq init_ct).seq ((u.seq (update_ct v hL)).seq (f.seq (finalize_ct v hL)))).seq
    (prune_ct.seq ((b.seq (base_ct hL)).seq (wipe_ct hL)))

theorem lay_eq {s t : State} (hp : pkLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2]

theorem publicKey_ct (v : Whole.Backend) : ConstantTime isa pkLocal.pre pkLocal.pub (code v.code v.suffix) := by
  refine Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok v (entry_ctx hs hp) (lay_ok hs) (entry_args hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr t.v q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args hqb
    exact ⟨(body_ct v (lay_ok hs) (entry_args hpa) hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs hpa, trivial⟩, ⟨hq, trivial⟩⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.AArch64.PublicKey
end

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

theorem publicKey_verified (v : Whole.Backend) :
    Verified AArch64.target (code v.code v.suffix) (Spec.Ed25519.publicKeyContract AArch64.abi 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => publicKey_ok v h) (publicKey_ct v) (.refl pk_implies.sat_left))
    pk_implies

end VG.Proof.Ed25519.AArch64.PublicKey
