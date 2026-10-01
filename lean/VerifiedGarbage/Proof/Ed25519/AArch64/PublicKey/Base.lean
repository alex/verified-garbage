import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Layout
import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Prune
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (callWith)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem base_noFrames : Impl.Ed25519.AArch64.scalarBase.noFrames = true := by lit_decide

def BaseArgs (L : Lay) (t : State) : Prop :=
  t.gpr .x0 = L.out ∧ t.gpr .x1 = L.E + 32 ∧ t.gpr .x2 = L.scr

theorem base_pre (hL : L.Ok) (ha : BaseArgs L t) :
    scalarBaseLocal.pre (t.callEntry.withRegions [⟨L.E + 32, 32⟩] L.outputs) := by
  obtain ⟨h0, h1, h2⟩ := ha
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2]
  exact ⟨True.intro, rfl, hL.kc.sub_left (Offset.sub_base _ (by decide : 32 + 32 ≤ 336)), hL.nc⟩

theorem base_covers (L : Lay) : Covers ([⟨L.E + 32, 32⟩] ++ L.outputs)
    (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact ⟨Whole.FR L.E, List.mem_append_right _ List.mem_cons_self, 32, rfl, by change 32 + 32 ≤ 256; decide⟩
  · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), 0, by simp⟩

theorem base_writes (L : Lay) : ∀ r ∈ L.outputs,
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  fun r hr => .inr ⟨r, hr, 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_call (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : BaseArgs L t) :
    WP isa (.call "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Ed25519.bytesAt u.mem L.out 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (L.E + 32) 32) := by
  refine Whole.call_ok hc scalarBase_ok base_noFrames (base_pre hL ha) (base_covers L)
    (base_writes L) fun u hu _ hp => ⟨hu, ?_⟩
  change Spec.Ed25519.bytesAt u.mem (t.callEntry.gpr .x0) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (t.callEntry.gpr .x1) 32) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), ha.1, ha.2.1] at hp
  exact hp

theorem prune_step (hc : Ctx L g vec m₀ t) {digest : List Byte}
    (hh : Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 = digest) :
    WP isa (.block prune) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (L.E + 32) 32) = Spec.Ed25519.prune digest := by
  have hwrite : (⟨t.sp, 256⟩ : Region) ∈ t.wr := by rw [hc.sp, hc.wr]; exact List.mem_cons_self
  have hash : Spec.Sha512.bytesAt t.mem (t.sp + 192) 64 = digest := by rw [hc.sp]; exact hh
  refine WP.mono (prune_ok hwrite hash) fun u ⟨hu, hf, hp⟩ => ⟨?_, ?_⟩
  · refine hc.of_frame hu.rd hu.wr hu.sp ?_ ?_ hf ?_
    · intro r hr _
      apply hu.regs r <;> intro h <;> subst r <;> simp [preserved] at hr
    · intro r _; rw [hu.v]
    · rintro r hr
      rw [List.mem_singleton.mp hr, hc.sp]
      exact .inl (Offset.sub_base _ (by decide : 32 + 32 ≤ 256))
  · rw [hc.sp] at hp
    exact hp

theorem base_step (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) {n : Nat}
    (hs : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (L.E + 32) 32) = n) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Ed25519.bytesAt u.mem L.out 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul n Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.x0, .caller 0 0), (.x1, .frame 32), (.x2, .caller 2 0)])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])) fun u ⟨hu, hm, hav⟩ => ?_)
  have h0 := hav (.x0, .caller 0 0) (by simp)
  have h1 := hav (.x1, .frame 32) (by simp)
  have h2 := hav (.x2, .caller 2 0) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  refine WP.mono (base_call hu hL ⟨h0, h1, h2⟩) fun u' ⟨hu', hp⟩ => ⟨hu', ?_⟩
  rw [hp, hm, Spec.Ed25519.scalarBase, hs]

theorem wipe_step (hc : Ctx L g vec m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed25519.bytesAt u.mem L.out 32 = Spec.Ed25519.bytesAt t.mem L.out 32 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 4) (count := 28) (by decide)) fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes (R := L.OUT) ?_
    (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 8 * 4 + 8 * 28 ≤ 336))).symm

end VG.Proof.Ed25519.AArch64.PublicKey
