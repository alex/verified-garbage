import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Layout
import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Prune
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wipe

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey
open VG.Impl.Ed25519.Arm.Whole (callWith)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem base_noFrames : Impl.Ed25519.Arm.scalarBase.noFrames = true := by lit_decide

def BaseArgs (L : Lay) (t : State) : Prop :=
  t.gpr .r0 = L.out ∧ t.gpr .r1 = L.E + 24 ∧ t.gpr .r2 = L.scr

theorem scalar_addr (hL : L.Ok) : State.addr (L.E + 24) = State.addr L.E + 24 :=
  addr_add (k := 24) (by have := hL.top; omega)

theorem base_pre (hL : L.Ok) (ha : BaseArgs L t) :
    scalarBaseLocal.pre (t.callEntry.withRegions [⟨State.addr L.E + 24, 32⟩] L.outputs) := by
  obtain ⟨h0, h1, h2⟩ := ha
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), h0, h1, h2, scalar_addr hL]
  refine ⟨True.intro, rfl, (hL.ko.sub_left (Offset.sub_base _ (by decide : 24 + 32 ≤ 280))).symm,
    hL.oc, hL.kc.sub_left (Offset.sub_base _ (by decide : 24 + 32 ≤ 280)), hL.no, ?_, hL.nc⟩
  have h := hL.top
  rw [BitVec.toNat_add_of_lt (by change L.E.toNat + 24 < 2 ^ 32; omega)]
  change L.E.toNat + 24 + 32 ≤ 2 ^ 32
  omega

theorem base_covers (L : Lay) : Covers ([⟨State.addr L.E + 24, 32⟩] ++ L.outputs)
    (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact ⟨Whole.FR L.E, List.mem_append_right _ List.mem_cons_self, 24, rfl, by change 24 + 32 ≤ 248; decide⟩
  · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), 0, by simp⟩

theorem base_writes (L : Lay) : ∀ r ∈ L.outputs,
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  fun r hr => .inr ⟨r, hr, 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_call (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : BaseArgs L t) :
    WP isa (.call "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase) t fun u =>
      Ctx L g m₀ u ∧ Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32) := by
  refine Whole.call_ok hc scalarBase_ok base_noFrames (base_pre hL ha) (base_covers L)
    (base_writes L) fun u hu _ hp => ⟨hu, ?_⟩
  change Spec.Ed25519.bytesAt u.mem (State.addr (t.callEntry.gpr .r0)) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem (State.addr (t.callEntry.gpr .r1)) 32) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), ha.1, ha.2.1, scalar_addr hL] at hp
  exact hp

theorem prune_step (hc : Ctx L g m₀ t) (hL : L.Ok) {digest : List Byte}
    (hh : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 184) 64 = digest) :
    WP isa (.block prune) t fun u => Ctx L g m₀ u ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32) = Spec.Ed25519.prune digest := by
  have hwrite : (⟨State.addr L.E, 248⟩ : Region) ∈ t.wr := by rw [hc.wr]; exact List.mem_cons_self
  refine WP.mono (prune_ok hc.sp (by have := hL.top; omega) hwrite hh) fun u ⟨hu, hf, hp⟩ => ⟨?_, hp⟩
  refine hc.of_frame hu.rd hu.wr hu.sp ?_ hf ?_
  · intro r hr _
    apply hu.regs r <;> intro h <;> subst r <;> simp [preserved] at hr
  · rintro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by decide : 24 + 32 ≤ 248))

theorem base_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) {n : Nat}
    (hs : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32) = n) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase) t fun u =>
      Ctx L g m₀ u ∧ Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul n Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.r0, .caller 0 0), (.r1, .frame 24), (.r2, .caller 2 0)]) (stk := [])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])
    (by decide) (by simp) (by simp)) fun u ⟨hu, hm, hav, _⟩ => ?_)
  have h0 := hav (.r0, .caller 0 0) (by simp)
  have h1 := hav (.r1, .frame 24) (by simp)
  have h2 := hav (.r2, .caller 2 0) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  have he : Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32 =
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => hm.bytes (R := ⟨State.addr L.E + 24, 32⟩) ?_
      (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint_base _ (by decide) (by decide)
  refine WP.mono (base_call hu hL ⟨h0, h1, h2⟩) fun u' ⟨hu', hp⟩ => ⟨hu', ?_⟩
  rw [hp, he, Spec.Ed25519.scalarBase, hs]

theorem wipe_step (hc : Ctx L g m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => Ctx L g m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 = Spec.Ed25519.bytesAt t.mem (State.addr L.out) 32 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (by have := hL.top; omega) (start := 6) (count := 56) (by decide))
    fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes (R := L.OUT) ?_
    (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 4 * 6 + 4 * 56 ≤ 280))).symm

end VG.Proof.Ed25519.Arm.PublicKey
