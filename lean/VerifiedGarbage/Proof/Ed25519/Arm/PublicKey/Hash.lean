import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Layout
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.HashPre

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey
open VG.Impl.Ed25519.Arm.Whole (callWith)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem setup_repr (hL : L.Ok) {u : State} (hf : Frame [⟨State.addr L.E, 24⟩] t.mem u.mem)
    {msg : List Byte} (hh : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr) msg) :
    Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (State.addr L.scr) msg := by
  refine Proof.Sha512.Stream.repr_congr (mem := t.mem) ?_ hh
  intro i hi
  refine hf.bytes (R := Whole.SHA L.scr) ?_ (by change 192 ≤ 2 ^ 64; decide) hi
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact ((hL.kc.sub_left (Region.sub_prefix (by decide : 24 ≤ 280))).sub_right (Whole.sha_sub L.scr)).symm

theorem init_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith initArgs Spec.Sha512.init512Api.name (Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512)) t
      fun u => Ctx L g m₀ u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (State.addr L.scr) [] := by
  refine WP.seq (WP.mono (setup_ok hc hL ha (args := [(.r0, .caller 2 0)]) (stk := [])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])
    (by decide) (by simp) (by simp)) fun u ⟨hu, _, hs, _⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact WP.mono (Whole.init_call hu (Whole.init_pre h0 hL.nc) (Whole.covers_writes hw) hw h0)
    fun v ⟨hv, _, hh⟩ => ⟨hv, hh⟩

theorem update_covers (L : Lay) : Covers (Whole.updateRd L.E L.seed 32 ++ Whole.hashWr L.scr)
    (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨L.SEED, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, by change 0 + (32#32).toNat ≤ 32; decide⟩
  · exact ⟨L.FR, by simp, 0, (BitVec.add_zero _).symm, by change 0 + 12 ≤ 248; decide⟩
  · exact ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0 + 192 ≤ 8192; decide⟩
  · exact ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192 + 272 ≤ 8192; decide⟩

theorem update_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hh : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr) []) :
    WP isa (callWith updateArgs Spec.Sha512.updateApi.name Impl.Sha512.Arm.Stream.update) t fun u =>
      Ctx L g m₀ u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (State.addr L.scr)
        (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.r0, .caller 2 0), (.r2, .const 0), (.r3, .const 0)])
    (stk := [.caller 1 0, .const 32, .caller 2 192])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])
    (by decide) (by simp [Whole.valid]) (by simp)) fun u ⟨hu, hm, hs, st⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp)
  have h2 := hs (.r2, .const 0) (by simp)
  have h3 := hs (.r3, .const 0) (by simp)
  have a0 := st 0 (by decide)
  have a1 := st 1 (by decide)
  have a2 := st 2 (by decide)
  simp only [argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 h2 h3 a0 a1 a2
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  have hp := Whole.update_pre hu.sp h0 a0 a1 a2 hL.sc
    (hL.kc.sub_left (Region.sub_prefix (by decide : 12 ≤ 280))) hL.nc hL.ns
    (by have := hL.top; omega)
  have count : Proof.Sha512.countArm u = BitVec.ofNat 64 ([] : List Byte).length := by
    rw [Proof.Sha512.countArm, h2, h3]
    rfl
  refine WP.mono (Whole.update_call hu hp (update_covers L) hw h0 a0 a1 count (setup_repr hL hm hh))
    fun u' ⟨hu', _, hr⟩ => ⟨hu', ?_⟩
  change Spec.Sha512.Repr _ u'.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (State.addr L.seed) 32) at hr
  rw [List.nil_append, hu.seed_bytes hL] at hr
  exact hr

theorem digest_addr (hL : L.Ok) : State.addr (L.E + 184) = State.addr L.E + 184 :=
  addr_add (k := 184) (by have := hL.top; omega)

theorem finalize_writes (hL : L.Ok) : ∀ r ∈ Whole.finalizeWr L.scr (L.E + 184),
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0 + 192 ≤ 8192; decide⟩
  · exact .inl ⟨184, digest_addr hL, by change 184 + 64 ≤ 248; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192 + 272 ≤ 8192; decide⟩

theorem finalize_covers (hL : L.Ok) :
    Covers (Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 184))
      (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  intro a n ⟨r, hr, hh⟩
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr] at hh
    exact ⟨L.FR, List.mem_append_right _ List.mem_cons_self, by
      change (a - State.addr L.E).toNat + n ≤ 248
      change (a - State.addr L.E).toNat + n ≤ 8 at hh
      omega⟩
  · exact Whole.covers_writes (finalize_writes hL) a n ⟨r, hr, hh⟩

theorem finalize_step (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hh : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr L.scr)
      (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32)) :
    WP isa (callWith finalizeArgs Spec.Sha512.finalizeApi.name Impl.Sha512.Arm.Stream.finalize) t fun u =>
      Ctx L g m₀ u ∧ Spec.Ed25519.bytesAt u.mem (State.addr L.E + 184) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.r0, .caller 2 0), (.r2, .const 32), (.r3, .const 0)])
    (stk := [.frame 184, .caller 2 192])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])
    (by decide) (by simp [Whole.valid]) (by simp)) fun u ⟨hu, hm, hs, st⟩ => ?_)
  have h0 := hs (.r0, .caller 2 0) (by simp)
  have h2 := hs (.r2, .const 32) (by simp)
  have h3 := hs (.r3, .const 0) (by simp)
  have a0 := st 0 (by decide)
  have a1 := st 1 (by decide)
  simp only [argValue, Lay.value, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 h2 h3 a0 a1
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
  have hp := Whole.finalize_pre hu.sp h0 a0 a1 hd
    (hL.kc.sub_left (Region.sub_prefix (by decide : 8 ≤ 280))) ds hL.nc nf
    (by have := hL.top; omega)
  have hl : (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  have count : Proof.Sha512.countArm u = BitVec.ofNat 64 (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32).length := by
    rw [hl, Proof.Sha512.countArm, h2, h3]
    rfl
  refine WP.mono (Whole.finalize_call hu hp (finalize_covers hL) (finalize_writes hL) h0 a0 count
    (setup_repr hL hm hh) (by rw [hl]; decide)) fun u' ⟨hu', _, hd⟩ => ⟨hu', ?_⟩
  rw [addr_add (k := 184) (by have := hL.top; omega)] at hd
  exact hd

theorem hash_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hash t fun u => Ctx L g m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.E + 184) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32) := by
  exact WP.seq (WP.mono (init_step hc hL ha) fun t₁ ⟨h₁, hh₁⟩ =>
    WP.seq (WP.mono (update_step h₁ hL ha hh₁) fun t₂ ⟨h₂, hh₂⟩ => finalize_step h₂ hL ha hh₂))

end VG.Proof.Ed25519.Arm.PublicKey
