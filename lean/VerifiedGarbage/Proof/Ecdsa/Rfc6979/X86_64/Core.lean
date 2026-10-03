import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Blocks
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Bytes

/-!
# Deterministic ECDSA on x86-64: signing with a candidate

The call of `vg_ecdsa_p256_sign` with `k = V` from the frame (`core_ok`):
it returns 1 and writes the signature, or returns 0 and writes zeros, as
`Spec.Ecdsa.signWith` gives for `d`, the digest and `V`, and changes only
`out`, `scratch` and its return address.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

variable {v : Compress} {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

theorem core_nosp : NoSp Impl.Ecdsa.X86_64.signP256 :=
  Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide)

theorem core_depth : Impl.Ecdsa.X86_64.signP256.depth = 0 := by lit_decide

/-- The signature `core` computes, or none. -/
abbrev coreSig (L : Lay) (m : Mem) : Option (Nat × Nat) :=
  Proof.Ecdsa.X86_64.sig m L.d L.dg (L.B + BitVec.ofNat 64 56)

abbrev coreRd (L : Lay) : List Region := [L.D, L.DG, ⟨L.B + BitVec.ofNat 64 56, 32⟩]
abbrev coreWr (L : Lay) : List Region := [L.OUT, L.SCR]

theorem ce_gpr (t : State) (rd wr : List Region) {r : Reg} (h : r ≠ .rsp) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- The return address of a call from the frame. -/
theorem Ctx.ret {t : State} (hc : Ctx L g m₀ t) :
    (⟨t.callEntry.gpr .rsp, 8⟩ : Region) = ⟨L.B + BitVec.ofNat 64 16, 8⟩ := by
  rw [State.callEntry_rsp, hc.rsp]
  congr 1
  bv_omega

/-- Bytes the return address misses, on entry to a call. -/
theorem ce_bytesAt {t : State} (hc : Ctx L g m₀ t) {p : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨p, n⟩ ⟨L.B + BitVec.ofNat 64 16, 8⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt t.callEntry.mem p n = Spec.Sha256.bytesAt t.mem p n := by
  refine bytesAt_frame (ws := [below (t.gpr .rsp) 8]) ?_ (fun r hr => ?_) hn
  · exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega))
  · simp only [List.mem_singleton] at hr; subst hr
    rw [hc.rsp]
    refine hd.sub_right fun a ha => ?_
    have e : L.B + BitVec.ofNat 64 24 - BitVec.ofNat 64 8 = L.B + BitVec.ofNat 64 16 := by bv_omega
    simpa [below, e] using ha

theorem core_pre (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.out) (hsi : t.gpr .rsi = L.d)
    (hdx : t.gpr .rdx = L.dg) (hcx : t.gpr .rcx = L.B + BitVec.ofNat 64 56) (h8 : t.gpr .r8 = L.scr) :
    Proof.Ecdsa.X86_64.signX86_64.pre (t.callEntry.withRegions (coreRd L) (coreWr L)) := by
  have hret := hc.ret
  simp only [Proof.Ecdsa.X86_64.signX86_64, ce_gpr _ _ _ (by decide : Reg.rdi ≠ .rsp),
    ce_gpr _ _ _ (by decide : Reg.rsi ≠ .rsp), ce_gpr _ _ _ (by decide : Reg.rdx ≠ .rsp),
    ce_gpr _ _ _ (by decide : Reg.rcx ≠ .rsp), ce_gpr _ _ _ (by decide : Reg.r8 ≠ .rsp), hdi, hsi, hdx, hcx, h8,
    State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr]
  rw [hret]
  exact ⟨by triv, by triv, hL.oc, hL.od, hL.og, (hL.stk_OUT (by omega)).symm, hL.dc, hL.gc, hL.stk_SCR (by omega),
    hL.stk_OUT (by omega), hL.stk_SCR (by omega), hL.no, hL.nc⟩

theorem core_covers {t : State} (hc : Ctx L g m₀ t) : Covers (coreRd L ++ coreWr L) (t.rd ++ t.wr) :=
  hc.covers fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.D, by simp, within_base _ (by omega)⟩
    · exact ⟨L.DG, by simp, within_base _ (by omega)⟩
    · exact ⟨L.FR, by simp, within_fr _ (by omega) (by omega)⟩
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

theorem core_coversW {t : State} (hc : Ctx L g m₀ t) : Covers (coreWr L) t.wr :=
  hc.coversW fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

/-- `core(out, d, digest, V, scratch)`. -/
theorem core_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.out)
    (hsi : t.gpr .rsi = L.d) (hdx : t.gpr .rdx = L.dg) (hcx : t.gpr .rcx = L.B + BitVec.ofNat 64 56)
    (h8 : t.gpr .r8 = L.scr) :
    WP isa (.call (cfgOf v).coreN (cfgOf v).coreC) t fun t' => Ctx L g m₀ t' ∧
      Frame [L.OUT, L.SCR, ⟨L.B + BitVec.ofNat 64 16, 8⟩] t.mem t'.mem ∧
      match coreSig L t.mem with
      | some rs => (t'.gpr .rax).setWidth 32 = 1 ∧
          Spec.Sha256.bytesAt t'.mem L.out 64 = Spec.Ecdsa.encode Spec.P256.curve rs
      | none => (t'.gpr .rax).setWidth 32 = 0 ∧ Spec.Sha256.bytesAt t'.mem L.out 64 = List.replicate 64 0 := by
  have hsp : below (t.gpr .rsp) (8 * (Impl.Ecdsa.X86_64.signP256.depth + 1)) = ⟨L.B + BitVec.ofNat 64 16, 8⟩ := by
    rw [core_depth, hc.rsp]
    show (⟨L.B + BitVec.ofNat 64 24 - BitVec.ofNat 64 8, 8⟩ : Region) = _
    congr 1; bv_omega
  refine WP.call (k := Proof.Ecdsa.X86_64.signX86_64) Proof.Ecdsa.X86_64.sign_x86 core_nosp
    (by rw [core_depth]; decide) (core_pre hL hc hdi hsi hdx hcx h8)
    (core_covers hc) (core_coversW hc) fun t' hrd hwr hcs hf _ ⟨s₂, hm, hg₂, hpost⟩ => ?_
  rw [hsp] at hf
  refine ⟨hc.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf fun r hr => ?_, hf, ?_⟩
  · simp only [coreWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (sub_refl _)
    · exact .inr (.inl (sub_refl _))
    · exact safe_low L (by omega)
  · have hk : Proof.Ecdsa.X86_64.sig t.callEntry.mem L.d L.dg (L.B + BitVec.ofNat 64 56) = coreSig L t.mem := by
      simp only [Proof.Ecdsa.X86_64.sig, coreSig, ecdsa_bytesAt]
      rw [ce_bytesAt hc (hL.stk_D (d := 16) (n := 8) (by omega)).symm (by omega),
        ce_bytesAt hc (hL.stk_DG (d := 16) (n := 8) (by omega)).symm (by omega),
        ce_bytesAt hc (Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
    have hp := hpost
    simp only [Proof.Ecdsa.X86_64.signX86_64, ce_gpr _ _ _ (by decide : Reg.rdi ≠ .rsp),
      ce_gpr _ _ _ (by decide : Reg.rsi ≠ .rsp), ce_gpr _ _ _ (by decide : Reg.rdx ≠ .rsp),
      ce_gpr _ _ _ (by decide : Reg.rcx ≠ .rsp), hdi, hsi, hdx, hcx, State.withRegions_mem, hk, hm,
      hg₂ .rax (by decide)] at hp
    exact hp

end VG.Proof.Ecdsa.Rfc6979.X86_64
