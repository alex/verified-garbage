import VerifiedGarbage.Proof.Scrypt.AArch64.BlockMixFun
import VerifiedGarbage.Proof.Scrypt.AArch64.Salsa

/-!
# scryptBlockMix on AArch64: verified

Untrusted: everything here is checked by Lean. `SalsaSpec` of the verified
Salsa20/8 Core, from its `Verified` proof by `WP.call`; then the `Verified`
proof of `vg_scrypt_blockmix`. Only the pointers and `r` are public, and the
taint analysis checks that nothing else reaches an address or a branch.
-/

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64

theorem salsa_noFrames : Impl.Scrypt.AArch64.salsa.noFrames = true := by decide +kernel

/-- A region inside one of `rs` is covered by `rs`. -/
theorem covers_of_in {rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) :
    Covers [⟨a, n⟩] rs := by
  obtain ⟨R, hR, hc⟩ := h
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨R, hR, (a - R.base).toNat, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega, hc⟩

theorem covers_pair {rs : List Region} {a b : Region} (ha : Covers [a] rs) (hb : Covers [b] rs) :
    Covers [a, b] rs := by
  intro x n ⟨r, hr, hc⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ha x n ⟨_, List.mem_singleton_self _, hc⟩
  · exact hb x n ⟨_, List.mem_singleton_self _, hc⟩

theorem salsaSpec : SalsaSpec Impl.Scrypt.AArch64.salsa := by
  intro s d sc hd hsc hds hind hins Q hQ
  have c0 : s.callEntry.gpr .x0 = d := (State.callEntry_gpr _ (by decide)).trans hd
  have c1 : s.callEntry.gpr .x1 = sc := (State.callEntry_gpr _ (by decide)).trans hsc
  have hw : Covers [⟨d, 64⟩, ⟨sc, 64⟩] s.wr := covers_pair (covers_of_in hind) (covers_of_in hins)
  refine WP.call (k := Proof.Scrypt.salsaAArch64) Proof.Scrypt.AArch64.salsa_verified.1
    (rd := []) (wr := [⟨d, 64⟩, ⟨sc, 64⟩]) ?_ ?_ hw ?_ salsa_noFrames
  · simp only [Proof.Scrypt.salsaAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, hds⟩
  · intro a n h
    obtain ⟨R, hR, hc⟩ := hw a n (by simpa using h)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.Scrypt.salsaAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0] at hpost
    exact hQ s' hrd hwr hsp hcs hf hpost

theorem main_fdepth : 16 * (Impl.Scrypt.AArch64.blockMixMain Impl.Scrypt.AArch64.salsa).fdepth + 16 < 2 ^ 64 := by
  decide +kernel

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Scrypt.blockMixAArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition (with no data). -/
def bmSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 0x2000 | .x3 => 1 | .x4 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 128⟩]

theorem blockMix_verified :
    Verified AArch64.target Impl.Scrypt.AArch64.blockMix Proof.Scrypt.blockMixAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ :=
      BlockMix.correct salsaSpec main_fdepth (pre_of hs).1 (pre_of hs).2
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)
  · refine ⟨bmSat, rfl, rfl, ?_, ?_, ?_, by decide, ?_, ?_, ?_, by decide, by decide, by decide,
      rfl, by decide⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, bmSat] at h₁ h₂
      bv_omega

end VG.Proof.Scrypt.AArch64.BlockMix
