import VerifiedGarbage.Proof.Aes.AArch64.Variant
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.AArch64.RelCT

/-!
# AES-CMAC on AArch64: calling `vg_aes_ctr32` on one block

`ctr_call`: a call of any implementation of `vg_aes_ctr32` with the counter
block `C`, one data block `D` holding zeros, and working space `S`, from its
contract (with `WP.call`): `D` then holds `CIPH_K(C)`, as bytes
(`Cmac.aesWith`), and only `C`, `D` and `S` change in memory.
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

theorem ofBytes_zeros : Spec.Gcm.ofBytes (Spec.Cmac.zeros 16) = 0 := by decide

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

theorem one_toNat : (1 : BitVec 64).toNat = 1 := rfl

/-- What a call of `vg_aes_ctr32` on one block needs. -/
structure CallPre (s : State) (W C D S : Addr) (R : Nat) : Prop where
  x0 : s.gpr .x0 = W
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = C
  x3 : s.gpr .x3 = D
  x4 : s.gpr .x4 = 1
  x5 : s.gpr .x5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wc : (⟨W, 240⟩ : Region).Disjoint ⟨C, 16⟩
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 16⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  wrap : D.toNat + 16 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩] s.wr
  zero : Spec.Aes.bytesAt s.mem D 16 = Spec.Cmac.zeros 16

/-- What a call of `vg_aes_ctr32` on one block leaves. -/
structure CallPost (s : State) (W C D S : Addr) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem D 16 =
    Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem W (16 * (R + 1))) (Spec.Aes.bytesAt s.mem C 16)

theorem callEntry_x0 (s : State) : s.callEntry.gpr .x0 = s.gpr .x0 := s.callEntry_gpr (by decide)
theorem callEntry_x1 (s : State) : s.callEntry.gpr .x1 = s.gpr .x1 := s.callEntry_gpr (by decide)
theorem callEntry_x2 (s : State) : s.callEntry.gpr .x2 = s.gpr .x2 := s.callEntry_gpr (by decide)
theorem callEntry_x3 (s : State) : s.callEntry.gpr .x3 = s.gpr .x3 := s.callEntry_gpr (by decide)
theorem callEntry_x4 (s : State) : s.callEntry.gpr .x4 = s.gpr .x4 := s.callEntry_gpr (by decide)
theorem callEntry_x5 (s : State) : s.callEntry.gpr .x5 = s.gpr .x5 := s.callEntry_gpr (by decide)

/-- `vg_aes_ctr32`'s precondition, on entry to a call with the regions it is given. -/
theorem CallPre.ctr_pre {s : State} {W C D S : Addr} {R : Nat} (h : CallPre s W C D S R) :
    Proof.Aes.ctr32AArch64.pre
      (s.callEntry.withRegions [⟨W, 240⟩] [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [Proof.Aes.ctr32AArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4,
    callEntry_x5, h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, hR, one_toNat, Nat.mul_one]
  exact ⟨trivial, trivial, h.wc, by simpa using h.wd, h.ws, by simpa using h.cd, h.cs,
    by simpa using h.ds, by simpa using h.wrap, h.rounds⟩

theorem ctr_call (v : Ctr32Impl) {s : State} {W C D S : Addr} {R : Nat} (h : CallPre s W C D S R) :
    WP isa (.call v.callee.name v.callee.code) s (CallPost s W C D S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := Proof.Aes.ctr32AArch64) v.ok (rd := [⟨W, 240⟩])
    (wr := [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩]) h.ctr_pre h.reads h.writes ?_ v.noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  obtain ⟨hdata, -⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, callEntry_x0,
    callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, h.x0, h.x1, h.x2, h.x3, h.x4, hR,
    one_toNat] at hdata
  have one : ∀ m : Mem, Spec.Gcm.blocksAt m D 1 = [Spec.Gcm.blockAt m D] := fun m => by
    simp [Spec.Gcm.blocksAt]
  have bD : Spec.Gcm.blockAt s.mem D = 0 := by rw [Spec.Gcm.blockAt, h.zero, ofBytes_zeros]
  rw [one, one, bD, Proof.Cmac.ctr32_one, List.cons.injEq] at hdata
  rw [Proof.Cmac.bytesAt_blockAt, hdata.1, Spec.Gcm.blockAt,
    Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _)]

/-- Calls of `vg_aes_ctr32` on one block, with the same arguments in both
runs, are constant time. -/
theorem ctr_rel (v : Ctr32Impl) {W C D S : Addr} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → CallPre s₁ W C D S R ∧ CallPre s₂ W C D S R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call v.callee.name v.callee.code) fun _ _ => True := by
  refine RelCT.call v.ok v.ct [⟨W, 240⟩] [⟨C, 16⟩, ⟨D, 16⟩, ⟨S, 2048⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.ctr_pre, h₂.ctr_pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.ctr32AArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₁.x5, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, h₂.x5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacAes.AArch64
