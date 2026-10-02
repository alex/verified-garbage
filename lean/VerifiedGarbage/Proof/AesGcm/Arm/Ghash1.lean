import VerifiedGarbage.Proof.AesGcm.Arm.Blocks

/-!
# AES-GCM on ARMv7: GHASH over blocks of the state, `T` or the data

Untrusted: everything here is checked by Lean. `ghCall_ok` is the frame of a
call of `vg_ghash` from a state whose registers are its arguments (the hash
subkey at `ctx + 240`, the accumulator at `st + yo`, the working space at
`W + 512`), and `ghash1 yo b o` continues the accumulator over the block at
`P = b + o` (`ghash1_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- What a call of `vg_ghash` from `s` leaves in `s'`, for the accumulator
at `Y`, the working space at `W + 512` and the data `ds` (as blocks). -/
structure GhOut (s : State) (c w sp : BitVec 32) (Y : Addr) (ds : List Block) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  spk : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨Y, 16⟩, ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp] s.mem s'.mem
  out : blockAt s'.mem Y = ghashFrom (blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) (blockAt s.mem Y) ds

theorem GhOut.env {s s' : State} {c st w sp k7 k8 : BitVec 32} {Y : Addr} {ds : List Block}
    (h : GhOut s c w sp Y ds s') (he : Env c st w sp k7 k8 s) : Env c st w sp k7 k8 s' :=
  he.of_saved h.saved h.spk h.rd h.wr

theorem blocksAt_one (m : Mem) (p : Addr) : blocksAt m p 1 = [blockAt m p] := by
  simp [blocksAt]

/-- The call itself, from a state whose registers are its arguments, for
`n` blocks at the 32-bit pointer `P`. -/
theorem ghCall_ok {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : Env c st w sp k7 k8 s) {P : BitVec 32} {n : Nat}
    (h0 : s.gpr .r0 = c + BitVec.ofNat 32 240) (h1 : s.gpr .r1 = st + BitVec.ofNat 32 yo)
    (h2 : s.gpr .r2 = P) (h3 : s.gpr .r3 = BitVec.ofNat 32 n) (h12 : s.gpr .r12 = w + BitVec.ofNat 32 512)
    (hfit : P.toNat + 16 * n ≤ 2 ^ 32)
    (hpy : (⟨State.addr st + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨State.addr P, 16 * n⟩)
    (hpw : (⟨State.addr P, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below sp).Disjoint ⟨State.addr P, 16 * n⟩) (hpr : Covers [⟨State.addr P, 16 * n⟩] (s.rd ++ s.wr)) :
    WP isa ghFrame s (GhOut s c w sp (State.addr st + BitVec.ofNat 64 yo) (blocksAt s.mem (State.addr P) n)) := by
  have eH := L.cA (d := 240) (by decide)
  have eY := L.stA (d := yo) (by omega)
  have eS := L.wA (d := 512) (by decide)
  have hc : GhCall s (c + BitVec.ofNat 32 240) (st + BitVec.ofNat 32 yo) P (w + BitVec.ofNat 32 512) n := by
    have hk := he.sp
    refine ⟨h0, h1, h2, h3, h12, by rw [hk]; exact L.sp8, by rw [L.cN (by decide)]; have := L.cw; omega,
      by rw [L.stN (by omega)]; have := L.sw; omega, hfit, by rw [L.wN (by decide)]; have := L.ww; omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [eH, eY, eS, hk]
    · exact L.ctx_st (by decide) (by omega)
    · exact L.ctx_w (by decide) (by decide)
    · exact hpy
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact hpw
    · exact L.stk_ctx (by decide)
    · exact L.stk_st (by omega)
    · exact hpk
    · exact L.stk_w (by decide)
    · exact covers_cons (he.perm.ctxC (by decide)) hpr
    · exact covers_cons (he.perm.stC (by omega)) (he.perm.wC (by decide))
  refine WP.mono (gh_call hc) fun s' h => ⟨h.rd, h.wr, h.sp, h.saved, ?_, ?_⟩
  · have f := h.frame; rw [eY, eS, he.sp] at f; exact f
  · have o := h.out; rw [eH, eY] at o; exact o

/-- The arguments of `ghash1`. -/
theorem ghArgs_ok {c st w sp k7 k8 : BitVec 32} {s : State} (he : Env c st w sp k7 k8 s) (yo : Nat) (b : Reg) (o : Nat)
    (hb : b = .r10 ∨ b = .r11) (hyo : encodable (BitVec.ofNat 32 yo) = true)
    (ho : encodable (BitVec.ofNat 32 o) = true) :
    ∃ s', runBlock isa [addI .r0 .r9 240, addI .r1 .r10 yo, addI .r2 b o, .mov .r3 (imm 1),
        addI .r12 .r11 scrO] s = some s' ∧
      s'.gpr .r0 = c + BitVec.ofNat 32 240 ∧ s'.gpr .r1 = st + BitVec.ofNat 32 yo ∧
      s'.gpr .r2 = s.gpr b + BitVec.ofNat 32 o ∧ s'.gpr .r3 = BitVec.ofNat 32 1 ∧
      s'.gpr .r12 = w + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h9 := he.r9; have h10 := he.r10; have h11 := he.r11
  rcases hb with rfl | rfl
  all_goals
    refine ⟨_, by arun [hyo, ho], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h9]
    · simp [gpr_setReg, h10]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg, h11]
    · intro r a b c d e; simp [gpr_setReg, a, b, c, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩

/-- `ghash1 yo b o`, for the block at `P = b + o`. -/
theorem ghash1_ok {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : Env c st w sp k7 k8 s) (b : Reg) (o : Nat) (hb : b = .r10 ∨ b = .r11)
    (ho : encodable (BitVec.ofNat 32 o) = true) {P : BitVec 32}
    (hP : s.gpr b + BitVec.ofNat 32 o = P) (hfit : P.toNat + 16 ≤ 2 ^ 32)
    (hpy : (⟨State.addr st + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨State.addr P, 16⟩)
    (hpw : (⟨State.addr P, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below sp).Disjoint ⟨State.addr P, 16⟩) (hpr : Covers [⟨State.addr P, 16⟩] (s.rd ++ s.wr)) :
    WP isa (ghash1 yo b o) s (GhOut s c w sp (State.addr st + BitVec.ofNat 64 yo) [blockAt s.mem (State.addr P)]) := by
  obtain ⟨s₁, run₁, h0, h1, h2, h3, h12, hkeep, hk⟩ := ghArgs_ok he yo b o hb
    (by rcases hyo with rfl | rfl <;> decide) ho
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide))
    hk.sp hk.rd hk.wr
  refine WP.mono (ghCall_ok L hyo he₁ (P := P) (n := 1) h0 h1 (by rw [h2, hP]) h3 h12 (by omega)
    (by simpa using hpy) (by simpa using hpw) (by simpa using hpk)
    (by rw [hk.rd, hk.wr]; simpa using hpr)) fun s' h => ?_
  exact ⟨h.rd.trans hk.rd, h.wr.trans hk.wr, h.spk.trans hk.sp,
    fun r hr hl => by
      rw [h.saved r hr hl]
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl hl | exact hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide),
    hk.mem ▸ h.frame, by rw [h.out, blocksAt_one, hk.mem]⟩

end VG.Proof.AesGcm.Arm
