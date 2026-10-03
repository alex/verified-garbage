import VerifiedGarbage.Proof.ChaCha20.AArch64.Stream.Bytes
import VerifiedGarbage.Proof.ChaCha20.AArch64.XorVariant

/-!
# Streaming ChaCha20 on AArch64: the calls

Untrusted: everything here is checked by Lean. The calls of
`vg_chacha20_block` and of an implementation of `vg_chacha20_xor`, from their
proofs of correctness (with `WP.call`), as ChaCha20-Poly1305 makes them. A
call stores nothing in memory, so the callee changes memory only within the
regions it may write.
-/

namespace VG.Proof.ChaCha20.AArch64.Stream

open VG VG.AArch64
open VG.Spec.ChaCha20 (stateAt keystream bytesAt)

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are not callee-saved (or are `x30`). -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem
  vec : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ∉ linkRegs) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr _ h

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem block_call {s : State} {S B : Addr} (hx0 : s.gpr .x0 = S) (hx1 : s.gpr .x1 = B)
    (hdj : (⟨B, 256⟩ : Region).Disjoint ⟨S, 64⟩)
    (hc : Covers ([⟨S, 64⟩] ++ [⟨B, 256⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨B, 256⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨B, 256⟩] s s' → stateAt s'.mem B = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.AArch64.block) s Q := by
  refine WP.callV (k := Proof.ChaCha20.blockAArch64) Proof.ChaCha20.AArch64.block_correct
    (rd := [⟨S, 64⟩]) (wr := [⟨B, 256⟩]) ?_ hc hw ?_ (by lit_decide)
  · simp only [Proof.ChaCha20.blockAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), hx0, hx1]
    exact ⟨trivial, trivial, hdj⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ ?_
    simpa only [Proof.ChaCha20.blockAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), hx0, hx1] using hpost

theorem xor_call (v : Proof.ChaCha20.AArch64.XorImpl) {s : State} {S D B : Addr} {n : Nat}
    (hx0 : s.gpr .x0 = S) (hx1 : s.gpr .x1 = D)
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 n) (hx3 : s.gpr .x3 = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s s' →
      bytesAt s'.mem D n = List.zipWith (· ^^^ ·) (bytesAt s.mem D n) (keystream (stateAt s.mem S) n) →
      Q s') :
    WP isa (.call v.callee.name v.callee.code) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  refine WP.callV (k := Proof.ChaCha20.xorAArch64) v.ok
    (rd := []) (wr := [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) ?_ hc hw ?_ v.noFrames
  · simp only [Proof.ChaCha20.xorAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.x2 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x3 ∉ linkRegs), hx0, hx1, hx2, hx3, hn']
    exact ⟨trivial, trivial, hSD, hSB, hDB, hwrap⟩
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ ?_
    simpa only [Proof.ChaCha20.xorAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.x2 ∉ linkRegs),
      hx0, hx1, hx2, hn'] using hpost

end VG.Proof.ChaCha20.AArch64.Stream
