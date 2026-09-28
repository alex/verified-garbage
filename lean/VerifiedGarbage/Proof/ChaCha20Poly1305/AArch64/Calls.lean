import VerifiedGarbage.Proof.Poly1305.AArch64.Shared
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64

/-!
# ChaCha20-Poly1305 on AArch64: the calls

Untrusted: everything here is checked by Lean. Each call of a verified
function, from its proof of `Verified` (with `WP.call`): what it needs of the
state it is called from, and what holds when it returns. A call stores
nothing in memory, so the callee changes memory only within the regions it
may write.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## Memory -/

theorem bytesAt_eq : Spec.ChaCha20.bytesAt = Spec.Poly1305.bytesAt := rfl

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem sub_off (p : Addr) {a n len : Nat} (h : a + n ≤ len) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, n⟩ ⟨p, len⟩ := by
  intro x hx
  simp only [Region.Contains] at *
  have : (x - p).toNat ≤ (x - (p + BitVec.ofNat 64 a)).toNat + a := by
    rw [show x - p = (x - (p + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by bv_omega,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    exact le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

/-- A Poly1305 state outside a frame is unchanged. -/
theorem Repr.frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr}
    (hd : ∀ r ∈ rs, (⟨P, 128⟩ : Region).Disjoint r) {key msg : List Byte} (h : Repr m P key msg) :
    Repr m' P key msg := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · rw [show (P + 24 : Addr) = P + BitVec.ofNat 64 24 from rfl,
      bytesAt_frame hf (n := 32) (fun r hr => (hd r hr).sub_left (sub_off P (a := 24) (by omega)))
      (by omega)]
    exact h2
  · rw [bytesAt_frame hf (n := 24) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega)))
      (by omega)]
    exact h3

/-- A ChaCha20 state outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p :=
  VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf hd

/-! ## What a call keeps -/

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are not callee-saved (or are `x30`). -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem Kept.trans {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : Kept rs s₁ s₂) (h₂ : Kept rs s₂ s₃) :
    Kept rs s₁ s₃ :=
  ⟨fun r hr h => by rw [h₂.cs r hr h, h₁.cs r hr h], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem Kept.sub {rs rs' : List Region} {s s' : State} (h : Kept rs s s')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : Kept rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.sub hs⟩

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ∉ linkRegs) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr _ h

theorem init_noFrames : Impl.Poly1305.AArch64.init.noFrames = true := by decide +kernel
theorem blocks_noFrames : Impl.Poly1305.AArch64.blocks.noFrames = true := by decide +kernel
theorem finalize_noFrames : Impl.Poly1305.AArch64.finalize.noFrames = true := by decide +kernel
theorem xor_noFrames : Impl.ChaCha20.AArch64.Xor.xor.noFrames = true := by decide +kernel

/-! ## `vg_poly1305_init` -/

theorem init_call {s : State} {P K : Addr} (hx0 : s.gpr .x0 = P) (hx1 : s.gpr .x1 = K)
    (hdj : (⟨P, 128⟩ : Region).Disjoint ⟨K, 32⟩)
    (hc : Covers ([⟨K, 32⟩] ++ [⟨P, 128⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨P, 128⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩] s s' → Repr s'.mem P (bytesAt s.mem K 32) [] → Q s') :
    WP isa (.call "vg_poly1305_init" Impl.Poly1305.AArch64.init) s Q := by
  refine WP.call (k := Proof.Poly1305.initAArch64) Proof.Poly1305.AArch64.init_verified.1
    (rd := [⟨K, 32⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_ init_noFrames
  · simp only [Proof.Poly1305.initAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), hx0, hx1]
    exact ⟨trivial, trivial, hdj⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.Poly1305.initAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), hx0, hx1] using hpost

/-! ## `vg_poly1305_blocks` -/

theorem blocks_call {s : State} {P p : Addr} {n : Nat} (hx0 : s.gpr .x0 = P) (hx1 : s.gpr .x1 = p)
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 n) (hn : 16 * n < 2 ^ 64)
    (hdj : (⟨P, 128⟩ : Region).Disjoint ⟨p, 16 * n⟩) (hwrap : p.toNat + 16 * n ≤ 2 ^ 64)
    (hc : Covers ([⟨p, 16 * n⟩] ++ [⟨P, 128⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨P, 128⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩] s s' →
      (∀ key msg, Repr s.mem P key msg → Repr s'.mem P key (msg ++ bytesAt s.mem p (16 * n))) → Q s') :
    WP isa (.call "vg_poly1305_blocks" Impl.Poly1305.AArch64.blocks) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine WP.call (k := Proof.Poly1305.blocksAArch64) Proof.Poly1305.AArch64.blocks_verified.1
    (rd := [⟨p, 16 * n⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_ blocks_noFrames
  · simp only [Proof.Poly1305.blocksAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.x2 ∉ linkRegs),
      hx0, hx1, hx2, hn']
    exact ⟨trivial, trivial, hdj, hwrap⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ fun key msg hr => ?_
    simp only [Proof.Poly1305.blocksAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.x2 ∉ linkRegs),
      hx0, hx1, hx2, hn'] at hpost
    exact hpost key msg hr

/-! ## `vg_poly1305_finalize` -/

theorem finalize_call {s : State} {P T O : Addr} {n : Nat} (hx0 : s.gpr .x0 = P) (hx1 : s.gpr .x1 = T)
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 n) (hx3 : s.gpr .x3 = O) (hn : n < 16)
    (hPT : (⟨P, 128⟩ : Region).Disjoint ⟨T, n⟩) (hPO : (⟨P, 128⟩ : Region).Disjoint ⟨O, 16⟩)
    (hTO : (⟨T, n⟩ : Region).Disjoint ⟨O, 16⟩)
    (hc : Covers ([⟨T, n⟩] ++ [⟨P, 128⟩, ⟨O, 16⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨P, 128⟩, ⟨O, 16⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩, ⟨O, 16⟩] s s' →
      (∀ key msg, Repr s.mem P key msg → bytesAt s'.mem O 16 = mac key (msg ++ bytesAt s.mem T n)) →
      Q s') :
    WP isa (.call "vg_poly1305_finalize" Impl.Poly1305.AArch64.finalize) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine WP.call (k := Proof.Poly1305.finalizeAArch64) Proof.Poly1305.AArch64.finalize_verified.1
    (rd := [⟨T, n⟩]) (wr := [⟨P, 128⟩, ⟨O, 16⟩]) ?_ hc hw ?_ finalize_noFrames
  · simp only [Proof.Poly1305.finalizeAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.x2 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x3 ∉ linkRegs), hx0, hx1, hx2, hx3, hn']
    exact ⟨trivial, trivial, hPT, hPO, hTO, hn⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ fun key msg hr => ?_
    simp only [Proof.Poly1305.finalizeAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.x2 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x3 ∉ linkRegs), hx0, hx1, hx2, hx3, hn'] at hpost
    exact hpost key msg hr

/-! ## `vg_chacha20_block` -/

theorem block_call {s : State} {S B : Addr} (hx0 : s.gpr .x0 = S) (hx1 : s.gpr .x1 = B)
    (hdj : (⟨B, 256⟩ : Region).Disjoint ⟨S, 64⟩)
    (hc : Covers ([⟨S, 64⟩] ++ [⟨B, 256⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨B, 256⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨B, 256⟩] s s' → stateAt s'.mem B = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.AArch64.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockAArch64) Proof.ChaCha20.AArch64.block_verified.1
    (rd := [⟨S, 64⟩]) (wr := [⟨B, 256⟩]) ?_ hc hw ?_ Proof.ChaCha20.AArch64.Xor.block_noFrames
  · simp only [Proof.ChaCha20.blockAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), hx0, hx1]
    exact ⟨trivial, trivial, hdj⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.ChaCha20.blockAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), hx0, hx1] using hpost

/-! ## `vg_chacha20_xor` -/

theorem xor_call {s : State} {S D B : Addr} {n : Nat} (hx0 : s.gpr .x0 = S) (hx1 : s.gpr .x1 = D)
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 n) (hx3 : s.gpr .x3 = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s s' →
      Spec.ChaCha20.bytesAt s'.mem D n =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem D n) (keystream (stateAt s.mem S) n) → Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.AArch64.Xor.xor) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  refine WP.call (k := Proof.ChaCha20.xorAArch64) Proof.ChaCha20.AArch64.Xor.xor_verified.1
    (rd := []) (wr := [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) ?_ hc hw ?_ xor_noFrames
  · simp only [Proof.ChaCha20.xorAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.x2 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x3 ∉ linkRegs), hx0, hx1, hx2, hx3, hn']
    exact ⟨trivial, trivial, hSD, hSB, hDB, hwrap⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.ChaCha20.xorAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.x2 ∉ linkRegs),
      hx0, hx1, hx2, hn'] using hpost

end VG.Proof.ChaCha20Poly1305.AArch64
