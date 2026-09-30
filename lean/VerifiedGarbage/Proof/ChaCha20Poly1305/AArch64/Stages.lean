import VerifiedGarbage.Proof.Poly1305.AArch64.Init
import VerifiedGarbage.Proof.Poly1305.AArch64.Blocks
import VerifiedGarbage.Proof.Poly1305.AArch64.Finalize
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Spec.ChaCha20Poly1305
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega

section

/-!
# ChaCha20-Poly1305 on AArch64: the calls

Untrusted: everything here is checked by Lean. Each call of a verified
function, from its proof of `Verified` (with `WP.call`): what it needs of the
state it is called from, and what holds when it returns. A call stores
nothing in memory, so the callee changes memory only within the regions it
may write.
-/

open VG.PowLit

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
    Region.Sub ⟨p + BitVec.ofNat 64 a, n⟩ ⟨p, len⟩ := Offset.sub_base p h

/-- A Poly1305 state outside a frame is unchanged. -/
theorem Repr.frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr}
    (hd : ∀ r ∈ rs, (⟨P, 128⟩ : Region).Disjoint r) {key msg : List Byte} (h : Repr m P key msg) :
    Repr m' P key msg := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · rw [show (P + 24 : Addr) = P + BitVec.ofNat 64 24 from rfl,
      bytesAt_frame hf (n := 32) (fun r hr => (hd r hr).sub_left (sub_off P (a := 24) (by lit_omega)))
      (by lit_omega)]
    exact h2
  · rw [bytesAt_frame hf (n := 24) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by lit_omega)))
      (by lit_omega)]
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
  refine WP.call (k := Proof.Poly1305.initAArch64) Proof.Poly1305.AArch64.init_ok
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
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by lit_omega)
  refine WP.call (k := Proof.Poly1305.blocksAArch64) Proof.Poly1305.AArch64.blocks_ok
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

/-- With `count = 0`: the message is whole blocks, so nothing is buffered.
The per-target contract does not use `scratch` (`x3`). -/
theorem finalize_call {s : State} {P O : Addr} (hx0 : s.gpr .x0 = P) (hx1 : s.gpr .x1 = 0)
    (hx2 : s.gpr .x2 = O) (hPO : (⟨P, 128⟩ : Region).Disjoint ⟨O, 16⟩)
    (hc : Covers ([] ++ [⟨P, 128⟩, ⟨O, 16⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨P, 128⟩, ⟨O, 16⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩, ⟨O, 16⟩] s s' →
      (∀ key msg, Repr s.mem P key msg → bytesAt s'.mem O 16 = mac key msg) → Q s') :
    WP isa (.call "vg_poly1305_finalize" Impl.Poly1305.AArch64.finalize) s Q := by
  refine WP.call (k := Proof.Poly1305.finalizeAArch64) Proof.Poly1305.AArch64.finalize_ok
    (rd := []) (wr := [⟨P, 128⟩, ⟨O, 16⟩]) ?_ hc hw ?_ finalize_noFrames
  · simp only [Proof.Poly1305.finalizeAArch64, State.withRegions_gpr, State.withRegions_wr,
      callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.x2 ∉ linkRegs),
      hx0, hx2]
    exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self, hPO⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ fun key msg hr => ?_
    simp only [Proof.Poly1305.finalizeAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, callEntry_gpr' s (by decide : Reg.x0 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.x1 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.x2 ∉ linkRegs),
      hx0, hx1, hx2] at hpost
    refine hpost key msg (Proof.Poly1305.Repr.buffered hr) ?_
    rw [show (0 : BitVec 64).toNat = 0 from rfl, hr.1]

/-! ## `vg_chacha20_block` -/

theorem block_call {s : State} {S B : Addr} (hx0 : s.gpr .x0 = S) (hx1 : s.gpr .x1 = B)
    (hdj : (⟨B, 256⟩ : Region).Disjoint ⟨S, 64⟩)
    (hc : Covers ([⟨S, 64⟩] ++ [⟨B, 256⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨B, 256⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨B, 256⟩] s s' → stateAt s'.mem B = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.AArch64.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockAArch64) Proof.ChaCha20.AArch64.block_correct
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
  refine WP.call (k := Proof.ChaCha20.xorAArch64) Proof.ChaCha20.AArch64.Xor.xor_correct
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

end

/-!
# ChaCha20-Poly1305 on AArch64: the entry state, regions and invariant

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.ChaCha20Poly1305

open Spec.ChaCha20Poly1305
open Spec.Poly1305 (bytesAt)

open VG.AArch64 in
/-- The precondition of both functions: `ctx` (1024 bytes) and `data` may be
read and written, `aad` read; none of them overlaps another; nothing wraps
around the end of the address space. -/
def preAArch64 (s : AArch64.State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 1024⟩
  let aad : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
  let data : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  s.rd = [aad] ∧ s.wr = [ctx, data] ∧
  ctx.Disjoint aad ∧ ctx.Disjoint data ∧ aad.Disjoint data ∧
  (s.gpr .x0).toNat + 1024 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
  (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64

open VG.AArch64 in
def pubAArch64 (s₁ s₂ : AArch64.State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
  s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_chacha20_poly1305_seal(ctx, aad, aad_len, data, len)`. -/
def sealAArch64 : Contract AArch64.isa where
  pre := preAArch64
  post s s' :=
    let ctx := s.gpr .x0
    encrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) =
      (bytesAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat, bytesAt s'.mem (ctx + 48) 16)
  pub := pubAArch64

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_chacha20_poly1305_open(ctx, aad, aad_len, data, len) -> u32`. -/
def openAArch64 : Contract AArch64.isa where
  pre := preAArch64
  post s s' :=
    let ctx := s.gpr .x0
    match decrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
        (bytesAt s.mem (ctx + 48) 16) with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0
  pub := pubAArch64

end VG.Proof.ChaCha20Poly1305

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-! ## One instruction at a time (beyond those of `vg_chacha20_xor`'s proof) -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl .x d n sh :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .x d (s.gpr n <<< sh)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_add {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add .x d n m :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .x d (s.gpr n + s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_eor {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_orr {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .orr .x d n m :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .x d (s.gpr n ||| s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_movz32 {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d ((imm.setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .w d imm 0 :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .w d (imm.setWidth 32)) exec_movz_w (k _ (Upd.write _ _ _ _))

theorem wp_movk32 {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (((s.gpr d).setWidth 32 &&& (0xFFFF : BitVec 32) ||| imm.setWidth 32 <<< 16 :
      BitVec 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movk .w d imm 1 :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons exec_movk_w (k _ (Upd.write _ _ _ _))

end

/-- A block that writes no callee-saved register keeps them, and the stack
pointer. -/
theorem WP.kept {is : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q)
    (hc : (is.all fun i => preserved.all fun r => dstOf i != some r) = true) :
    WP isa (.block is) s fun s' => Q s' ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he (.inl rfl), Exec.sp he⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  simpa using this

/-- Code keeps the stack pointer. -/
theorem WP.withSp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.sp he⟩

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev cx : Addr := s₀.gpr .x0
abbrev ad : Addr := s₀.gpr .x1
abbrev AL : Nat := (s₀.gpr .x2).toNat
abbrev dp : Addr := s₀.gpr .x3
abbrev L : Nat := (s₀.gpr .x4).toNat
/-- The key, the nonce, the additional data, the data and the tag on entry. -/
abbrev K : List Byte := bytesAt s₀.mem (cx s₀) 32
abbrev N : List Byte := bytesAt s₀.mem (cx s₀ + 32) 12
abbrev A : List Byte := bytesAt s₀.mem (ad s₀) (AL s₀)
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (L s₀)
abbrev T0 : List Byte := bytesAt s₀.mem (cx s₀ + 48) 16
/-- The one-time Poly1305 key. -/
abbrev otk : List Byte := Spec.ChaCha20Poly1305.polyKeyGen (K s₀) (N s₀)
abbrev ctxR : Region := ⟨cx s₀, 1024⟩
abbrev aR : Region := ⟨ad s₀, AL s₀⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
/-- `ctx[k, k + n)`. -/
abbrev sub (k n : Nat) : Region := ⟨off (cx s₀) k, n⟩
end

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [aR s₀]
  wr : s₀.wr = [ctxR s₀, dR s₀]
  c_a : (ctxR s₀).Disjoint (aR s₀)
  c_d : (ctxR s₀).Disjoint (dR s₀)
  a_d : (aR s₀).Disjoint (dR s₀)
  wrap_c : (cx s₀).toNat + 1024 ≤ 2 ^ 64
  wrap_a : (ad s₀).toNat + AL s₀ ≤ 2 ^ 64
  wrap_d : (dp s₀).toNat + L s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : preAArch64 s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## Regions -/

theorem sub_ctx (s₀ : State) {k n : Nat} (h : k + n ≤ 1024) : Region.Sub (sub s₀ k n) (ctxR s₀) :=
  sub_off _ h

theorem sub_sub (s₀ : State) {a m k n : Nat} (h₁ : a ≤ k) (h₂ : k + n ≤ a + m) (_h₃ : a + m ≤ 1024) :
    Region.Sub (sub s₀ k n) (sub s₀ a m) := Offset.sub (cx s₀) h₁ h₂

theorem sub_disj (s₀ : State) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 1024)
    (hb : b + m ≤ 1024) : (sub s₀ a n).Disjoint (sub s₀ b m) := Offset.disjoint (cx s₀) h (by lit_omega) (by lit_omega)

theorem contains_sub (s₀ : State) {k n a w : Nat} (h₁ : k ≤ a) (h₂ : a + w ≤ k + n) (h₃ : k + n ≤ 1024) :
    (sub s₀ k n).Contains (off (cx s₀) a) w := Offset.contains (cx s₀) h₁ h₂ (by lit_omega)

theorem contains_ctx (s₀ : State) {a w : Nat} (h : a + w ≤ 1024) : (ctxR s₀).Contains (off (cx s₀) a) w :=
  Offset.contains_base (cx s₀) h (by lit_omega)

theorem APre.in_ctx {s₀ : State} (hp : APre s₀) {a w : Nat} (h : a + w ≤ 1024) :
    InRegions s₀.wr (off (cx s₀) a) w := ⟨ctxR s₀, by simp [hp.wr], contains_ctx s₀ h⟩

theorem APre.in_ctx' {s₀ : State} (hp : APre s₀) {a w : Nat} (h : a + w ≤ 1024) :
    InRegions (s₀.rd ++ s₀.wr) (off (cx s₀) a) w := ⟨ctxR s₀, by simp [hp.wr], contains_ctx s₀ h⟩

theorem APre.off_toNat {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < 1024) :
    (off (cx s₀) k).toNat = (cx s₀).toNat + k := by
  have := hp.wrap_c
  rw [BitVec.toNat_add, toNat_ofNat_lt (by lit_omega), Nat.mod_eq_of_lt (by lit_omega)]

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  show p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Words of the context at different offsets are at separate addresses. -/
theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  VG.Proof.ChaCha20.AArch64.Xor.readW64_off m p v hd he h

theorem readW32_off (m : Mem) (p : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 32 = m.readW (off p d) 32 :=
  Mem.readW_writeW_sep (Offset.sep p h (by lit_omega) (by lit_omega)) (by decide)

/-! ## Covering the callees' regions -/

theorem covers_sub {s₀ s : State} (hp : APre s₀) (hwr : s.wr = s₀.wr) (rs : List Region)
    (h : ∀ r ∈ rs, ∃ k, r = sub s₀ k r.len ∧ k + r.len ≤ 1024) : Covers rs s.wr := by
  refine Covers.of_sub fun r hr => ?_
  obtain ⟨k, hrk, hk⟩ := h r hr
  exact ⟨ctxR s₀, by simp [hwr, hp.wr], k, by rw [hrk], hk⟩

theorem covers_left {rs wr : List Region} (rd : List Region) (h : Covers rs wr) : Covers rs (rd ++ wr) :=
  fun a n hi => by
    obtain ⟨r, hr, hc⟩ := h a n hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_nil_append {rs rs' : List Region} (h : Covers rs rs') : Covers ([] ++ rs) rs' := by
  simpa using h

/-- A callee's state (at `ctx + a`, `n` bytes) and argument (at `ctx + b`,
`m` bytes) in the context. -/
theorem covers2 {s₀ s : State} (hp : APre s₀) (hwr : s.wr = s₀.wr) {a n b m : Nat}
    (ha : a + n ≤ 1024) (hb : b + m ≤ 1024) :
    Covers ([sub s₀ b m] ++ [sub s₀ a n]) (s.rd ++ s.wr) :=
  covers_left _ (covers_sub hp hwr _ fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨b, rfl, hb⟩
    · exact ⟨a, rfl, ha⟩)

theorem covers1 {s₀ s : State} (hp : APre s₀) (hwr : s.wr = s₀.wr) {a n : Nat} (ha : a + n ≤ 1024) :
    Covers [sub s₀ a n] s.wr :=
  covers_sub hp hwr _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨a, rfl, ha⟩

/-! ## The saved registers and the invariant -/

/-- Our caller's `x21`–`x25` and our return address, saved in `ctx[592, 640)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (off (cx s₀) 592) 64 = s₀.gpr .x21 ∧ m.readW (off (cx s₀) 600) 64 = s₀.gpr .x22 ∧
  m.readW (off (cx s₀) 608) 64 = s₀.gpr .x23 ∧ m.readW (off (cx s₀) 616) 64 = s₀.gpr .x24 ∧
  m.readW (off (cx s₀) 624) 64 = s₀.gpr .x25 ∧ m.readW (off (cx s₀) 632) 64 = s₀.gpr .x30

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sub s₀ 592 48).Disjoint r) : Saved s₀ m' := by
  have c : ∀ d, 592 ≤ d → d + 8 ≤ 640 → (sub s₀ 592 48).Contains (off (cx s₀) d) (64 / 8) :=
    fun d h₁ h₂ => contains_sub s₀ h₁ h₂ (by lit_omega)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨by rw [hf.readW (c 592 (Nat.le_refl _) (by lit_omega)) hd (by decide), h1],
    by rw [hf.readW (c 600 (by lit_omega) (by lit_omega)) hd (by decide), h2],
    by rw [hf.readW (c 608 (by lit_omega) (by lit_omega)) hd (by decide), h3],
    by rw [hf.readW (c 616 (by lit_omega) (by lit_omega)) hd (by decide), h4],
    by rw [hf.readW (c 624 (by lit_omega) (by lit_omega)) hd (by decide), h5],
    by rw [hf.readW (c 632 (by lit_omega) (by lit_omega)) hd (by decide), h6]⟩

/-- The working space: `ctx[64, 1024)`. -/
abbrev workR (s₀ : State) : Region := sub s₀ 64 960

/-- The callee-saved registers the code never writes (the functions it
calls restore `x19` and `x20`). -/
def untouched : List Reg := [.x19, .x20, .x26, .x27, .x28]

theorem untouched_preserved : ∀ r ∈ untouched, r ∈ preserved ∧ r ≠ .x30 := by decide

/-- What holds between the parts of the code. -/
structure Inv (s₀ : State) (s : State) : Prop where
  x21 : s.gpr .x21 = cx s₀
  x22 : s.gpr .x22 = dp s₀
  x23 : s.gpr .x23 = s₀.gpr .x4
  x24 : s.gpr .x24 = ad s₀
  x25 : s.gpr .x25 = s₀.gpr .x2
  un : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [workR s₀, dR s₀] s₀.mem s.mem

theorem pres (r : Reg) (h : r ∈ preserved ∧ r ≠ .x30 := by decide) : r ∈ preserved := h.1
theorem pres30 (r : Reg) (h : r ∈ preserved ∧ r ≠ .x30 := by decide) : r ≠ .x30 := h.2

/-- The invariant survives a part that keeps the callee-saved registers and
writes only the working space and the data. -/
theorem Inv.step {s₀ s s' : State} {rs : List Region} (h : Inv s₀ s) (hk : Kept rs s s')
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [workR s₀, dR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ 592 48).Disjoint r) : Inv s₀ s' where
  x21 := by rw [hk.cs _ (pres .x21) (pres30 .x21), h.x21]
  x22 := by rw [hk.cs _ (pres .x22) (pres30 .x22), h.x22]
  x23 := by rw [hk.cs _ (pres .x23) (pres30 .x23), h.x23]
  x24 := by rw [hk.cs _ (pres .x24) (pres30 .x24), h.x24]
  x25 := by rw [hk.cs _ (pres .x25) (pres30 .x25), h.x25]
  un r hr := by
    rw [hk.cs _ (untouched_preserved r hr).1 (untouched_preserved r hr).2, h.un r hr]
  sp := by rw [hk.sp, h.sp]
  rd := by rw [hk.rd, h.rd]
  wr := by rw [hk.wr, h.wr]
  saved := h.saved.frame hk.frame hsv
  frame := h.frame.trans (hk.frame.sub hsub)

/-- Kept, from a block's facts. -/
theorem Kept.of {rs : List Region} {s s' : State} (hg : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    Kept rs s s' :=
  ⟨fun r hr _ => hg r hr, hsp, hrd, hwr, hf⟩

end VG.Proof.ChaCha20Poly1305.AArch64

section

/-!
# ChaCha20-Poly1305 on AArch64: the prologue

Untrusted: everything here is checked by Lean. Saving the registers, the
ChaCha20 state for counter 0, the one-time key and the Poly1305 state for it.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd wp_addImm wp_mov wp_str wp_str32 wp_ldr32)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## Saving the registers -/

theorem saveMoves_eq : save ++ moves =
    [.str .x .x22 .x0 600, .str .x .x23 .x0 608, .str .x .x24 .x0 616, .str .x .x25 .x0 624,
     .str .x .x30 .x0 632, .str .x .x21 .x0 592,
     mov .x21 .x0, mov .x24 .x1, mov .x25 .x2, mov .x22 .x3, mov .x23 .x4] := rfl

/-- The registers the moves write. -/
theorem untouched_ne {r : Reg} (hr : r ∈ untouched) :
    r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x24 ∧ r ≠ .x25 := by
  simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem saveMoves_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (save ++ moves)) s₀ fun s =>
      s.gpr .x21 = cx s₀ ∧ s.gpr .x24 = ad s₀ ∧ s.gpr .x25 = s₀.gpr .x2 ∧ s.gpr .x22 = dp s₀ ∧
      s.gpr .x23 = s₀.gpr .x4 ∧ (∀ r ∈ untouched, s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧
      s.wr = s₀.wr ∧ Frame [sub s₀ 592 48] s₀.mem s.mem ∧ Saved s₀ s.mem := by
  have o : ∀ d, 592 ≤ d → d + 8 ≤ 640 → InRegions s₀.wr (off (cx s₀) d) 8 :=
    fun d _ h => hp.in_ctx (by lit_omega)
  rw [saveMoves_eq]
  refine wp_str (a := off (cx s₀) 600) (by decide) rfl (o 600 (by lit_omega) (by lit_omega)) fun s₁ g₁ => ?_
  refine wp_str (a := off (cx s₀) 608) (by decide) (by rw [g₁.gpr])
    (by rw [g₁.wr]; exact o 608 (by lit_omega) (by lit_omega)) fun s₂ g₂ => ?_
  have e₂ : s₂.gpr = s₀.gpr := by rw [g₂.gpr, g₁.gpr]
  refine wp_str (a := off (cx s₀) 616) (by decide) (by rw [e₂])
    (by rw [g₂.wr, g₁.wr]; exact o 616 (by lit_omega) (by lit_omega)) fun s₃ g₃ => ?_
  refine wp_str (a := off (cx s₀) 624) (by decide) (by rw [g₃.gpr, e₂])
    (by rw [g₃.wr, g₂.wr, g₁.wr]; exact o 624 (by lit_omega) (by lit_omega)) fun s₄ g₄ => ?_
  have e₄ : s₄.gpr = s₀.gpr := by rw [g₄.gpr, g₃.gpr, e₂]
  refine wp_str (a := off (cx s₀) 632) (by decide) (by rw [e₄])
    (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact o 632 (by lit_omega) (by lit_omega)) fun s₅ g₅ => ?_
  refine wp_str (a := off (cx s₀) 592) (by decide) (by rw [g₅.gpr, e₄])
    (by rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact o 592 (by lit_omega) (by lit_omega)) fun s₆ g₆ => ?_
  have e₆ : s₆.gpr = s₀.gpr := by rw [g₆.gpr, g₅.gpr, e₄]
  refine wp_mov fun s₇ u₇ => wp_mov fun s₈ u₈ => wp_mov fun s₉ u₉ => wp_mov fun s₁₀ u₁₀ =>
    wp_mov fun s₁₁ u₁₁ => WP.block_nil ?_
  have hm : s₁₁.mem = (((((s₀.mem.writeW (off (cx s₀) 600) (s₀.gpr .x22)).writeW (off (cx s₀) 608)
      (s₀.gpr .x23)).writeW (off (cx s₀) 616) (s₀.gpr .x24)).writeW (off (cx s₀) 624)
      (s₀.gpr .x25)).writeW (off (cx s₀) 632) (s₀.gpr .x30)).writeW (off (cx s₀) 592) (s₀.gpr .x21) := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, g₁.mem,
      g₅.gpr, e₄, g₃.gpr, e₂, g₁.gpr]
  have c : ∀ d, 592 ≤ d → d + 8 ≤ 640 → (sub s₀ 592 48).Contains (off (cx s₀) d) (64 / 8) :=
    fun d h₁ h₂ => contains_sub s₀ h₁ h₂ (by lit_omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.gpr, e₆]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr,
      u₇.other _ (by decide), e₆]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide),
      u₇.other _ (by decide), e₆]
  · rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), e₆]
  · rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), e₆]
  · have h := untouched_ne hr
    rw [u₁₁.other _ h.2.2.1, u₁₀.other _ h.2.1, u₉.other _ h.2.2.2.2, u₈.other _ h.2.2.2.1,
      u₇.other _ h.1, e₆]
  · rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd]
  · rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr]
  · rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 600 (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 608 (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 616 (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 624 (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 632 (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 592 (Nat.le_refl _) (by lit_omega))
  · rw [hm]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW64_off]

/-! ## The ChaCha20 state -/

/-- The word `stW k` stores, from memory `m` and the context `c`. -/
def wordOf (m : Mem) (c : Addr) (k : Nat) : BitVec 32 :=
  if k < 4 then consts.getD k 0
  else if k < 12 then m.readW (off c (4 * (k - 4))) 32
  else if k = 12 then 0
  else m.readW (off c (32 + 4 * (k - 13))) 32

/-- The context may be read and written. -/
def CtxOk (c : Addr) (s : State) : Prop :=
  ∀ a w, a + w ≤ 1024 → InRegions (s.rd ++ s.wr) (off c a) w ∧ InRegions s.wr (off c a) w

/-- `movz` of the low half and `movk` of the high half, then a 32-bit store. -/
theorem const_word (c : BitVec 32) :
    (((((c.extractLsb' 0 16).setWidth 32).setWidth 64).setWidth 32 &&& (0xFFFF : BitVec 32) |||
      (c.extractLsb' 16 16).setWidth 32 <<< 16 : BitVec 32).setWidth 64).setWidth 32 = c := by
  rw [BitVec.setWidth_setWidth_of_le _ (by lit_omega), BitVec.setWidth_setWidth_of_le _ (by lit_omega),
    BitVec.setWidth_eq, BitVec.setWidth_eq]
  exact movz_movk c

theorem load_word (v : BitVec 32) : ((v.setWidth 64).setWidth 32) = v := by
  rw [BitVec.setWidth_setWidth_of_le _ (by lit_omega), BitVec.setWidth_eq]

theorem stW_ok {c : Addr} {k : Nat} (hk : k < 16) {s : State} (hx21 : s.gpr .x21 = c) (hc : CtxOk c s) :
    WP isa (.block (stW k)) s fun s' =>
      s'.mem = s.mem.writeW (off c (64 + 4 * k)) (wordOf s.mem c k) ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o := (hc (64 + 4 * k) 4 (by lit_omega)).2
  unfold stW stSrc wordOf
  by_cases h₁ : k < 4
  · simp only [h₁, ite_true, List.cons_append, List.nil_append]
    refine wp_movz32 fun s₁ u₁ => wp_movk32 fun s₂ u₂ => ?_
    refine wp_str32 (a := off c (64 + 4 * k)) (by lit_omega) (by rw [u₂.other _ (by decide),
      u₁.other _ (by decide), hx21]) (by rw [u₂.wr, u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, const_word], fun r hr => by
      rw [g₃.gpr, u₂.other r hr, u₁.other r hr], by rw [g₃.rd, u₂.rd, u₁.rd], by rw [g₃.wr, u₂.wr, u₁.wr]⟩
  by_cases h₂ : k < 12
  · simp only [h₁, h₂, ite_true, ite_false, List.cons_append, List.nil_append]
    have i := (hc (4 * (k - 4)) 4 (by lit_omega)).1
    refine wp_ldr32 (a := off c (4 * (k - 4))) (by lit_omega) (by rw [hx21]) i fun s₁ u₁ => ?_
    refine wp_str32 (a := off c (64 + 4 * k)) (by lit_omega) (by rw [u₁.other _ (by decide), hx21])
      (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem, load_word], fun r hr => by
      rw [g₃.gpr, u₁.other r hr], by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr]⟩
  by_cases h₃ : k = 12
  · simp only [h₃, ite_true]
    refine wp_movz32 fun s₁ u₁ => ?_
    refine wp_str32 (a := off c (64 + 4 * 12)) (by lit_omega) (by rw [u₁.other _ (by decide), hx21])
      (by rw [u₁.wr]; exact h₃ ▸ o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem]; rfl, fun r hr => by
      rw [g₃.gpr, u₁.other r hr], by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr]⟩
  · simp only [h₁, h₂, h₃, ite_false, List.cons_append, List.nil_append]
    have i := (hc (32 + 4 * (k - 13)) 4 (by lit_omega)).1
    refine wp_ldr32 (a := off c (32 + 4 * (k - 13))) (by lit_omega) (by rw [hx21]) i fun s₁ u₁ => ?_
    refine wp_str32 (a := off c (64 + 4 * k)) (by lit_omega) (by rw [u₁.other _ (by decide), hx21])
      (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem, load_word], fun r hr => by
      rw [g₃.gpr, u₁.other r hr], by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr]⟩

/-- The context's words `[a, a + 4)` outside `[64, 64 + n)`. -/
theorem readW_frame_ctx {c : Addr} {m m' : Mem} {n : Nat} (hf : Frame [⟨off c 64, n⟩] m m') {a : Nat}
    (ha : a + 4 ≤ 64) (hn : n ≤ 960) : m'.readW (off c a) 32 = m.readW (off c a) 32 := by
  refine hf.readW (r := ⟨off c a, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  exact Offset.disjoint c (.inl ha) (by lit_omega) (by lit_omega)

theorem wordOf_frame {c : Addr} {m m' : Mem} {n : Nat} (hf : Frame [⟨off c 64, n⟩] m m') (hn : n ≤ 960)
    {k : Nat} (hk : k < 16) : wordOf m' c k = wordOf m c k := by
  unfold wordOf
  split_ifs
  · rfl
  · exact readW_frame_ctx hf (by lit_omega) hn
  · rfl
  · exact readW_frame_ctx hf (by lit_omega) hn

theorem initState_step (j : Nat) : (List.range (j + 1)).flatMap stW = (List.range j).flatMap stW ++ stW j := by
  simp [List.range_succ, List.flatMap_append]

/-- The first `j` words of the ChaCha20 state. -/
theorem initState_ok {c : Addr} {j : Nat} (hj : j ≤ 16) {s : State} (hx21 : s.gpr .x21 = c)
    (hc : CtxOk c s) :
    WP isa (.block ((List.range j).flatMap stW)) s fun s' =>
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨off c 64, 4 * j⟩] s.mem s'.mem ∧
      ∀ i < j, s'.mem.readW (off c (64 + 4 * i)) 32 = wordOf s.mem c i := by
  induction j with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by lit_omega)⟩
  | succ j ih =>
    rw [initState_step]
    refine WP.block_append (WP.mono (ih (by lit_omega)) fun s₁ ⟨g₁, rd₁, wr₁, f₁, w₁⟩ => ?_)
    have hc₁ : CtxOk c s₁ := by rw [CtxOk, rd₁, wr₁]; exact hc
    refine WP.mono (stW_ok (by lit_omega) (by rw [g₁ _ (by decide), hx21]) hc₁) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
    refine ⟨fun r hr => by rw [g₂ r hr, g₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_, fun i hi => ?_⟩
    · rw [m₂]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by lit_omega)
      · exact Offset.contains c (by lit_omega) (by lit_omega) (by lit_omega)
    · rw [m₂, wordOf_frame f₁ (by lit_omega) (by lit_omega)]
      by_cases h : i = j
      · subst h; exact Mem.readW_writeW_self32 _ _ _
      · rw [readW32_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega)]
        exact w₁ i (by lit_omega)

theorem consts_eq : ∀ i < 4, consts.getD i 0 = Spec.ChaCha20.constants.getD i 0 := by decide +kernel

/-- The words stored are the initial ChaCha20 state for the key, counter 0
and the nonce. -/
theorem stateAt_initState {s₀ : State} {m₁ m' : Mem} (hf₁ : Frame [sub s₀ 592 48] s₀.mem m₁)
    (hw : ∀ i < 16, m'.readW (off (cx s₀) (64 + 4 * i)) 32 = wordOf m₁ (cx s₀) i) :
    stateAt m' (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
  have r₁ : ∀ a, a + 4 ≤ 44 → m₁.readW (off (cx s₀) a) 32 = s₀.mem.readW (off (cx s₀) a) 32 := by
    intro a ha
    refine hf₁.readW (r := sub s₀ a 4) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  apply Vector.ext
  intro i hi
  simp only [stateAt, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  rw [show off (cx s₀) 64 + BitVec.ofNat 64 (4 * i) = off (cx s₀) (64 + 4 * i) from off_off _ _ _, hw i hi]
  unfold wordOf
  split_ifs with h₁ h₂ h₃
  · exact consts_eq i h₁
  · rw [r₁ _ (by lit_omega), show (K s₀) = Spec.ChaCha20.bytesAt s₀.mem (cx s₀) 32 from rfl,
      wordLE_bytesAt s₀.mem (cx s₀) (n := 32) (j := i - 4) (by lit_omega)]
  · rfl
  · rw [r₁ _ (by lit_omega)]
    rw [show (N s₀) = Spec.ChaCha20.bytesAt s₀.mem (cx s₀ + 32) 12 from rfl,
      wordLE_bytesAt s₀.mem (cx s₀ + 32) (n := 12) (j := i - 13) (by lit_omega)]
    refine congrArg (fun a => s₀.mem.readW a 32) ?_
    show cx s₀ + BitVec.ofNat 64 (32 + 4 * (i - 13)) = cx s₀ + 32 + BitVec.ofNat 64 (4 * (i - 13))
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl

/-- The first `n ≤ 64` bytes of a ChaCha20 state in memory. -/
theorem bytesAt_serialize (m : Mem) (p : Addr) {n : Nat} (hn : n ≤ 64) :
    bytesAt m p n = (Spec.ChaCha20.serialize (stateAt m p)).take n := by
  apply List.ext_getElem
  · simp [bytesAt, VG.Proof.ChaCha20.length_serialize]; omega
  · intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have e := VG.Proof.ChaCha20.serialize_stateAt m p (i := i) (by lit_omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega), Option.getD_some] at e
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, e]

/-! ## The first block -/

/-- `x0 = x21 + a` and `x1 = x21 + b`. -/
theorem ptrs2_ok {a b : Nat} (ha : a < 4096) (hb : b < 4096) (s : State) :
    WP isa (.block [.addImm .x .x0 .x21 a, .addImm .x .x1 .x21 b]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) a ∧ s'.gpr .x1 = off (s.gpr .x21) b ∧ Kept [] s s' := by
  have h : WP isa (.block [.addImm .x .x0 .x21 a, .addImm .x .x1 .x21 b]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) a ∧ s'.gpr .x1 = off (s.gpr .x21) b ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_addImm ha fun s₁ u₁ => wp_addImm hb fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.other _ (by decide)],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept h (by simp [dstOf, preserved])) fun s' ⟨⟨h0, h1, hrd, hwr, hm⟩, hg, hsp⟩ =>
    ⟨h0, h1, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- After the first block: the registers saved and moved, the ChaCha20
state, and the pointers for the block function. -/
structure Post1 (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  fine : Frame [workR s₀] s₀.mem s.mem
  st : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  x0 : s.gpr .x0 = off (cx s₀) 64
  x1 : s.gpr .x1 = off (cx s₀) 128

theorem sub1 (s₀ : State) {k n : Nat} (h₁ : 64 ≤ k) (h₂ : k + n ≤ 1024) : Region.Sub (sub s₀ k n) (workR s₀) :=
  sub_sub s₀ h₁ (by lit_omega) (by lit_omega)

theorem block1_eq : save ++ moves ++ initState ++ ([.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 128] : List Instr) =
    (save ++ moves) ++ (initState ++ ([.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 128] : List Instr)) := by
  simp only [List.append_assoc]

theorem block1_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (save ++ moves ++ initState ++ ([.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 128] : List Instr))) s₀
      (Post1 s₀) := by
  rw [block1_eq]
  refine WP.block_append (WP.mono (WP.withSp (saveMoves_ok hp))
    fun s₁ ⟨⟨e21, e24, e25, e22, e23, un₁, rd₁, wr₁, f₁, sv₁⟩, sp₁⟩ => ?_)
  have hc₁ : CtxOk (cx s₀) s₁ := fun a w h => by
    rw [rd₁, wr₁]; exact ⟨hp.in_ctx' h, hp.in_ctx h⟩
  refine WP.block_append (WP.mono (WP.withSp (initState_ok (j := 16) (Nat.le_refl _) e21 hc₁))
    fun s₂ ⟨⟨g₂, rd₂, wr₂, f₂, w₂⟩, sp₂⟩ => ?_)
  refine WP.mono (ptrs2_ok (a := 64) (b := 128) (by lit_omega) (by lit_omega) s₂) fun s₃ ⟨h0, h1, k₃⟩ => ?_
  have x21₂ : s₂.gpr .x21 = cx s₀ := by rw [g₂ _ (by decide), e21]
  have hm : s₃.mem = s₂.mem := funext fun x => k₃.frame x fun _ h => absurd h List.not_mem_nil
  have f₂' : Frame [sub s₀ 64 64] s₁.mem s₂.mem := f₂
  have gcs : ∀ r ∈ preserved, r ≠ .x30 → s₃.gpr r = s₂.gpr r := k₃.cs
  have fine : Frame [workR s₀] s₀.mem s₃.mem := by
    rw [hm]
    refine (f₁.sub fun r hr => ?_).trans (f₂'.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s₀, List.mem_singleton_self _, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s₀, List.mem_singleton_self _, sub1 s₀ (by lit_omega) (by lit_omega)⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [gcs _ (pres .x21) (pres30 .x21), x21₂]
  · rw [gcs _ (pres .x22) (pres30 .x22), g₂ _ (by decide), e22]
  · rw [gcs _ (pres .x23) (pres30 .x23), g₂ _ (by decide), e23]
  · rw [gcs _ (pres .x24) (pres30 .x24), g₂ _ (by decide), e24]
  · rw [gcs _ (pres .x25) (pres30 .x25), g₂ _ (by decide), e25]
  · have h := untouched_preserved r hr
    rw [gcs r h.1 h.2, g₂ r (by rintro rfl; simp [untouched] at hr), un₁ r hr]
  · rw [k₃.sp, sp₂, sp₁]
  · rw [k₃.rd, rd₂, rd₁]
  · rw [k₃.wr, wr₂, wr₁]
  · rw [hm]
    exact sv₁.frame f₂' (by
      simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  · exact fine.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · exact fine
  · rw [hm]; exact stateAt_initState f₁ w₂
  · rw [h0, x21₂]
  · rw [h1, x21₂]

/-! ## The whole prologue -/

/-- A part that writes `ctx[k, k + n)` keeps the invariant. -/
theorem Inv.step1 {s₀ s s' : State} (h : Inv s₀ s) {k n : Nat} (hk : Kept [sub s₀ k n] s s')
    (h₁ : 64 ≤ k) (h₂ : k + n ≤ 1024) (h₃ : k + n ≤ 592 ∨ 640 ≤ k) : Inv s₀ s' :=
  h.step hk (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨workR s₀, by simp, sub1 s₀ h₁ h₂⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by lit_omega) (by lit_omega) h₂)

/-- A part that writes no memory keeps the invariant. -/
theorem Inv.step0 {s₀ s s' : State} (h : Inv s₀ s) (hk : Kept [] s s') : Inv s₀ s' :=
  h.step hk (fun _ hr => absurd hr List.not_mem_nil) (fun _ hr => absurd hr List.not_mem_nil)

theorem Kept.mem_eq {s s' : State} (hk : Kept [] s s') : s'.mem = s.mem :=
  funext fun x => hk.frame x fun _ h => absurd h List.not_mem_nil

/-- The frame of a part that writes `ctx[k, k + n)`, in the working space. -/
theorem frame_work1 {s₀ s s' : State} {k n : Nat} (hk : Kept [sub s₀ k n] s s') (h₁ : 64 ≤ k)
    (h₂ : k + n ≤ 1024) : Frame [workR s₀] s.mem s'.mem :=
  hk.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨workR s₀, by simp, sub1 s₀ h₁ h₂⟩

/-- After the prologue. -/
structure PostP (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  fine : Frame [workR s₀] s₀.mem s.mem
  poly : Repr s.mem (off (cx s₀) 448) (otk s₀) []
  st : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)

theorem prologue_ok {s₀ : State} (hp : APre s₀) : WP isa prologue s₀ (PostP s₀) := by
  unfold prologue
  refine WP.seq (WP.mono (block1_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (block_call h₁.x0 h₁.x1
    (sub_disj s₀ (a := 128) (n := 256) (b := 64) (m := 64) (by lit_omega) (by lit_omega) (by lit_omega))
    (covers2 hp h₁.inv.wr (a := 128) (n := 256) (b := 64) (m := 64) (by lit_omega) (by lit_omega))
    (covers1 hp h₁.inv.wr (a := 128) (n := 256) (by lit_omega)) fun s₂ k₂ blk₂ => ?_)
  have i₂ := h₁.inv.step1 (k := 128) (n := 256) k₂ (by lit_omega) (by lit_omega) (by lit_omega)
  refine WP.seq (WP.mono (ptrs2_ok (a := 448) (b := 128) (by lit_omega) (by lit_omega) s₂)
    fun s₃ ⟨h0, h1, k₃⟩ => ?_)
  have i₃ := i₂.step0 k₃
  rw [i₂.x21] at h0 h1
  refine init_call h0 h1 (sub_disj s₀ (a := 448) (n := 128) (b := 128) (m := 32) (by lit_omega) (by lit_omega)
      (by lit_omega))
    (covers2 hp i₃.wr (a := 448) (n := 128) (b := 128) (m := 32) (by lit_omega) (by lit_omega))
    (covers1 hp i₃.wr (a := 448) (n := 128) (by lit_omega)) fun s₄ k₄ repr₄ => ?_
  have m₃ := k₃.mem_eq
  have st₂ : stateAt s₂.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)), h₁.st]
  refine ⟨i₃.step1 (k := 448) (n := 128) k₄ (by lit_omega) (by lit_omega) (by lit_omega),
    h₁.fine.trans ((frame_work1 (k := 128) (n := 256) k₂ (by lit_omega) (by lit_omega)).trans (by
      rw [← m₃]; exact frame_work1 (k := 448) (n := 128) k₄ (by lit_omega) (by lit_omega))), ?_, ?_⟩
  · have hk : bytesAt s₃.mem (off (cx s₀) 128) 32 = otk s₀ := by
      rw [m₃, bytesAt_serialize _ _ (by lit_omega), blk₂, h₁.st]; rfl
    rw [← hk]; exact repr₄
  · rw [stateAt_frame k₄.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)), m₃, st₂]

end VG.Proof.ChaCha20Poly1305.AArch64

end

/-!
# ChaCha20-Poly1305 on AArch64: absorbing padded data

Untrusted: everything here is checked by Lean. `macPad p n` absorbs the `n`
bytes at `p` into the Poly1305 state, and zeros to a multiple of 16:
`msg ++ x ++ pad16 x`.
-/

open VG.PowLit

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd wp_addImm wp_subImm wp_mov wp_movz wp_sub wp_lsr wp_ldrb
  wp_strb wp_str eval_zero eval_nonzero_ofNat ofNat_beq_zero sub_ofNat add_ofNat writeW8_apply)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20Poly1305 (pad16)

/-- The registers `macPad` may take its arguments in. -/
def MacRegs (p n : Reg) : Prop := (p = .x24 ∨ p = .x22) ∧ (n = .x25 ∨ n = .x23)

/-- What `macPad` needs of the bytes it absorbs. -/
structure Src (s₀ : State) (P : Addr) (len : Nat) : Prop where
  lt : len < 2 ^ 64
  wrap : P.toNat + len ≤ 2 ^ 64
  ctx : (ctxR s₀).Disjoint ⟨P, len⟩
  cov : Covers [⟨P, len⟩] (s₀.rd ++ s₀.wr)

theorem contains_off_sub {P : Addr} {a n len w : Nat} {x : Addr} (h : a + n ≤ len)
    (hc : (⟨P + BitVec.ofNat 64 a, n⟩ : Region).Contains x w) : (⟨P, len⟩ : Region).Contains x w := by
  simp only [Region.Contains] at *
  have : (x - P).toNat ≤ (x - (P + BitVec.ofNat 64 a)).toNat + a := by
    rw [show x - P = (x - (P + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by
      rw [Offset.sub_add_eq, BitVec.sub_add_cancel],
      BitVec.toNat_add, BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

theorem Src.cov_sub {s₀ : State} {P : Addr} {len : Nat} (hs : Src s₀ P len) {a n : Nat} (h : a + n ≤ len)
    {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    Covers [⟨P + BitVec.ofNat 64 a, n⟩] (s.rd ++ s.wr) := by
  intro x w ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  rw [hrd, hwr]
  exact hs.cov x w ⟨_, List.mem_singleton_self _, contains_off_sub h hc⟩

theorem Src.disj_sub {P : Addr} {len : Nat} {R : Region} (hd : R.Disjoint ⟨P, len⟩) {a n : Nat}
    (h : a + n ≤ len) : R.Disjoint ⟨P + BitVec.ofNat 64 a, n⟩ :=
  fun x h₁ h₂ => hd x h₁ (contains_off_sub h h₂)

theorem MacRegs.p_ne {p n : Reg} (hr : MacRegs p n) :
    p ≠ .x0 ∧ p ≠ .x1 ∧ p ≠ .x2 ∧ p ≠ .x9 ∧ p ≠ .x10 ∧ p ∈ preserved ∧ p ≠ .x30 := by
  rcases hr.1 with rfl | rfl <;> decide

theorem MacRegs.n_ne {p n : Reg} (hr : MacRegs p n) :
    n ≠ .x0 ∧ n ≠ .x1 ∧ n ≠ .x2 ∧ n ≠ .x9 ∧ n ≠ .x10 ∧ n ∈ preserved ∧ n ≠ .x30 := by
  rcases hr.2 with rfl | rfl <;> decide

/-! ## The whole blocks -/

theorem macA_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block [.addImm .x .x0 .x21 448, mov .x1 p, .lsr .x .x2 n 4]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) 448 ∧ s'.gpr .x1 = s.gpr p ∧ s'.gpr .x2 = s.gpr n >>> 4 ∧
      Kept [] s s' := by
  have hp := hr.p_ne
  have hn := hr.n_ne
  have h : WP isa (.block [.addImm .x .x0 .x21 448, mov .x1 p, .lsr .x .x2 n 4]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) 448 ∧ s'.gpr .x1 = s.gpr p ∧ s'.gpr .x2 = s.gpr n >>> 4 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_addImm (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_lsr (by decide) fun s₃ u₃ => WP.block_nil
      ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
        by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ hp.1],
        by rw [u₃.gpr, u₂.other _ hn.2.1, u₁.other _ hn.1],
        by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept h (by simp [mov, dstOf, preserved])) fun s' ⟨⟨h0, h1, h2, hrd, hwr, hm⟩, hg, hsp⟩ =>
    ⟨h0, h1, h2, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- `(x << 60) >> 60` is `x mod 16`. -/
theorem shl_shr60 (x : BitVec 64) : (x <<< 60) >>> 60 = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, toNat_ofNat_lt (by lit_omega),
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 64 = 16 * 2 ^ 60 from rfl, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem macC_ok (n : Reg) (s : State) :
    WP isa (.block [.lsl .x .x10 n 60, .lsr .x .x10 .x10 60]) s fun s' =>
      s'.gpr .x10 = BitVec.ofNat 64 ((s.gpr n).toNat % 16) ∧ Kept [] s s' := by
  have h : WP isa (.block [.lsl .x .x10 n 60, .lsr .x .x10 .x10 60]) s fun s' =>
      s'.gpr .x10 = BitVec.ofNat 64 ((s.gpr n).toNat % 16) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mem = s.mem :=
    wp_lsl (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.gpr, u₁.gpr, shl_shr60], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr],
        by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept h (by simp [dstOf, preserved])) fun s' ⟨⟨h10, hrd, hwr, hm⟩, hg, hsp⟩ =>
    ⟨h10, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

theorem macD_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block [.sub .x .x9 n .x10, .add .x .x1 p .x9]) s fun s' =>
      s'.gpr .x1 = s.gpr p + (s.gpr n - s.gpr .x10) ∧ (∀ r, r ≠ .x9 → r ≠ .x1 → s'.gpr r = s.gpr r) ∧
      Kept [] s s' := by
  have hp := hr.p_ne
  have h : WP isa (.block [.sub .x .x9 n .x10, .add .x .x1 p .x9]) s fun s' =>
      s'.gpr .x1 = s.gpr p + (s.gpr n - s.gpr .x10) ∧ (∀ r, r ≠ .x9 → r ≠ .x1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_sub fun s₁ u₁ => wp_add fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.gpr, u₁.other _ hp.2.2.2.1, u₁.gpr],
        fun r h₁ h₂ => by rw [u₂.other _ h₂, u₁.other _ h₁],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept h (by simp [dstOf, preserved])) fun s' ⟨⟨h1, hg', hrd, hwr, hm⟩, hg, hsp⟩ =>
    ⟨h1, hg', Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- `x0 = x21 + a`, `x1 = x21 + b` and `x2 = v`. -/
theorem ptrs3_ok {a b : Nat} (ha : a < 4096) (hb : b < 4096) (v : BitVec 16) (s : State) :
    WP isa (.block [.addImm .x .x0 .x21 a, .addImm .x .x1 .x21 b, .movz .x .x2 v 0]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) a ∧ s'.gpr .x1 = off (s.gpr .x21) b ∧
      s'.gpr .x2 = v.setWidth 64 ∧ Kept [] s s' := by
  have h : WP isa (.block [.addImm .x .x0 .x21 a, .addImm .x .x1 .x21 b, .movz .x .x2 v 0]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) a ∧ s'.gpr .x1 = off (s.gpr .x21) b ∧ s'.gpr .x2 = v.setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_addImm ha fun s₁ u₁ => wp_addImm hb fun s₂ u₂ => wp_movz fun s₃ u₃ => WP.block_nil
      ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
        by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)], u₃.gpr,
        by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept h (by simp [dstOf, preserved])) fun s' ⟨⟨h0, h1, h2, hrd, hwr, hm⟩, hg, hsp⟩ =>
    ⟨h0, h1, h2, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-! ## Zeroing the padded block -/

theorem zero16 : ((0 : BitVec 16).setWidth 64 : BitVec 64) = 0 := rfl

theorem padZ_ok {s₀ : State} (hp : APre s₀) {s : State} (hx21 : s.gpr .x21 = cx s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block [.movz .x .x11 0 0, .str .x .x11 .x21 576, .str .x .x11 .x21 584,
      .addImm .x .x9 .x21 576]) s fun s' =>
      s'.gpr .x9 = off (cx s₀) 576 ∧ (∀ r, r ≠ .x11 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [sub s₀ 576 16] s.mem s'.mem ∧ ∀ j < 16, s'.mem (off (cx s₀) (576 + j)) = 0 := by
  have o0 := hp.in_ctx (a := 576) (w := 8) (by lit_omega)
  have o1 := hp.in_ctx (a := 584) (w := 8) (by lit_omega)
  rw [← hwr] at o0 o1
  refine wp_movz fun s₁ u₁ => ?_
  refine wp_str (a := off (cx s₀) 576) (by decide) (by rw [u₁.other _ (by decide), hx21])
    (by rw [u₁.wr]; exact o0) fun s₂ g₂ => ?_
  refine wp_str (a := off (cx s₀) 584) (by decide) (by rw [g₂.gpr, u₁.other _ (by decide), hx21])
    (by rw [g₂.wr, u₁.wr]; exact o1) fun s₃ g₃ => ?_
  refine wp_addImm (by decide) fun s₄ u₄ => WP.block_nil ?_
  have x11 : s₁.gpr .x11 = 0 := u₁.gpr
  have hm : s₄.mem = (s.mem.writeW (off (cx s₀) 576) (0 : BitVec 64)).writeW (off (cx s₀) 584)
      (0 : BitVec 64) := by
    rw [u₄.mem, g₃.mem, g₂.gpr, g₂.mem, u₁.mem, x11]
  refine ⟨by rw [u₄.gpr, g₃.gpr, g₂.gpr, u₁.other _ (by decide), hx21],
    fun r h₁ h₂ => by rw [u₄.other _ h₂, g₃.gpr, g₂.gpr, u₁.other _ h₁],
    by rw [u₄.rd, g₃.rd, g₂.rd, u₁.rd], by rw [u₄.wr, g₃.wr, g₂.wr, u₁.wr], ?_, fun j hj => ?_⟩
  · rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  · rw [hm, VG.Proof.Poly1305.writeW64_zero_apply, VG.Proof.Poly1305.writeW64_zero_apply]
    have e : ∀ d, d ≤ 576 + j → (off (cx s₀) (576 + j) - off (cx s₀) d).toNat = 576 + j - d := by
      intro d hd
      exact Offset.sub_toNat _ hd (by lit_omega)
    by_cases h : 8 ≤ j
    · rw [e 584 (by lit_omega)]
      simp only [show 576 + j - 584 < 8 by omega, ite_true]
    · have w : ¬ (off (cx s₀) (576 + j) - off (cx s₀) 584).toNat < 8 := by
        rw [Offset.sub_toNat' _ (by lit_omega) (by lit_omega)]
        split <;> omega
      simp only [w, ite_false, e 576 (by lit_omega), show 576 + j - 576 < 8 by omega, ite_true]

/-! ## Copying the last bytes -/

/-- Before byte `i` of the last `t` bytes at `Q` is copied into the padded
block, from the state `s₂` after the block was zeroed. -/
structure CpInv (s₀ s₂ : State) (Q : Addr) (t i : Nat) (s : State) : Prop where
  x1 : s.gpr .x1 = Q + BitVec.ofNat 64 i
  x9 : s.gpr .x9 = off (cx s₀) (576 + i)
  x10 : s.gpr .x10 = BitVec.ofNat 64 (t - i)
  keep : ∀ r ∈ preserved, s.gpr r = s₂.gpr r
  sp : s.sp = s₂.sp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame [sub s₀ 576 16] s₂.mem s.mem
  buf : ∀ j < 16, s.mem (off (cx s₀) (576 + j)) = if j < i then s₂.mem (Q + BitVec.ofNat 64 j) else 0

def copyBody : List Instr :=
  [.ldrb .x11 .x1 0, .strb .x11 .x9 0, .addImm .x .x1 .x1 1, .addImm .x .x9 .x9 1, .subImm .x .x10 .x10 1]

theorem byte_rt (b : Byte) : ((b.setWidth 64).setWidth 8 : Byte) = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by lit_omega), BitVec.setWidth_eq]

theorem off_ne (p : Addr) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : a ≠ b) : off p a ≠ off p b := by
  intro he
  have e : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
    have e := congrArg (· - p) he; simpa using e
  have := congrArg BitVec.toNat e
  rw [toNat_ofNat_lt (by lit_omega), toNat_ofNat_lt (by lit_omega)] at this
  exact h this

theorem copy_step {s₀ : State} (hp : APre s₀) {s₂ : State} {Q : Addr} {t : Nat} (ht : t < 16)
    (hwr : s₂.wr = s₀.wr) (hsrc : ∀ j < t, InRegions (s₂.rd ++ s₂.wr) (Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, ∀ r ∈ [sub s₀ 576 16], (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint r)
    {i : Nat} (hi : i < t) {s : State} (h : CpInv s₀ s₂ Q t i s) :
    WP isa (.block copyBody) s (CpInv s₀ s₂ Q t (i + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 i) 1 := by rw [h.rd, h.wr]; exact hsrc i hi
  have hout : InRegions s.wr (off (cx s₀) (576 + i)) 1 := by rw [h.wr, hwr]; exact hp.in_ctx (by lit_omega)
  have core : WP isa (.block copyBody) s fun s' =>
      s'.gpr .x1 = Q + BitVec.ofNat 64 (i + 1) ∧ s'.gpr .x9 = off (cx s₀) (576 + (i + 1)) ∧
      s'.gpr .x10 = BitVec.ofNat 64 (t - (i + 1)) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (off (cx s₀) (576 + i)) (s.mem (Q + BitVec.ofNat 64 i)) := by
    unfold copyBody
    refine wp_ldrb (a := Q + BitVec.ofNat 64 i) (by decide) (by rw [h.x1]; exact BitVec.add_zero _) hin
      fun s₁ u₁ => ?_
    refine wp_strb (a := off (cx s₀) (576 + i)) (by decide)
      (by rw [u₁.other _ (by decide), h.x9]; exact BitVec.add_zero _) (by rw [u₁.wr]; exact hout)
      fun s₂' g₂ => ?_
    refine wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ =>
      wp_subImm (by decide) fun s₅ u₅ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.x1,
        add_ofNat]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x9]
      exact add_ofNat _ _ _
    · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x10,
        sub_ofNat (by lit_omega), Nat.sub_sub]
    · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]
    · rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, byte_rt]
  refine WP.mono (WP.kept core (by simp [copyBody, dstOf, preserved]))
    fun s' ⟨⟨h1, h9, h10, hrd, hwr', hm⟩, hg, hsp⟩ => ⟨h1, h9, h10, fun r hr => by rw [hg r hr, h.keep r hr],
      by rw [hsp, h.sp], by rw [hrd, h.rd], by rw [hwr', h.wr], ?_, fun k hk => ?_⟩
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  · have hbyte : s.mem (Q + BitVec.ofNat 64 i) = s₂.mem (Q + BitVec.ofNat 64 i) :=
      h.frame _ fun r hr hc => hdisj i hi r hr _ (by
        simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
    rw [hm, writeW8_apply]
    by_cases hki : k = i
    · subst hki
      simp only [ite_true, show k < k + 1 by omega, hbyte]
    · simp only [off_ne (cx s₀) (a := 576 + k) (b := 576 + i) (by lit_omega) (by lit_omega) (by lit_omega), ite_false]
      rw [h.buf k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]

/-- The padded block's bytes. -/
theorem padded_bytes {s₀ : State} {m mz : Mem} {Q : Addr} {t : Nat} (ht : t < 16)
    (h : ∀ j < 16, m (off (cx s₀) (576 + j)) = if j < t then mz (Q + BitVec.ofNat 64 j) else 0) :
    bytesAt m (off (cx s₀) 576) 16 = bytesAt mz Q t ++ List.replicate (16 - t) 0 := by
  apply List.ext_getElem
  · simp [bytesAt]; omega
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [show off (cx s₀) 576 + BitVec.ofNat 64 k = off (cx s₀) (576 + k) from off_off _ _ _, h k h₁]
    by_cases hk : k < t
    · rw [List.getElem_append_left (by simp [hk])]
      simp [hk]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [hk]

/-- The frame of the Poly1305 state and the padded block. -/
abbrev macR (s₀ : State) : List Region := [sub s₀ 448 144]

theorem sub_mac (s₀ : State) {k n : Nat} (h₁ : 448 ≤ k) (h₂ : k + n ≤ 592) :
    Region.Sub (sub s₀ k n) (sub s₀ 448 144) := sub_sub s₀ h₁ (by lit_omega) (by lit_omega)

theorem kept_mac {s₀ s s' : State} {k n : Nat} (h₁ : 448 ≤ k) (h₂ : k + n ≤ 592)
    (hk : Kept [sub s₀ k n] s s') : Kept (macR s₀) s s' :=
  hk.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sub_mac s₀ h₁ h₂⟩

theorem kept_mac0 {s₀ s s' : State} (hk : Kept [] s s') : Kept (macR s₀) s s' :=
  hk.sub fun _ hr => absurd hr List.not_mem_nil

theorem padTail_eq : padTail =
    .seq (.block [.movz .x .x11 0 0, .str .x .x11 .x21 576, .str .x .x11 .x21 584, .addImm .x .x9 .x21 576])
    (.seq (.loop (.block copyBody) (.nonzero .x .x10))
    (.seq (.block [.addImm .x .x0 .x21 448, .addImm .x .x1 .x21 576, .movz .x .x2 1 0])
      (.call "vg_poly1305_blocks" Impl.Poly1305.AArch64.blocks))) := rfl

theorem padTail_ok {s₀ : State} (hp : APre s₀) {s : State} {Q : Addr} {t : Nat} (ht0 : 0 < t) (ht : t < 16)
    (hx1 : s.gpr .x1 = Q) (hx10 : s.gpr .x10 = BitVec.ofNat 64 t) (hx21 : s.gpr .x21 = cx s₀)
    (hwr : s.wr = s₀.wr)
    (hsrc : ∀ j < t, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint (sub s₀ 576 16)) :
    WP isa padTail s fun s' => Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ (bytesAt s.mem Q t ++ List.replicate (16 - t) 0)) := by
  rw [padTail_eq]
  refine WP.seq (WP.mono (WP.withSp (padZ_ok hp hx21 hwr)) fun s₂ ⟨⟨x9₂, g₂, rd₂, wr₂, f₂, z₂⟩, sp₂⟩ => ?_)
  have hd' : ∀ j < t, ∀ r ∈ [sub s₀ 576 16], (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint r := by
    intro j hj r hr; simp only [List.mem_singleton] at hr; subst hr; exact hdisj j hj
  have src₂ : ∀ j < t, s₂.mem (Q + BitVec.ofNat 64 j) = s.mem (Q + BitVec.ofNat 64 j) := fun j hj =>
    f₂ _ fun r hr hc => hd' j hj r hr _ (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
  refine WP.seq (WP.mono (Q := CpInv s₀ s₂ Q t t) ?_ fun s₃ h₃ => ?_)
  · let Inv : Nat → State → Prop := fun n s => ∃ i, n = t - i ∧ i < t ∧ CpInv s₀ s₂ Q t i s
    have hstep : ∀ n s, Inv n s → WP isa (.block copyBody) s (fun s' =>
        (isa.eval (.nonzero .x .x10) s' = some false ∧ CpInv s₀ s₂ Q t t s') ∨
        (isa.eval (.nonzero .x .x10) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨i, rfl, hi, hI⟩
      refine WP.mono (copy_step hp ht (by rw [wr₂, hwr]) (by rw [rd₂, wr₂]; exact hsrc) hd' hi hI)
        fun s' h' => ?_
      have hz := eval_nonzero_ofNat s' .x10 (by lit_omega) h'.x10
      by_cases hl : i + 1 = t
      · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ h'⟩
      · exact .inr ⟨by rw [hz]; simp; omega, t - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep t s₂ ⟨0, by simp, ht0, ⟨by rw [g₂ _ (by decide) (by decide), hx1]; simp,

      by rw [x9₂], by rw [g₂ _ (by decide) (by decide), hx10]; rfl, fun _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _, fun j hj => by simp [z₂ j hj]⟩⟩
  refine WP.seq (WP.mono (ptrs3_ok (a := 448) (b := 576) (by lit_omega) (by lit_omega) 1 s₃)
    fun s₄ ⟨h0, h1, h2, k₄⟩ => ?_)
  have x21₃ : s₃.gpr .x21 = cx s₀ := by
    rw [h₃.keep _ (by decide), g₂ _ (by decide) (by decide), hx21]
  rw [x21₃] at h0 h1
  have wr₄ : s₄.wr = s₀.wr := by rw [k₄.wr, h₃.wr, wr₂, hwr]
  have mm₄ : s₄.mem = s₃.mem := k₄.mem_eq
  refine blocks_call (n := 1) h0 h1 h2 (by lit_omega)
    (sub_disj s₀ (b := 576) (m := 16 * 1) (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [hp.off_toNat (by lit_omega)]; have := hp.wrap_c; omega)
    (covers2 hp wr₄ (a := 448) (n := 128) (b := 576) (m := 16 * 1) (by lit_omega) (by lit_omega))
    (covers1 hp wr₄ (a := 448) (n := 128) (by lit_omega)) fun s₅ k₅ repr₅ => ?_
  have k₃ : Kept [sub s₀ 576 16] s s₃ :=
    ⟨fun r hr h30 => by
        rw [h₃.keep r hr, g₂ r (by rintro rfl; simp [preserved] at hr) (by rintro rfl; simp [preserved] at hr)],
      by rw [h₃.sp, sp₂], by rw [h₃.rd, rd₂], by rw [h₃.wr, wr₂], f₂.trans h₃.frame⟩
  refine ⟨(kept_mac (by lit_omega) (by lit_omega) k₃).trans ((kept_mac0 k₄).trans (kept_mac (k := 448) (n := 128)
    (by lit_omega) (by lit_omega) k₅)), fun key msg hr => ?_⟩
  have f26 : Frame [sub s₀ 576 16] s.mem s₄.mem := by rw [mm₄]; exact k₃.frame
  have hr₄ : Repr s₄.mem (off (cx s₀) 448) key msg := Repr.frame f26 (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) hr
  have hb : bytesAt s₄.mem (off (cx s₀) 576) (16 * 1) = bytesAt s.mem Q t ++ List.replicate (16 - t) 0 := by
    rw [mm₄, show 16 * 1 = 16 from rfl, padded_bytes ht h₃.buf]
    refine congrArg (· ++ _) ?_
    simp only [bytesAt]
    apply List.map_congr_left
    intro j hj
    exact src₂ j (List.mem_range.mp hj)
  have := repr₅ key msg hr₄
  rwa [hb] at this

/-! ## The whole of `macPad` -/

theorem shr4_ofNat {len : Nat} (h : len < 2 ^ 64) : BitVec.ofNat 64 len >>> 4 = BitVec.ofNat 64 (len / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_lt h, toNat_ofNat_lt (by lit_omega), Nat.shiftRight_eq_div_pow]

theorem self_contains (a : Addr) : (⟨a, 1⟩ : Region).Contains a 1 := by
  simp only [Region.Contains]; rw [BitVec.sub_self]; simp

/-- The `len` bytes at `P` (in `p` and `n`), padded with zeros, absorbed. -/
theorem macPad_ok {s₀ : State} (hp : APre s₀) {p n : Reg} (hr : MacRegs p n) {P : Addr} {len : Nat}
    (hs : Src s₀ P len) {s : State} (hx21 : s.gpr .x21 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hP : s.gpr p = P) (hn : s.gpr n = BitVec.ofNat 64 len) :
    WP isa (macPad p n) s fun s' => Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ (bytesAt s.mem P len ++ pad16 (bytesAt s.mem P len))) := by
  have hpn := hr.p_ne
  have hnn := hr.n_ne
  have hcP : (ctxR s₀).Disjoint ⟨P, len⟩ := hs.ctx
  have hlt := hs.lt
  refine WP.seq (WP.mono (macA_ok hr s) fun s₁ ⟨x0₁, x1₁, x2₁, k₁⟩ => ?_)
  have hk : 16 * (len / 16) ≤ len := Nat.mul_div_le _ _
  refine WP.seq (blocks_call (P := off (cx s₀) 448) (p := P) (n := len / 16)
    (by rw [x0₁, hx21]) (by rw [x1₁, hP]) (by rw [x2₁, hn, shr4_ofNat hlt]) (by lit_omega)
    ((hcP.sub_left (sub_ctx s₀ (by lit_omega))).sub_right (Region.sub_prefix hk))
    (by have := hs.wrap; omega)
    (fun a w ⟨r, hr', hc⟩ => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · rw [k₁.rd, k₁.wr, hrd, hwr]
        exact hs.cov a w ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
      · exact covers1 hp (by rw [k₁.wr, hwr]) (a := 448) (n := 128) (by lit_omega) a w
          ⟨_, List.mem_singleton_self _, hc⟩ |> fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (covers1 hp (by rw [k₁.wr, hwr]) (a := 448) (n := 128) (by lit_omega))
    fun s₂ k₂ repr₂ => ?_)
  have m₁ := k₁.mem_eq
  rw [m₁] at repr₂
  refine WP.seq (WP.mono (macC_ok n s₂) fun s₃ ⟨x10₃, k₃⟩ => ?_)
  have n₂ : s₂.gpr n = BitVec.ofNat 64 len := by
    rw [k₂.cs n hnn.2.2.2.2.2.1 hnn.2.2.2.2.2.2, k₁.cs n hnn.2.2.2.2.2.1 hnn.2.2.2.2.2.2, hn]
  have p₂ : s₂.gpr p = P := by
    rw [k₂.cs p hpn.2.2.2.2.2.1 hpn.2.2.2.2.2.2, k₁.cs p hpn.2.2.2.2.2.1 hpn.2.2.2.2.2.2, hP]
  rw [n₂, toNat_ofNat_lt hlt] at x10₃
  have k₁₃ : Kept (macR s₀) s s₃ :=
    (kept_mac0 k₁).trans ((kept_mac (k := 448) (n := 128) (by lit_omega) (by lit_omega) k₂).trans (kept_mac0 k₃))
  have x_eq : bytesAt s.mem P len = bytesAt s.mem P (16 * (len / 16)) ++
      bytesAt s.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, Nat.div_add_mod]
  have hlen : (bytesAt s.mem P len).length = len := VG.Proof.Poly1305.length_bytesAt _ _ _
  have m₃ := k₃.mem_eq
  refine WP.ite (decide (len % 16 = 0)) (by
      have e : isa.eval (.zero .x .x10) s₃ = some (s₃.gpr .x10 == 0) := eval_zero s₃ .x10
      rw [e, x10₃, ofNat_beq_zero (by lit_omega)]) (fun h => ?_) (fun h => ?_)
  · -- A multiple of 16: nothing to pad.
    have h0 : len % 16 = 0 := by simpa using h
    refine WP.block_nil ⟨k₁₃, fun key msg hr => ?_⟩
    rw [m₃]
    have := repr₂ key msg hr
    rwa [show pad16 (bytesAt s.mem P len) = [] by simp [pad16, hlen, h0], List.append_nil,
      ← show 16 * (len / 16) = len by omega]
  · have h0 : len % 16 ≠ 0 := by simpa using h
    refine WP.seq (WP.mono (macD_ok hr s₃) fun s₄ ⟨x1₄, g₄, k₄⟩ => ?_)
    have hQ : s₄.gpr .x1 = P + BitVec.ofNat 64 (16 * (len / 16)) := by
      rw [x1₄, x10₃, k₃.cs n hnn.2.2.2.2.2.1 hnn.2.2.2.2.2.2, n₂, k₃.cs p hpn.2.2.2.2.2.1 hpn.2.2.2.2.2.2, p₂,
        sub_ofNat (by lit_omega), show len - len % 16 = 16 * (len / 16) by omega]
    have hsrc : ∀ j < len % 16, InRegions (s₄.rd ++ s₄.wr)
        (P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j) 1 := fun j hj => by
      rw [add_ofNat]
      exact hs.cov_sub (a := 16 * (len / 16) + j) (n := 1) (by lit_omega)
        (by rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd, hrd]) (by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr, hwr]) _ _
        ⟨_, List.mem_singleton_self _, self_contains _⟩
    have hdj : ∀ j < len % 16, (⟨P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j, 1⟩ :
        Region).Disjoint (sub s₀ 576 16) := fun j hj => by
      rw [add_ofNat]
      exact (Src.disj_sub (hcP.sub_left (sub_ctx s₀ (by lit_omega))) (a := 16 * (len / 16) + j) (n := 1)
        (by lit_omega)).symm
    refine WP.mono (padTail_ok hp (Q := P + BitVec.ofNat 64 (16 * (len / 16))) (t := len % 16)
      (by lit_omega) (by lit_omega) hQ
      (by rw [g₄ _ (by decide) (by decide), x10₃])
      (by rw [k₄.cs _ (pres .x21) (pres30 .x21), k₃.cs _ (pres .x21) (pres30 .x21),
        k₂.cs _ (pres .x21) (pres30 .x21), k₁.cs _ (pres .x21) (pres30 .x21), hx21])
      (by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr, hwr])
      hsrc hdj) fun s₅ ⟨k₅, repr₅⟩ => ?_

    refine ⟨k₁₃.trans ((kept_mac0 k₄).trans k₅), fun key msg hr => ?_⟩
    have m₄ := k₄.mem_eq
    have := repr₅ key _ (by rw [m₄, m₃]; exact repr₂ key msg hr)
    rw [m₄, m₃, bytesAt_frame k₂.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((hcP.sub_left (sub_ctx s₀ (by lit_omega))).sub_right
          (sub_off P (a := 16 * (len / 16)) (by lit_omega))).symm) (by lit_omega), m₁] at this

    rw [show pad16 (bytesAt s.mem P len) = List.replicate (16 - len % 16) 0 by simp [pad16, hlen, h0],
      x_eq]
    simpa only [List.append_assoc] using this

end VG.Proof.ChaCha20Poly1305.AArch64

/-!
# ChaCha20-Poly1305 on AArch64: the other parts

Untrusted: everything here is checked by Lean. The lengths block, the
encryption, absorbing the lengths, the tag, comparing tags, and restoring the
registers.
-/

open VG.PowLit

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd wp_addImm wp_mov wp_movz wp_sub wp_lsr wp_str wp_str32 wp_ldr
  stateAt_writeW_counter)
open VG.Proof.ChaCha20.AArch64 (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream)

theorem mac_inv {s₀ s s' : State} (h : Inv s₀ s) (hk : Kept (macR s₀) s s') : Inv s₀ s' :=
  h.step1 (k := 448) (n := 144) hk (by lit_omega) (by lit_omega) (by lit_omega)

/-! ## The lengths block -/

theorem bytesAt_16 (m : Mem) (p : Addr) :
    bytesAt m p 16 = leBytes 8 (m.readW p 64).toNat ++ leBytes 8 (m.readW (off p 8) 64).toNat := by
  rw [show 16 = 8 + 8 from rfl, VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.bytesAt_leBytes_64,
    VG.Proof.Poly1305.bytesAt_leBytes_64]

theorem lengths_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block lengths) s fun s' => Inv s₀ s' ∧ Kept [sub s₀ 656 16] s s' ∧
      bytesAt s'.mem (off (cx s₀) 656) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
  have o0 := hp.in_ctx (a := 656) (w := 8) (by lit_omega)
  have o1 := hp.in_ctx (a := 664) (w := 8) (by lit_omega)
  rw [← h.wr] at o0 o1
  have core : WP isa (.block lengths) s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = (s.mem.writeW (off (cx s₀) 656) (s.gpr .x25)).writeW (off (cx s₀) 664) (s.gpr .x23) :=
    wp_str (a := off (cx s₀) 656) (by decide) (by rw [h.x21]) o0 fun s₁ g₁ =>
      wp_str (a := off (cx s₀) 664) (by decide) (by rw [g₁.gpr, h.x21]) (by rw [g₁.wr]; exact o1)
        fun s₂ g₂ => WP.block_nil ⟨by rw [g₂.rd, g₁.rd], by rw [g₂.wr, g₁.wr], by rw [g₂.mem, g₁.gpr, g₁.mem]⟩
  refine WP.mono (WP.kept core (by simp [lengths, dstOf, preserved])) fun s' ⟨⟨hrd, hwr, hm⟩, hg, hsp⟩ => ?_
  have hk : Kept [sub s₀ 656 16] s s' := Kept.of hg hsp hrd hwr (by
    rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)))
  refine ⟨h.step1 hk (by lit_omega) (by lit_omega) (by lit_omega), hk, ?_⟩
  rw [bytesAt_16, off_off, show 656 + 8 = 664 from rfl, hm, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    Mem.readW_writeW_self64, Mem.readW_writeW_self64, h.x25, h.x23]

/-! ## Encrypting -/

theorem set12_initState (key nonce : List Byte) :
    (Spec.ChaCha20.initState key 0 nonce).set 12 1 = Spec.ChaCha20.initState key 1 nonce := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_set, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  by_cases h : 12 = i
  · subst h; simp
  · simp only [h, ite_false, show ¬ i = 12 from fun h' => h h'.symm]

theorem one32 : ((((1 : BitVec 16).setWidth 32).setWidth 64).setWidth 32 : BitVec 32) = 1 := rfl

theorem cryptA_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block [.movz .w .x9 1 0, .str .w .x9 .x21 112, .addImm .x .x0 .x21 64, mov .x1 .x22,
      mov .x2 .x23, .addImm .x .x3 .x21 128]) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x1 = dp s₀ ∧ s'.gpr .x2 = s₀.gpr .x4 ∧ s'.gpr .x3 = off (cx s₀) 128 ∧
      Kept [sub s₀ 64 64] s s' := by
  have o := hp.in_ctx (a := 112) (w := 4) (by lit_omega)
  rw [← h.wr] at o
  have core : WP isa (.block [.movz .w .x9 1 0, .str .w .x9 .x21 112, .addImm .x .x0 .x21 64, mov .x1 .x22,
      mov .x2 .x23, .addImm .x .x3 .x21 128]) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.gpr .x0 = off (cx s₀) 64 ∧
      s'.gpr .x1 = dp s₀ ∧ s'.gpr .x2 = s₀.gpr .x4 ∧ s'.gpr .x3 = off (cx s₀) 128 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine wp_movz32 fun s₁ u₁ => ?_
    refine wp_str32 (a := off (cx s₀) 112) (by decide) (by rw [u₁.other _ (by decide), h.x21])
      (by rw [u₁.wr]; exact o) fun s₂ g₂ => ?_
    refine wp_addImm (by decide) fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
      wp_addImm (by decide) fun s₆ u₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, one32]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr,
        u₁.other _ (by decide), h.x21]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), h.x22]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), h.x23]
    · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr,
        u₁.other _ (by decide), h.x21]
    · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd]
    · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr]
  refine WP.mono (WP.kept core (by simp [mov, dstOf, preserved]))
    fun s' ⟨⟨hm, h0, h1, h2, h3, hrd, hwr⟩, hg, hsp⟩ => ⟨hm, h0, h1, h2, h3, Kept.of hg hsp hrd hwr ?_⟩
  rw [hm]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))

theorem hL (s₀ : State) : s₀.gpr .x4 = BitVec.ofNat 64 (L s₀) := by simp [L]

/-- The data encrypted (or decrypted) from block counter 1. -/
theorem crypt_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)) :
    WP isa crypt s fun s' => Inv s₀ s' ∧ Kept [sub s₀ 64 384, dR s₀] s s' ∧
      bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  refine WP.seq (WP.mono (cryptA_ok hp h) fun s₁ ⟨m₁, x0₁, x1₁, x2₁, x3₁, k₁⟩ => ?_)
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, h.wr]
  have hw : Covers [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀, L s₀⟩, ⟨off (cx s₀) 128, 320⟩] s₁.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by simp [wr₁, hp.wr], 64, rfl, by show 64 + 64 ≤ 1024; omega⟩
    · exact ⟨dR s₀, by simp [wr₁, hp.wr], 0, by simp, by simp⟩
    · exact ⟨ctxR s₀, by simp [wr₁, hp.wr], 128, rfl, by show 128 + 320 ≤ 1024; omega⟩
  refine xor_call x0₁ x1₁ (by rw [x2₁]; exact hL s₀) x3₁ (s₀.gpr .x4).isLt
    (hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega)))
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))) hp.wrap_d
    (covers_nil_append (covers_left _ hw)) hw fun s₂ k₂ data₂ => ?_
  have hsub : ∀ r ∈ [sub s₀ 64 384, dR s₀], ∃ r' ∈ [workR s₀, dR s₀], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨dR s₀, by simp, fun _ h => h⟩
  have hk : Kept [sub s₀ 64 384, dR s₀] s s₂ := by
    refine (k₁.sub fun r hr => ?_).trans (k₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  refine ⟨h.step hk hsub (fun r hr => ?_), hk, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
  · have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) :=
      bytesAt_frame k₁.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).symm) (Nat.le_of_lt (s₀.gpr .x4).isLt)
    have st₁ : stateAt s₁.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
      rw [m₁, show off (cx s₀) 112 = off (cx s₀) 64 + BitVec.ofNat 64 48 from (off_off _ 64 48).symm,
        stateAt_writeW_counter, hst, set12_initState]
    rw [← bytesAt_eq, data₂, st₁, bytesAt_eq, d₁, encrypt_eq, VG.Proof.Poly1305.length_bytesAt]

/-! ## Absorbing the lengths and the tag -/

/-- The lengths block absorbed. -/
theorem absorbLengths_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa absorbLengths s fun s' => Inv s₀ s' ∧ Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s.mem (off (cx s₀) 656) 16) := by
  unfold absorbLengths
  refine WP.seq (WP.mono (ptrs3_ok (a := 448) (b := 656) (by lit_omega) (by lit_omega) 1 s)
    fun s₁ ⟨h0, h1, h2, k₁⟩ => ?_)
  rw [h.x21] at h0 h1
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, h.wr]
  have m₁ := k₁.mem_eq
  refine blocks_call (n := 1) h0 h1 h2 (by lit_omega)
    (sub_disj s₀ (b := 656) (m := 16 * 1) (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [hp.off_toNat (by lit_omega)]; have := hp.wrap_c; omega)
    (covers2 hp wr₁ (a := 448) (n := 128) (b := 656) (m := 16 * 1) (by lit_omega) (by lit_omega))
    (covers1 hp wr₁ (a := 448) (n := 128) (by lit_omega)) fun s₂ k₂ repr₂ => ?_
  have hk : Kept (macR s₀) s s₂ := (kept_mac0 k₁).trans (kept_mac (k := 448) (n := 128) (by lit_omega) (by lit_omega) k₂)
  exact ⟨mac_inv h hk, hk, fun key msg hr => by rw [← m₁]; exact repr₂ key msg (by rw [m₁]; exact hr)⟩

/-- `x0 = x21 + 448`, `x1 = 0`, `x2 = x21 + out` and `x3 = x21 + 672`. -/
theorem fptrs_ok {out : Nat} (ho : out < 4096) (s : State) :
    WP isa (.block [.addImm .x .x0 .x21 448, .movz .x .x1 0 0, .addImm .x .x2 .x21 out,
      .addImm .x .x3 .x21 672]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) 448 ∧ s'.gpr .x1 = 0 ∧ s'.gpr .x2 = off (s.gpr .x21) out ∧
      Kept [] s s' := by
  have h : WP isa (.block [.addImm .x .x0 .x21 448, .movz .x .x1 0 0, .addImm .x .x2 .x21 out,
      .addImm .x .x3 .x21 672]) s fun s' =>
      s'.gpr .x0 = off (s.gpr .x21) 448 ∧ s'.gpr .x1 = 0 ∧ s'.gpr .x2 = off (s.gpr .x21) out ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem :=
    wp_addImm (by decide) fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_addImm ho fun s₃ u₃ =>
      wp_addImm (by decide) fun s₄ u₄ => WP.block_nil
      ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
        by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl,
        by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)],
        by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr],
        by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept h (by simp [dstOf, preserved]))
    fun s' ⟨⟨h0, h1, h2, hrd, hwr, hm⟩, hg, hsp⟩ =>
      ⟨h0, h1, h2, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- The tag written to `ctx[out, out + 16)`. -/
theorem finalizeTo_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) {out : Nat}
    (hout : out + 16 ≤ 448 ∨ (640 ≤ out ∧ out + 16 ≤ 656)) :
    WP isa (finalizeTo out) s fun s' => Kept [sub s₀ 448 128, sub s₀ out 16] s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg → bytesAt s'.mem (off (cx s₀) out) 16 = mac key msg := by
  unfold finalizeTo
  refine WP.seq (WP.mono (fptrs_ok (out := out) (by lit_omega) s) fun s₁ ⟨h0, h1, h2, k₁⟩ => ?_)
  rw [h.x21] at h0 h2
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, h.wr]
  have m₁ := k₁.mem_eq
  have ho : out + 16 ≤ 1024 := by omega
  refine finalize_call h0 h1 h2 (sub_disj s₀ (by lit_omega) (by lit_omega) ho)
    (covers_left _ (covers_sub hp wr₁ _ (by
      intro r hr; simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩
      · exact ⟨out, rfl, ho⟩)))
    (covers_sub hp wr₁ _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩
      · exact ⟨out, rfl, ho⟩))
    fun s₂ k₂ tag₂ => ?_
  exact ⟨(k₁.sub fun _ hr => absurd hr List.not_mem_nil).trans k₂,
    fun key msg hr => tag₂ key msg (by rw [m₁]; exact hr)⟩

/-! ## Restoring the registers -/

theorem restore_eq : restore =
    [.ldr .x .x22 .x21 600, .ldr .x .x23 .x21 608, .ldr .x .x24 .x21 616, .ldr .x .x25 .x21 624,
     .ldr .x .x30 .x21 632, .ldr .x .x21 .x21 592] := rfl

theorem restore_ok {s₀ : State} (hp : APre s₀) {s : State} (hx21 : s.gpr .x21 = cx s₀)
    (hsv : Saved s₀ s.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' =>
      ((∀ r ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x30], s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ [Reg.x21, .x22, .x23, .x24, .x25, .x30] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem) ∧ s'.sp = s.sp := by
  have i : ∀ d, d + 8 ≤ 1024 → InRegions (s.rd ++ s.wr) (off (cx s₀) d) 8 := fun d h => by
    rw [hrd, hwr]; exact hp.in_ctx' h
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hsv
  rw [restore_eq]
  refine WP.withSp ?_
  refine wp_ldr (a := off (cx s₀) 600) (by decide) (by rw [hx21]) (i 600 (by lit_omega)) fun s₁ u₁ => ?_
  refine wp_ldr (a := off (cx s₀) 608) (by decide) (by rw [u₁.other _ (by decide), hx21])
    (by rw [u₁.rd, u₁.wr]; exact i 608 (by lit_omega)) fun s₂ u₂ => ?_
  refine wp_ldr (a := off (cx s₀) 616) (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hx21])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i 616 (by lit_omega)) fun s₃ u₃ => ?_
  refine wp_ldr (a := off (cx s₀) 624) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx21])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i 624 (by lit_omega)) fun s₄ u₄ => ?_
  refine wp_ldr (a := off (cx s₀) 632) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx21])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i 632 (by lit_omega)) fun s₅ u₅ => ?_
  refine wp_ldr (a := off (cx s₀) 592) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hx21])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i 592 (by lit_omega))
    fun s₆ u₆ => WP.block_nil ?_
  have hm₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨fun r hr => ?_, fun r hr => ?_, by rw [u₆.mem, hm₅]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₆.gpr, hm₅, v1]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, v2]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.mem, v3]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, v4]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem, v5]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v6]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h21, h22, h23, h24, h25, h30⟩ := hr
    rw [u₆.other _ h21, u₅.other _ h30, u₄.other _ h25, u₃.other _ h24, u₂.other _ h23, u₁.other _ h22]

/-! ## Comparing the tags -/

theorem bytesAt_8_eq {m : Mem} {p q : Addr} :
    bytesAt m p 8 = bytesAt m q 8 ↔ m.readW p 64 = m.readW q 64 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [← VG.Proof.Poly1305.leNum_bytesAt_64, ← VG.Proof.Poly1305.leNum_bytesAt_64, h]
  · intro h
    rw [VG.Proof.Poly1305.bytesAt_leBytes_64, VG.Proof.Poly1305.bytesAt_leBytes_64, h]

/-- The tags differ in no bit if and only if they are equal. -/
theorem tag_eq (m : Mem) (p q : Addr) :
    ((m.readW p 64 ^^^ m.readW q 64) ||| (m.readW (off p 8) 64 ^^^ m.readW (off q 8) 64)) = 0#64 ↔
      bytesAt m p 16 = bytesAt m q 16 := by
  rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff, show 16 = 8 + 8 from rfl,
    VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.bytesAt_add, ← bytesAt_8_eq, ← bytesAt_8_eq]
  constructor
  · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
  · intro h
    exact List.append_inj h (by rw [VG.Proof.Poly1305.length_bytesAt, VG.Proof.Poly1305.length_bytesAt])

/-- `(x | -x) >> 63` is 0 if `x = 0` and 1 otherwise. -/
theorem nz_bit (x : BitVec 64) : (x ||| (0 - x)) >>> 63 = if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · subst h; rfl
  · simp only [h, ↓reduceIte]
    have hx : x.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    have hlt := x.isLt
    have hneg : (0 - x).toNat = 2 ^ 64 - x.toNat := by
      rw [BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl]; omega
    have h1 : 2 ^ 63 ≤ (x ||| (0 - x)).toNat := by
      rw [BitVec.toNat_or]
      rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h2 | h2
      · exact Nat.le_trans (by lit_omega) (Nat.right_le_or (n := x.toNat))
      · exact Nat.le_trans h2 Nat.left_le_or
    have h2 := (x ||| (0 - x)).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (1 : BitVec 64).toNat = 1 from rfl]
    omega

theorem sel_eq {x : BitVec 64} {p : Prop} [Decidable p] (h : x = 0 ↔ p) :
    ((1 : BitVec 64) - if x = 0 then 0 else 1).setWidth 32 = if p then 1 else 0 := by
  by_cases hp : p
  · have hx : x = 0 := h.mpr hp
    simp only [hx, hp, ↓reduceIte]
    decide
  · have hx : ¬ x = 0 := fun e => hp (h.mp e)
    simp only [hx, hp, ↓reduceIte]
    decide


theorem compare_ok
 {s₀ : State} (hp : APre s₀) {s : State} (hx21 : s.gpr .x21 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block Impl.ChaCha20Poly1305.AArch64.compare) s fun s' =>
      (s'.gpr .x0).setWidth 32 =
        (if bytesAt s.mem (off (cx s₀) 640) 16 = bytesAt s.mem (off (cx s₀) 48) 16 then 1 else 0) ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have i : ∀ d, d + 8 ≤ 1024 → InRegions (s.rd ++ s.wr) (off (cx s₀) d) 8 := fun d h => by
    rw [hrd, hwr]; exact hp.in_ctx' h
  have core : WP isa (.block Impl.ChaCha20Poly1305.AArch64.compare) s fun s' =>
      s'.gpr .x0 = BitVec.ofNat 64 1 - ((s.mem.readW (off (cx s₀) 640) 64 ^^^ s.mem.readW (off (cx s₀) 48) 64) |||
        (s.mem.readW (off (cx s₀) 648) 64 ^^^ s.mem.readW (off (cx s₀) 56) 64) |||
        (0 - ((s.mem.readW (off (cx s₀) 640) 64 ^^^ s.mem.readW (off (cx s₀) 48) 64) |||
        (s.mem.readW (off (cx s₀) 648) 64 ^^^ s.mem.readW (off (cx s₀) 56) 64)))) >>> 63 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    unfold Impl.ChaCha20Poly1305.AArch64.compare
    refine wp_ldr (a := off (cx s₀) 640) (by decide) (by rw [hx21]) (i 640 (by lit_omega)) fun s₁ u₁ => ?_
    refine wp_ldr (a := off (cx s₀) 48) (by decide) (by rw [u₁.other _ (by decide), hx21])
      (by rw [u₁.rd, u₁.wr]; exact i 48 (by lit_omega)) fun s₂ u₂ => ?_
    refine wp_eor fun s₃ u₃ => ?_
    refine wp_ldr (a := off (cx s₀) 648) (by decide)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx21])
      (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i 648 (by lit_omega)) fun s₄ u₄ => ?_
    refine wp_ldr (a := off (cx s₀) 56) (by decide)
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
        hx21])
      (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i 56 (by lit_omega)) fun s₅ u₅ => ?_
    refine wp_eor fun s₆ u₆ => wp_orr fun s₇ u₇ => wp_movz fun s₈ u₈ => wp_sub fun s₉ u₉ =>
      wp_orr fun s₁₀ u₁₀ => wp_lsr (by decide) fun s₁₁ u₁₁ => wp_movz fun s₁₂ u₁₂ =>
      wp_sub fun s₁₃ u₁₃ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
    · have x9₃ : s₃.gpr .x9 = s.mem.readW (off (cx s₀) 640) 64 ^^^ s.mem.readW (off (cx s₀) 48) 64 := by
        rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem]
      have x10₆ : s₆.gpr .x10 = s.mem.readW (off (cx s₀) 648) 64 ^^^ s.mem.readW (off (cx s₀) 56) 64 := by
        rw [u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
      have x9₇ : s₇.gpr .x9 = (s.mem.readW (off (cx s₀) 640) 64 ^^^ s.mem.readW (off (cx s₀) 48) 64) |||
          (s.mem.readW (off (cx s₀) 648) 64 ^^^ s.mem.readW (off (cx s₀) 56) 64) := by
        rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), x9₃, x10₆]
      rw [u₁₃.gpr, u₁₂.gpr, u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.gpr, u₉.other _ (by decide), u₉.gpr,
        u₈.other _ (by decide), u₈.gpr, x9₇]
      rfl

    · rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem,
        u₁.mem]
    · rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine WP.mono (WP.kept core (by simp [Impl.ChaCha20Poly1305.AArch64.compare, dstOf, preserved]))
    fun s' ⟨⟨h0, hm, hrd', hwr'⟩, hg, hsp⟩ => ⟨?_, hg, hsp, hm, hrd', hwr'⟩
  have ht := tag_eq s.mem (off (cx s₀) 640) (off (cx s₀) 48)
  simp only [off_off, Nat.reduceAdd] at ht
  rw [h0, nz_bit]
  exact sel_eq ht




end VG.Proof.ChaCha20Poly1305.AArch64
