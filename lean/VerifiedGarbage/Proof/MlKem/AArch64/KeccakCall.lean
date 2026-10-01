import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.MlKem.AArch64.Wp

/-!
# ML-KEM on AArch64: calling the Keccak functions

Untrusted: everything here is checked by Lean. Each call of the verified
`vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze`, from its proof
(with `WP.callF`: they save `x30` in a frame): what it needs of the state
it is called from, and what holds when it returns (`Kept`: only the regions
it may write and its frame's 16 bytes below the stack pointer change, and
the callee-saved registers but `x30` are kept).
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64
open VG.Spec.Sha3 (Repr stateAt bytesAt absorb pad squeezeFrom rates)

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are not callee-saved (or are `x30`). -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem
  vcs : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-- The 16 bytes below the stack pointer, where a callee saves `x30`. -/
abbrev stk (s : State) : Region := ⟨s.sp - 16, 16⟩

theorem absorb_fdepth : Impl.Sha3.AArch64.Stream.absorb.aarch64Depth = 1 := by decide +kernel
theorem pad_fdepth : Impl.Sha3.AArch64.Stream.pad.aarch64Depth = 1 := by decide +kernel
theorem squeeze_fdepth : Impl.Sha3.AArch64.Stream.squeeze.aarch64Depth = 1 := by decide +kernel

theorem frame3 {a b c : Region} {m m' : Mem} (h : Frame ([a, b] ++ [c]) m m') : Frame [a, b, c] m m' := h

theorem frame4 {a b c d : Region} {m m' : Mem} (h : Frame ([a, b, c] ++ [d]) m m') :
    Frame [a, b, c, d] m m' := h

theorem gpr_entry (s : State) {r : Reg} (h : r ∉ linkRegs := by decide) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr s h

/-- `vg_keccak_absorb(st, rate, pos, dt, len, sc)`. -/
theorem absorb_call {s : State} {st dt sc : Addr} {rate pos len : Nat}
    (h0 : s.gpr .x0 = st) (h1 : (s.gpr .x1).toNat = rate) (h2 : (s.gpr .x2).toNat = pos)
    (h3 : s.gpr .x3 = dt) (h4 : (s.gpr .x4).toNat = len) (h5 : s.gpr .x5 = sc)
    (hr : rate ∈ rates) (hp : pos < rate)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩) (d₂ : Region.Disjoint ⟨dt, len⟩ ⟨st, 200⟩)
    (d₃ : Region.Disjoint ⟨dt, len⟩ ⟨sc, 640⟩) (hsp : 16 ≤ s.sp.toNat)
    (k₁ : (stk s).Disjoint ⟨st, 200⟩) (k₂ : (stk s).Disjoint ⟨dt, len⟩)
    (k₃ : (stk s).Disjoint ⟨sc, 640⟩)
    (hc : Covers [⟨dt, len⟩, ⟨st, 200⟩, ⟨sc, 640⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨sc, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨st, 200⟩, ⟨sc, 640⟩, below s.sp 16] s s' →
      (∀ msg, Repr s.mem st rate msg → pos = msg.length % rate →
        Repr s'.mem st rate (msg ++ bytesAt s.mem dt len)) →
      (s'.gpr .x0).toNat = (pos + len) % rate → Q s') :
    WP isa (.call "vg_keccak_absorb" Impl.Sha3.AArch64.Stream.absorb) s Q := by
  have c0 : s.callEntry.gpr .x0 = st := (gpr_entry s).trans h0
  have c1 : (s.callEntry.gpr .x1).toNat = rate := by rw [gpr_entry s]; exact h1
  have c2 : (s.callEntry.gpr .x2).toNat = pos := by rw [gpr_entry s]; exact h2
  have c3 : s.callEntry.gpr .x3 = dt := (gpr_entry s).trans h3
  have c4 : (s.callEntry.gpr .x4).toNat = len := by rw [gpr_entry s]; exact h4
  have c5 : s.callEntry.gpr .x5 = sc := (gpr_entry s).trans h5
  refine WP.callFV (k := Proof.Sha3.absorbAArch64) Proof.Sha3.AArch64.Stream.Absorb.absorb_correct
    (rd := [⟨dt, len⟩]) (wr := [⟨st, 200⟩, ⟨sc, 640⟩]) ?_ hc hw ?_ (by rw [absorb_fdepth]; decide)
  · simp only [Proof.Sha3.absorbAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c1, c2, c3, c4, c5]
    exact ⟨trivial, trivial, d₁, d₂, d₃, hsp, k₁, k₂, k₃, hr, hp⟩
  · intro s' hrd hwr hsp' hf hcs hv hpost
    rw [absorb_fdepth, Nat.mul_one] at hf
    simp only [Proof.Sha3.absorbAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, c3, c4] at hpost
    exact hQ s' ⟨hcs, hsp', hrd, hwr, frame3 hf, hv⟩ hpost.1 hpost.2

/-- `vg_keccak_pad(st, rate, pos, suffix, sc)`. -/
theorem pad_call {s : State} {st sc : Addr} {rate pos : Nat}
    (h0 : s.gpr .x0 = st) (h1 : (s.gpr .x1).toNat = rate) (h2 : (s.gpr .x2).toNat = pos)
    (h4 : s.gpr .x4 = sc) (hr : rate ∈ rates) (hp : pos < rate)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩) (hsp : 16 ≤ s.sp.toNat)
    (k₁ : (stk s).Disjoint ⟨st, 200⟩) (k₃ : (stk s).Disjoint ⟨sc, 640⟩)
    (hc : Covers [⟨st, 200⟩, ⟨sc, 640⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨sc, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨st, 200⟩, ⟨sc, 640⟩, below s.sp 16] s s' →
      (∀ msg, Repr s.mem st rate msg → pos = msg.length % rate →
        stateAt s'.mem st = absorb rate (pad rate ((s.gpr .x3).setWidth 8) msg)) → Q s') :
    WP isa (.call "vg_keccak_pad" Impl.Sha3.AArch64.Stream.pad) s Q := by
  have c0 : s.callEntry.gpr .x0 = st := (gpr_entry s).trans h0
  have c1 : (s.callEntry.gpr .x1).toNat = rate := by rw [gpr_entry s]; exact h1
  have c2 : (s.callEntry.gpr .x2).toNat = pos := by rw [gpr_entry s]; exact h2
  have c3 : s.callEntry.gpr .x3 = s.gpr .x3 := gpr_entry s
  have c4 : s.callEntry.gpr .x4 = sc := (gpr_entry s).trans h4
  refine WP.callFV (k := Proof.Sha3.padAArch64) Proof.Sha3.AArch64.Stream.Pad.pad_correct
    (rd := []) (wr := [⟨st, 200⟩, ⟨sc, 640⟩]) ?_ hc hw ?_ (by rw [pad_fdepth]; decide)
  · simp only [Proof.Sha3.padAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c1, c2, c4]
    exact ⟨trivial, trivial, d₁, hsp, k₁, k₃, hr, hp⟩
  · intro s' hrd hwr hsp' hf hcs hv hpost
    rw [pad_fdepth, Nat.mul_one] at hf
    simp only [Proof.Sha3.padAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, c3] at hpost
    exact hQ s' ⟨hcs, hsp', hrd, hwr, frame3 hf, hv⟩ hpost

/-- `vg_keccak_squeeze(st, rate, pos, out, len, sc)`. -/
theorem squeeze_call {s : State} {st out sc : Addr} {rate pos len : Nat}
    (h0 : s.gpr .x0 = st) (h1 : (s.gpr .x1).toNat = rate) (h2 : (s.gpr .x2).toNat = pos)
    (h3 : s.gpr .x3 = out) (h4 : (s.gpr .x4).toNat = len) (h5 : s.gpr .x5 = sc)
    (hr : rate ∈ rates) (hp : pos ≤ rate)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨out, len⟩) (d₂ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩)
    (d₃ : Region.Disjoint ⟨out, len⟩ ⟨sc, 640⟩) (hsp : 16 ≤ s.sp.toNat)
    (k₁ : (stk s).Disjoint ⟨st, 200⟩) (k₂ : (stk s).Disjoint ⟨out, len⟩)
    (k₃ : (stk s).Disjoint ⟨sc, 640⟩)
    (hc : Covers [⟨st, 200⟩, ⟨out, len⟩, ⟨sc, 640⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨out, len⟩, ⟨sc, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨st, 200⟩, ⟨out, len⟩, ⟨sc, 640⟩, below s.sp 16] s s' →
      bytesAt s'.mem out len = squeezeFrom rate (stateAt s.mem st) pos len →
      (s'.gpr .x0).toNat ≤ rate →
      (∀ d, squeezeFrom rate (stateAt s'.mem st) (s'.gpr .x0).toNat d =
        squeezeFrom rate (stateAt s.mem st) (pos + len) d) → Q s') :
    WP isa (.call "vg_keccak_squeeze" Impl.Sha3.AArch64.Stream.squeeze) s Q := by
  have c0 : s.callEntry.gpr .x0 = st := (gpr_entry s).trans h0
  have c1 : (s.callEntry.gpr .x1).toNat = rate := by rw [gpr_entry s]; exact h1
  have c2 : (s.callEntry.gpr .x2).toNat = pos := by rw [gpr_entry s]; exact h2
  have c3 : s.callEntry.gpr .x3 = out := (gpr_entry s).trans h3
  have c4 : (s.callEntry.gpr .x4).toNat = len := by rw [gpr_entry s]; exact h4
  have c5 : s.callEntry.gpr .x5 = sc := (gpr_entry s).trans h5
  refine WP.callFV (k := Proof.Sha3.squeezeAArch64) Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct
    (rd := []) (wr := [⟨st, 200⟩, ⟨out, len⟩, ⟨sc, 640⟩]) ?_ hc hw ?_
    (by rw [squeeze_fdepth]; decide)
  · simp only [Proof.Sha3.squeezeAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c1, c2, c3, c4, c5]
    exact ⟨trivial, trivial, d₁, d₂, d₃, hsp, k₁, k₂, k₃, hr, hp⟩
  · intro s' hrd hwr hsp' hf hcs hv hpost
    rw [squeeze_fdepth, Nat.mul_one] at hf
    simp only [Proof.Sha3.squeezeAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, c3, c4] at hpost
    exact hQ s' ⟨hcs, hsp', hrd, hwr, frame4 hf, hv⟩ hpost.1 hpost.2.1 hpost.2.2

end VG.Proof.MlKem.AArch64
