import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Impl.Blake2.X86.CompressS

/-!
# BLAKE2s on x86 (32-bit): the rounds

Untrusted: everything here is checked by Lean. `g_ok` executes `G`
symbolically once, for any words of the work vector (in `scratch`, at `esi`)
and of the block (at `edi`); `round_ok` and `rounds_ok` compose it into the
rounds of `F`. `Holds` says that the work vector is in `scratch`, `Msg` that
the block is at `edi`.
-/

namespace VG.Proof.Blake2.X86.CompressS

open VG VG.X86 VG.X86.Wp
open VG.Spec.Blake2 (Work Block G sigmaAt)
open VG.Proof.Blake2 (mix G_get)
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.CompressS
open VG.Proof.MdStream.X86 (contains_addr readW_writeW_addr)

/-- The work vector `v` is at `B`: word `k` at `[B + 4k]`. -/
def Holds (B : BitVec 32) (v : Work 32) (m : Mem) : Prop :=
  ∀ k (hk : k < 16), m.readW (addr B (vOff k)) 32 = v[k]

/-- The block `M` is at `K`: word `j` at `[K + 4j]`. -/
def Msg (K : BitVec 32) (M : Block 32) (m : Mem) : Prop :=
  ∀ j : Fin 16, m.readW (addr K (4 * j.val)) 32 = M j

/-- The work vector's 64 bytes. -/
abbrev workR (B : BitVec 32) : Region := ⟨B.setWidth 64, 64⟩

/-- What the rounds need of the regions `rd`, `wr`: the work vector (at `B`)
is writable and does not wrap around the address space, and the block (at
`K`) is readable and apart from it. -/
structure Ctx (B K : BitVec 32) (rs ws : List Region) : Prop where
  fit : B.toNat + 64 ≤ 2 ^ 32
  wr : ∀ k < 16, InRegions ws (addr B (vOff k)) 4
  rd : ∀ j < 16, InRegions (rs ++ ws) (addr K (4 * j)) 4
  sep : ∀ k < 16, ∀ j < 16, Mem.Sep (addr K (4 * j)) 4 (addr B (vOff k)) 4

theorem mem_rd {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- The memory after `G` on the words `a, b, c, d` stores `r` in them. -/
def gMem (m : Mem) (B : BitVec 32) (a b c d : Nat)
    (r : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) : Mem :=
  (((m.writeW (addr B (vOff a)) r.1).writeW (addr B (vOff b)) r.2.1).writeW (addr B (vOff c))
    r.2.2.1).writeW (addr B (vOff d)) r.2.2.2

/-! ## `G`, executed once -/

theorem g_ok {B K : BitVec 32} {s : State} (hc : Ctx B K s.rd s.wr) (hb : s.gpr .esi = B)
    (hk : s.gpr .edi = K) {a b c d j k : Nat} (ha : a < 16) (hb' : b < 16) (hc' : c < 16)
    (hd : d < 16) (hj : j < 16) (hk' : k < 16) :
    WP isa (.block (g a b c d j k)) s fun s' =>
      s'.gpr .esi = B ∧ s'.gpr .edi = K ∧ s'.gpr .esp = s.gpr .esp ∧ s'.gpr .ebp = s.gpr .ebp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = gMem s.mem B a b c d (mix Spec.Blake2.s (s.mem.readW (addr B (vOff a)) 32)
        (s.mem.readW (addr B (vOff b)) 32) (s.mem.readW (addr B (vOff c)) 32)
        (s.mem.readW (addr B (vOff d)) 32) (s.mem.readW (addr K (4 * j)) 32)
        (s.mem.readW (addr K (4 * k)) 32)) := by
  have ra := mem_rd (rd := s.rd) (hc.wr a ha)
  have rb := mem_rd (rd := s.rd) (hc.wr b hb')
  have rc := mem_rd (rd := s.rd) (hc.wr c hc')
  have rd := mem_rd (rd := s.rd) (hc.wr d hd)
  have wa := hc.wr a ha
  have wb := hc.wr b hb'
  have wc := hc.wr c hc'
  have wd := hc.wr d hd
  have mj := hc.rd j hj
  have mk := hc.rd k hk'
  apply WP.of_runBlock
  simp (config := {decide := true}) only [g, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, readSrc, ea_mk, State.load32, State.store32, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.gpr_setFlags,
    RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, hb, hk, ra, rb, rc, rd, wa, wb,
    wc, wd, mj, mk, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, rfl⟩

/-! ## The work vector and the block after `G` -/

section
variable {B : BitVec 32} (hfit : B.toNat + 64 ≤ 2 ^ 32)
include hfit

theorem rw_slot (m : Mem) (x : BitVec 32) {i k : Nat} (hi : i < 16) (hk : k < 16) :
    (m.writeW (addr B (vOff i)) x).readW (addr B (vOff k)) 32 =
      if i = k then x else m.readW (addr B (vOff k)) 32 := by
  by_cases h : i = k
  · subst h; simp only [Mem.readW_writeW_self32, ite_true]
  · simp only [h, ite_false]
    exact readW_writeW_addr m x (by simp only [vOff]; omega) (by simp only [vOff]; omega)
      (by simp only [vOff]; omega)

theorem holds_G {v : Work 32} {m : Mem} (hv : Holds B v m) {a b c d : Fin 16} (hab : a.1 ≠ b.1)
    (hac : a.1 ≠ c.1) (had : a.1 ≠ d.1) (hbc : b.1 ≠ c.1) (hbd : b.1 ≠ d.1) (hcd : c.1 ≠ d.1)
    (x y : BitVec 32) :
    Holds B (G Spec.Blake2.s v a b c d x y)
      (gMem m B a b c d (mix Spec.Blake2.s v[a] v[b] v[c] v[d] x y)) := by
  intro k hk
  rw [G_get _ v hab hac had hbc hbd hcd x y k hk]
  simp only [gMem, rw_slot hfit _ _ d.isLt hk, rw_slot hfit _ _ c.isLt hk, rw_slot hfit _ _ b.isLt hk,
    rw_slot hfit _ _ a.isLt hk, hv k hk]
  by_cases ed : (d : Nat) = k <;> by_cases ec : (c : Nat) = k <;> by_cases eb : (b : Nat) = k <;>
    by_cases ea : (a : Nat) = k <;> simp only [ed, ec, eb, ea, ite_true, ite_false] <;> omega

theorem frame_gMem (m : Mem) {a b c d : Nat} (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16)
    (r : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) : Frame [workR B] m (gMem m B a b c d r) := by
  have ct : ∀ i < 16, (workR B).Contains (addr B (vOff i)) (32 / 8) := fun i hi =>
    contains_addr (by simp only [vOff]; omega) (by decide) hfit
  have hm := List.mem_singleton_self (workR B)
  exact ((((Frame.refl _ _).writeW hm _ (ct a ha)).writeW hm _ (ct b hb)).writeW hm _ (ct c hc)).writeW
    hm _ (ct d hd)

end

theorem msg_gMem {B K : BitVec 32} {rs ws : List Region} (hc : Ctx B K rs ws) {M : Block 32} {m : Mem}
    (h : Msg K M m) {a b c d : Nat} (ha : a < 16) (hb : b < 16) (hc' : c < 16) (hd : d < 16)
    (r : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) : Msg K M (gMem m B a b c d r) := by
  intro j
  simp only [gMem]
  rw [Mem.readW_writeW_sep (hc.sep d hd j j.isLt) (by decide),
    Mem.readW_writeW_sep (hc.sep c hc' j j.isLt) (by decide),
    Mem.readW_writeW_sep (hc.sep b hb j j.isLt) (by decide),
    Mem.readW_writeW_sep (hc.sep a ha j j.isLt) (by decide)]
  exact h j

/-! ## The rounds -/

/-- During the rounds of block `M` (at `K`), from `s₀`: the work vector is
`v`, and only it has changed. -/
structure RS (B K : BitVec 32) (M : Block 32) (s₀ : State) (v : Work 32) (s : State) : Prop where
  esi : s.gpr .esi = B
  edi : s.gpr .edi = K
  esp : s.gpr .esp = s₀.gpr .esp
  ebp : s.gpr .ebp = s₀.gpr .ebp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  holds : Holds B v s.mem
  msg : Msg K M s.mem
  frame : Frame [workR B] s₀.mem s.mem

section
variable {B K : BitVec 32} {M : Block 32} {s₀ : State} (hc : Ctx B K s₀.rd s₀.wr)
include hc

theorem gAt_ok {v : Work 32} {s : State} (h : RS B K M s₀ v s) (r i : Nat) (a b c d : Fin 16)
    (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1) (had : a.1 ≠ d.1) (hbc : b.1 ≠ c.1) (hbd : b.1 ≠ d.1)
    (hcd : c.1 ≠ d.1) :
    WP isa (gAt r i a b c d) s
      (RS B K M s₀ (G Spec.Blake2.s v a b c d (M (sigmaAt r (2 * i))) (M (sigmaAt r (2 * i + 1))))) := by
  have hc' : Ctx B K s.rd s.wr := by rw [h.rd, h.wr]; exact hc
  refine WP.mono (g_ok hc' h.esi h.edi a.isLt b.isLt c.isLt d.isLt (sigmaAt r (2 * i)).isLt
    (sigmaAt r (2 * i + 1)).isLt) fun s' ⟨e1, e2, e3, e4, e5, e6, e7⟩ => ?_
  rw [h.holds a a.isLt, h.holds b b.isLt, h.holds c c.isLt, h.holds d d.isLt, h.msg, h.msg] at e7
  refine ⟨e1, e2, e3.trans h.esp, e4.trans h.ebp, e5.trans h.rd, e6.trans h.wr, ?_, ?_, ?_⟩
  · rw [e7]; exact holds_G hc.fit h.holds hab hac had hbc hbd hcd _ _
  · rw [e7]; exact msg_gMem hc h.msg a.isLt b.isLt c.isLt d.isLt _
  · rw [e7]; exact h.frame.trans (frame_gMem hc.fit _ a.isLt b.isLt c.isLt d.isLt _)

theorem round_ok {v : Work 32} {s : State} (h : RS B K M s₀ v s) (r : Nat) :
    WP isa (round r) s (RS B K M s₀ (Spec.Blake2.round Spec.Blake2.s M v r)) := by
  refine WP.seq (WP.mono (gAt_ok hc h r 0 0 4 8 12 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (gAt_ok hc h₁ r 1 1 5 9 13 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (gAt_ok hc h₂ r 2 2 6 10 14 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (gAt_ok hc h₃ r 3 3 7 11 15 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (gAt_ok hc h₄ r 4 0 5 10 15 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (gAt_ok hc h₅ r 5 1 6 11 12 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (gAt_ok hc h₆ r 6 2 7 8 13 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₇ h₇ => ?_)
  exact WP.mono (gAt_ok hc h₇ r 7 3 4 9 14 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₈ h₈ => h₈

theorem rounds_ok {v : Work 32} {s : State} (h : RS B K M s₀ v s) (n : Nat) :
    WP isa (rounds n) s (RS B K M s₀ ((List.range n).foldl (Spec.Blake2.round Spec.Blake2.s M) v)) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    refine WP.seq (WP.mono ih fun s' h' => ?_)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact round_ok hc h' n

end

end VG.Proof.Blake2.X86.CompressS
