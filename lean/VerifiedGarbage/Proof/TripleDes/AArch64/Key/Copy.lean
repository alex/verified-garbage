import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Component
import VerifiedGarbage.Proof.Rc2.AArch64.Lookup

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
open VG.Proof.Rc2.AArch64 (Keep)

theorem copy64_ok (s : State) (src dst : Reg) (a b : Nat) (hne : dst ≠ .x4)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 a) 8)
    (writable : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 b) 8)
    (ha : a % 8 = 0 ∧ a < 32768 := by decide)
    (hb : b % 8 = 0 ∧ b < 32768 := by decide) :
    ∃ s', runBlock isa [.ldr .x .x4 src a, .str .x .x4 dst b] s = some s' ∧
      Keep [.x4] {s with
        mem := s.mem.writeW (s.gpr dst + BitVec.ofNat 64 b) (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)} s' := by
  have hw : InRegions (s.write .x .x4 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)).wr
      ((s.write .x .x4 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)).gpr dst + BitVec.ofNat 64 b) 8 := by
    simpa only [wr_write, gpr_write, hne, ite_false] using writable
  refine ⟨_, by
    rw [runBlock_cons, exec_ldr_x ha readable, runStep_some,
      runBlock_cons, exec_str_x hb hw, runStep_some, runBlock_nil], ?_⟩
  constructor
  · intro r hr
    have hn : r ≠ .x4 := by intro h; subst r; exact hr (by simp)
    exact gpr_write_of_ne _ _ _ hn
  · simp only [gpr_write, hne, ite_false, ite_true, BitVec.setWidth_eq, mem_write]
  · rfl
  · rfl

 def copyCode (n : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [.ldr .x .x4 .x2 (8 * j), .str .x .x4 .x2 (256 + 8 * j)]

structure CopyPost (base : Addr) (s : State) (n : Nat) (s' : State) : Prop where
  keys : ∀ i < n, s'.mem.readW (base + BitVec.ofNat 64 (256 + 8 * i)) 64 =
    s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .x4 → s'.gpr r = s.gpr r
  frame : Frame [⟨base + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copy_ok (s : State) (n : Nat) (hn : n ≤ 16)
    (hr : ∀ i < 16, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8)
    (hw : ∀ i < 16, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (256 + 8 * i)) 8) :
    WP isa (.block (copyCode n)) s (CopyPost (s.gpr .x2) s n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ hi => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [copyCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    apply WP.mono (ih (by omega))
    intro s₁ h₁
    have hbase : s₁.gpr .x2 = s.gpr .x2 := h₁.reg .x2 (by decide)
    have readable : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x2 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [h₁.rd, h₁.wr, hbase]; exact hr n (by omega)
    have writable : InRegions s₁.wr (s₁.gpr .x2 + BitVec.ofNat 64 (256 + 8 * n)) 8 := by
      rw [h₁.wr, hbase]; exact hw n (by omega)
    obtain ⟨s₂, run₂, keep₂⟩ := copy64_ok s₁ .x2 .x2
      (8 * n) (256 + 8 * n) (by decide) readable writable (by omega) (by omega)
    have source : s₁.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (8 * n)) 64 =
        s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (8 * n)) 64 := by
      apply h₁.frame.readW (r := ⟨s.gpr .x2 + BitVec.ofNat 64 (8 * n), 8⟩)
        (Region.contains_self _ _) _ (by decide)
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact Offset.disjoint (s.gpr .x2) (by omega) (by omega) (by decide)
    have mem₂ : s₂.mem = s₁.mem.writeW (s.gpr .x2 + BitVec.ofNat 64 (256 + 8 * n))
        (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (8 * n)) 64) := by
      have hm := keep₂.mem
      rw [hbase, source] at hm
      exact hm
    refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr,
      fun r hr => (keep₂.reg r (by simpa only [List.mem_singleton] using hr)).trans (h₁.reg r hr), ?_⟩⟩
    · intro i hi
      rw [mem₂]
      by_cases he : i = n
      · subst i; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep (s.gpr .x2) (by omega) (by omega) (by omega)) (by decide)]
        exact h₁.keys i (by omega)
    · rw [mem₂]
      apply h₁.frame.writeW (List.mem_singleton_self _) _
      have hc := Offset.contains_base (s.gpr .x2 + BitVec.ofNat 64 256)
        (d := 8 * n) (n := 8) (k := 128) (by omega) (by omega)
      rw [Offset.add_ofNat_add_ofNat] at hc
      exact hc

end VG.Proof.TripleDes.AArch64.Key
