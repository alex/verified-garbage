import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Component
import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Steps

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

 def copyCode (n : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    [.mov .rax (.mem (memOp .rdx (8 * j))), .store (memOp .rdx (256 + 8 * j)) .rax]

structure CopyPost (base : Addr) (s : State) (n : Nat) (s' : State) : Prop where
  keys : ∀ i < n, s'.mem.readW (base + BitVec.ofNat 64 (256 + 8 * i)) 64 =
    s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  frame : Frame [⟨base + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copy_ok (s : State) (n : Nat) (hn : n ≤ 16)
    (hr : ∀ i < 16, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8)
    (hw : ∀ i < 16, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (256 + 8 * i)) 8) :
    WP isa (.block (copyCode n)) s (CopyPost (s.gpr .rdx) s n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ hi => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [copyCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    apply WP.mono (ih (by omega))
    intro s₁ h₁
    have hbase : s₁.gpr .rdx = s.gpr .rdx := h₁.reg .rdx (by decide)
    have readable : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdx + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [h₁.rd, h₁.wr, hbase]; exact hr n (by omega)
    have writable : InRegions s₁.wr (s₁.gpr .rdx + BitVec.ofNat 64 (256 + 8 * n)) 8 := by
      rw [h₁.wr, hbase]; exact hw n (by omega)
    obtain ⟨s₂, run₂, keep₂⟩ := VG.Proof.Rc2.X86_64.Cbc.copy64_ok s₁ .rdx .rdx
      (8 * n) (256 + 8 * n) (by decide) readable writable
    have source : s₁.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (8 * n)) 64 =
        s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (8 * n)) 64 := by
      apply h₁.frame.readW (r := ⟨s.gpr .rdx + BitVec.ofNat 64 (8 * n), 8⟩)
        (Region.contains_self _ _) _ (by decide)
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact Offset.disjoint (s.gpr .rdx) (by omega) (by omega) (by decide)
    have mem₂ : s₂.mem = s₁.mem.writeW (s.gpr .rdx + BitVec.ofNat 64 (256 + 8 * n))
        (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (8 * n)) 64) := by
      have hm := keep₂.mem
      rw [hbase, source] at hm
      exact hm
    refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr,
      fun r hr => (keep₂.reg r (by simpa only [List.mem_singleton] using hr)).trans (h₁.reg r hr), ?_⟩⟩
    · intro i hi
      rw [mem₂]
      by_cases he : i = n
      · subst i; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep (s.gpr .rdx) (by omega) (by omega) (by omega)) (by decide)]
        exact h₁.keys i (by omega)
    · rw [mem₂]
      apply h₁.frame.writeW (List.mem_singleton_self _) _
      have hc := Offset.contains_base (s.gpr .rdx + BitVec.ofNat 64 256)
        (d := 8 * n) (n := 8) (k := 128) (by omega) (by omega)
      rw [Offset.add_ofNat_add_ofNat] at hc
      exact hc

end VG.Proof.TripleDes.X86_64.Key
