import VerifiedGarbage.Proof.TripleDes.Arm.Key.Component
import VerifiedGarbage.Proof.TripleDes.Arm.WordStore
import VerifiedGarbage.Proof.Rc2.Arm.Lookup

namespace VG.Proof.TripleDes.Arm.Key
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (Keep)

def copyPair (a b : Nat) : List Instr :=
  [.ldr .r4 .r2 a, .ldr .r5 .r2 (a + 4), .str .r4 .r2 b, .str .r5 .r2 (b + 4)]

theorem copyPair_ok (s : State) (a b : Nat) (ha : a + 4 < 4096) (hb : b + 4 < 4096)
    (fit : (s.gpr .r2).toNat + max a b + 8 ≤ 2 ^ 32)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (a + 4 * t))) 4)
    (hw : ∀ t < 2, InRegions s.wr
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (b + 4 * t))) 4) :
    ∃ s', runBlock isa (copyPair a b) s = some s' ∧
      Keep [.r4, .r5] {s with
        mem := s.mem.writeW (State.addr (s.gpr .r2 + BitVec.ofNat 32 b))
          (s.mem.readW (State.addr (s.gpr .r2 + BitVec.ofNat 32 a)) 64)} s' := by
  have hr0 := hr 0 (by decide)
  have hr1 := hr 1 (by decide)
  have hw0 := hw 0 (by decide)
  have hw1 := hw 1 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at hr0 hw0
  simp only [Nat.mul_one] at hr1 hw1
  refine ⟨_, by
    simp only [copyPair, runBlock_cons, runStep_some, runBlock_nil, exec,
      show a < 4096 from by omega, ha, show b < 4096 from by omega, hb,
      ite_true, State.load32, State.store32, hr0, hr1, hw0, hw1, Option.map_some,
      gpr_setReg, reduceCtorEq, ite_true, ite_false, mem_setReg, rd_setReg, wr_setReg]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2, ite_false]
  · have ea : State.addr (s.gpr .r2 + BitVec.ofNat 32 (a + 4)) =
        State.addr (s.gpr .r2 + BitVec.ofNat 32 a) + 4 := by
      rw [addr_add (by omega_using [fit, Nat.le_max_left a b]),
        addr_add (by omega_using [fit, Nat.le_max_left a b]), ← Offset.add_ofNat_add_ofNat]
      rfl
    have eb : State.addr (s.gpr .r2 + BitVec.ofNat 32 (b + 4)) =
        State.addr (s.gpr .r2 + BitVec.ofNat 32 b) + 4 := by
      rw [addr_add (by omega_using [fit, Nat.le_max_right a b]),
        addr_add (by omega_using [fit, Nat.le_max_right a b]), ← Offset.add_ofNat_add_ofNat]
      rfl
    rw [ea, eb, writeW_pair, readW_pair]
  · rfl
  · rfl

 def copyCode (n : Nat) : List Instr :=
  (List.range n).flatMap fun j =>
    copyPair (8 * j) (256 + 8 * j)

structure CopyPost (base : Addr) (s : State) (n : Nat) (s' : State) : Prop where
  keys : ∀ i < n, s'.mem.readW (base + BitVec.ofNat 64 (256 + 8 * i)) 64 =
    s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r
  frame : Frame [⟨base + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copy_ok (s : State) (n : Nat) (hn : n ≤ 16)
    (fit : (s.gpr .r2).toNat + 384 ≤ 2 ^ 32)
    (hr : ∀ i < 16, ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (8 * i + 4 * t))) 4)
    (hw : ∀ i < 16, ∀ t < 2, InRegions s.wr
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (256 + 8 * i + 4 * t))) 4) :
    WP isa (.block (copyCode n)) s (CopyPost (State.addr (s.gpr .r2)) s n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ hi => by omega, rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [copyCode, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    apply WP.mono (ih (by omega))
    intro s₁ h₁
    have hbase : s₁.gpr .r2 = s.gpr .r2 := h₁.reg .r2 (by decide) (by decide)
    have readable : ∀ t < 2, InRegions (s₁.rd ++ s₁.wr)
        (State.addr (s₁.gpr .r2 + BitVec.ofNat 32 (8 * n + 4 * t))) 4 := by
      rw [h₁.rd, h₁.wr, hbase]; exact hr n (by omega)
    have writable : ∀ t < 2, InRegions s₁.wr
        (State.addr (s₁.gpr .r2 + BitVec.ofNat 32 (256 + 8 * n + 4 * t))) 4 := by
      rw [h₁.wr, hbase]; exact hw n (by omega)
    have fit₁ : (s₁.gpr .r2).toNat + max (8 * n) (256 + 8 * n) + 8 ≤ 2 ^ 32 := by
      rw [hbase, Nat.max_eq_right (by omega : 8 * n ≤ 256 + 8 * n)]
      omega_using [fit, hn]
    obtain ⟨s₂, run₂, keep₂⟩ := copyPair_ok s₁ (8 * n) (256 + 8 * n)
      (by omega) (by omega) fit₁ readable writable
    have source : s₁.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 (8 * n)) 64 =
        s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 (8 * n)) 64 := by
      apply h₁.frame.readW (r := ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 (8 * n), 8⟩)
        (Region.contains_self _ _) _ (by decide)
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact Offset.disjoint (State.addr (s.gpr .r2)) (by omega) (by omega) (by decide)
    have mem₂ : s₂.mem = s₁.mem.writeW (State.addr (s.gpr .r2) + BitVec.ofNat 64 (256 + 8 * n))
        (s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 (8 * n)) 64) := by
      have hm := keep₂.mem
      rw [hbase, addr_add (by omega_using [fit, hn]),
        addr_add (by omega_using [fit, hn]), source] at hm
      exact hm
    refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr,
      fun r h4 h5 => (keep₂.reg r (by
        simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using And.intro h4 h5)).trans (h₁.reg r h4 h5), ?_⟩⟩
    · intro i hi
      rw [mem₂]
      by_cases he : i = n
      · subst i; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep (State.addr (s.gpr .r2)) (by omega) (by omega) (by omega)) (by decide)]
        exact h₁.keys i (by omega)
    · rw [mem₂]
      apply h₁.frame.writeW (List.mem_singleton_self _) _
      have hc := Offset.contains_base (State.addr (s.gpr .r2) + BitVec.ofNat 64 256)
        (d := 8 * n) (n := 8) (k := 128) (by omega) (by omega)
      rw [Offset.add_ofNat_add_ofNat] at hc
      exact hc


end VG.Proof.TripleDes.Arm.Key
