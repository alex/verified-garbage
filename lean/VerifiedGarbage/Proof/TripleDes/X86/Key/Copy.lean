import Batteries.Logic
import VerifiedGarbage.Proof.TripleDes.X86.Key.Component
import VerifiedGarbage.Proof.Rc2.X86.RoundSteps

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep addr32)

def copyWord (a b : Nat) : List Instr :=
  [.mov .eax (.mem (memOp .edx a)), .store (memOp .edx b) .eax]

theorem copyWord_ok (s : State) (a b : Nat)
    (hr : InRegions (s.rd ++ s.wr) (addr (s.gpr .edx) a) 4)
    (hw : InRegions s.wr (addr (s.gpr .edx) b) 4) :
    ∃ s', runBlock isa (copyWord a b) s = some s' ∧
      Keep [.eax] {s with
        mem := (s.mem.writeW (addr (s.gpr .edx) b)
          (s.mem.readW (addr (s.gpr .edx) a) 32))} s' := by
  simp only [addr] at hr hw
  refine ⟨_, by
    simp only [copyWord, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.store32, State.ea, memOp, hr, hw, ite_true,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, ite_false]
    rfl, ?_⟩
  refine ⟨?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [gpr_setReg, hr, ite_false]

structure CopyPost (base : Addr) (s : State) (n : Nat) (s' : State) : Prop where
  words : ∀ i < n, s'.mem.readW (base + BitVec.ofNat 64 (256 + 4 * i)) 32 =
    s.mem.readW (base + BitVec.ofNat 64 (4 * i)) 32
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  frame : Frame [⟨base + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copy_ok (s : State) (n : Nat) (hn : n ≤ 32)
    (fit : (s.gpr .edx).toNat + 384 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (addr (s.gpr .edx) (4 * i)) 4)
    (hw : ∀ i < 32, InRegions s.wr (addr (s.gpr .edx) (256 + 4 * i)) 4) :
    WP isa (.block (Impl.TripleDes.X86.Key.copyWords n)) s (CopyPost (addr32 (s.gpr .edx)) s n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ hi => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [Impl.TripleDes.X86.Key.copyWords, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, WP.block_append_iff]
    apply WP.mono (ih (by omega))
    intro s₁ h₁
    have base₁ : s₁.gpr .edx = s.gpr .edx := h₁.reg .edx (by decide)
    have readable : InRegions (s₁.rd ++ s₁.wr) (addr (s₁.gpr .edx) (4 * n)) 4 := by
      rw [h₁.rd, h₁.wr, base₁]; exact hr n (by omega)
    have writable : InRegions s₁.wr (addr (s₁.gpr .edx) (256 + 4 * n)) 4 := by
      rw [h₁.wr, base₁]; exact hw n (by omega)
    obtain ⟨s₂, run₂, keep₂⟩ := copyWord_ok s₁ (4 * n) (256 + 4 * n) readable writable
    have source : s₁.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32 =
        s.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32 := by
      apply h₁.frame.readW (r := ⟨addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n), 4⟩)
        (Region.contains_self _ _) _ (by decide)
      intro r h
      obtain rfl := List.mem_singleton.mp h
      exact Offset.disjoint (addr32 (s.gpr .edx)) (by omega) (by omega) (by decide)
    have mem₂ : s₂.mem = s₁.mem.writeW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (256 + 4 * n))
        (s.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32) := by
      have hm := keep₂.mem
      rw [base₁, addr_eq (by omega : (s.gpr .edx).toNat + (256 + 4 * n) < 2 ^ 32),
        addr_eq (by omega : (s.gpr .edx).toNat + 4 * n < 2 ^ 32)] at hm
      change s₂.mem = s₁.mem.writeW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (256 + 4 * n))
        (s₁.mem.readW (addr32 (s.gpr .edx) + BitVec.ofNat 64 (4 * n)) 32) at hm
      rw [source] at hm
      exact hm
    refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr,
      fun r hr => (keep₂.reg r (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr)).trans
        (h₁.reg r hr), ?_⟩⟩
    · intro i hi
      rw [mem₂]
      by_cases he : i = n
      · subst i; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep (addr32 (s.gpr .edx)) (by omega) (by omega)
          (by omega)) (by decide)]
        exact h₁.words i (by omega)
    · rw [mem₂]
      apply h₁.frame.writeW (List.mem_singleton_self _) _
      have hc := Offset.contains_base (addr32 (s.gpr .edx) + BitVec.ofNat 64 256)
        (d := 4 * n) (n := 4) (k := 128) (by omega) (by omega)
      rw [Offset.add_ofNat_add_ofNat] at hc
      exact hc

structure CopySchedulePost (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (addr32 (scheduleArg s) + BitVec.ofNat 64 (256 + 8 * i)) 64 =
    s.mem.readW (addr32 (scheduleArg s) + BitVec.ofNat 64 (8 * i)) 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .eax → r ≠ .edx → s'.gpr r = s.gpr r
  frame : Frame [⟨addr32 (scheduleArg s) + BitVec.ofNat 64 256, 128⟩] s.mem s'.mem

theorem copyThird_ok (s : State) (fit : (scheduleArg s).toNat + 384 ≤ 2 ^ 32)
    (harg : InRegions (s.rd ++ s.wr) (VG.X86.Straight.wordAddr (s.gpr .esp) 3) 4)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (addr (scheduleArg s) (4 * i)) 4)
    (hw : ∀ i < 32, InRegions s.wr (addr (scheduleArg s) (256 + 4 * i)) 4) :
    WP isa (.block Impl.TripleDes.X86.Key.copyThird) s (CopySchedulePost s) := by
  rw [Impl.TripleDes.X86.Key.copyThird, WP.block_append_iff]
  let s₀ := s.setReg .edx (scheduleArg s)
  have he : exec (.mov .edx (.mem (memOp .esp 12))) s = some s₀ := by
    simp only [exec, readSrc, State.load32, State.ea, memOp]
    change (if InRegions (s.rd ++ s.wr) (VG.X86.Straight.wordAddr (s.gpr .esp) 3) 4 then
      some (scheduleArg s) else none).map (s.setReg .edx) = some s₀
    rw [ite_eq_left harg, Option.map_some]
  refine WP.of_runBlock ⟨s₀, by simp only [runBlock_cons, he, runStep_some, runBlock_nil], ?_⟩
  have ptr₀ : s₀.gpr .edx = scheduleArg s := gpr_setReg_self _ _ _
  apply WP.mono (copy_ok s₀ 32 (by decide) (by rw [ptr₀]; exact fit)
    (by rw [ptr₀]; exact hr) (by rw [ptr₀]; exact hw))
  intro s₁ h₁
  refine ⟨?_, h₁.rd, h₁.wr, ?_, ?_⟩
  · intro i hi
    let p := addr32 (scheduleArg s)
    have h0 := h₁.words (2 * i) (by omega)
    have h1 := h₁.words (2 * i + 1) (by omega)
    rw [ptr₀] at h0 h1
    change s₁.mem.readW (p + BitVec.ofNat 64 (256 + 8 * i)) 64 =
      s.mem.readW (p + BitVec.ofNat 64 (8 * i)) 64
    rw [← readW_pair, ← readW_pair]
    have d0 : 256 + 4 * (2 * i) = 256 + 8 * i := by omega
    have d1 : 256 + 4 * (2 * i + 1) = 256 + 8 * i + 4 := by omega
    have a0 : 4 * (2 * i) = 8 * i := by omega
    have a1 : 4 * (2 * i + 1) = 8 * i + 4 := by omega
    rw [d0, a0] at h0
    rw [d1, a1, ← Offset.add_ofNat_add_ofNat (addr32 (scheduleArg s)) (256 + 8 * i) 4,
      ← Offset.add_ofNat_add_ofNat (addr32 (scheduleArg s)) (8 * i) 4] at h1
    change s₁.mem.readW ((p + BitVec.ofNat 64 (256 + 8 * i)) + 4) 32 =
      s.mem.readW ((p + BitVec.ofNat 64 (8 * i)) + 4) 32 at h1
    change s₁.mem.readW (p + BitVec.ofNat 64 (256 + 8 * i)) 32 =
      s.mem.readW (p + BitVec.ofNat 64 (8 * i)) 32 at h0
    exact congrArg₂ (fun (hi lo : BitVec 32) => hi ++ lo) h1 h0
  · intro r ha hd
    exact (h₁.reg r ha).trans (gpr_setReg_of_ne s _ hd)
  · have hf := h₁.frame
    rw [ptr₀] at hf
    exact hf

end VG.Proof.TripleDes.X86.Key
