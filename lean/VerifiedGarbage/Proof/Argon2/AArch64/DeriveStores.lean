import VerifiedGarbage.Proof.Argon2.AArch64.DeriveStore

/-! Compose argument stores without re-executing a growing symbolic memory state. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def saveMemory (s : State) (args : List (Nat × Reg)) : Mem :=
  args.foldl (fun m arg => m.writeW (s.gpr .x19 + BitVec.ofNat 64 arg.1) (s.gpr arg.2)) s.mem

structure Saved (s t : State) (args : List (Nat × Reg)) : Prop where
  mem : t.mem = saveMemory s args
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (args.map fun arg => (⟨s.gpr .x19 + BitVec.ofNat 64 arg.1, 8⟩ : Region)) s.mem t.mem

theorem stores_ok (args : List (Nat × Reg)) (s : State)
    (encoding : ∀ arg ∈ args, arg.1 % 8 = 0 ∧ arg.1 < 32768)
    (write : ∀ arg ∈ args, InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 arg.1) 8) :
    WP isa (.block (args.map fun arg => .str .x arg.2 .x19 arg.1)) s (Saved s · args) := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons arg args ih =>
    rw [List.map_cons]
    change WP isa (.block (([.str .x arg.2 .x19 arg.1] : List Instr) ++ _)) s _
    rw [WP.block_append_iff]
    refine (store_ok s arg.1 arg.2 (encoding arg (List.mem_cons_self ..)).1
      (encoding arg (List.mem_cons_self ..)).2 (write arg (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t (fun a ha => encoding a (List.mem_cons_of_mem arg ha)) (fun a ha => by rw [ht.wr, ht.regs]; exact write a (List.mem_cons_of_mem arg ha))).mono ?_
    intro u hu
    refine ⟨?_, hu.regs.trans ht.regs, hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.sp.trans ht.sp, ?_⟩
    · rw [hu.mem]
      unfold saveMemory
      rw [ht.regs, ht.mem, List.foldl_cons]
    · apply (ht.frame.mono ?_).trans
      · have frame := hu.frame
        rw [ht.regs] at frame
        exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
      · intro region hr
        simp only [List.mem_singleton] at hr; subst region
        exact List.mem_cons_self ..

theorem Saved.other_word {s t : State} {args : List (Nat × Reg)} (h : Saved s t args)
    (e : Nat) (bound : e + 8 ≤ 2 ^ 64)
    (separate : ∀ arg ∈ args, e + 8 ≤ arg.1 ∨ arg.1 + 8 ≤ e)
    (bounds : ∀ arg ∈ args, arg.1 + 8 ≤ 2 ^ 64) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 e) 64 := by
  rw [h.regs]
  apply h.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨arg, member, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate arg member) bound (bounds arg member)

theorem stores_values_ok (args : List (Nat × Reg)) (s : State)
    (encoding : ∀ arg ∈ args, arg.1 % 8 = 0 ∧ arg.1 < 32768)
    (write : ∀ arg ∈ args, InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 arg.1) 8)
    (separate : args.Pairwise fun a b => a.1 + 8 ≤ b.1 ∨ b.1 + 8 ≤ a.1)
    (bounds : ∀ arg ∈ args, arg.1 + 8 ≤ 2 ^ 64) :
    WP isa (.block (args.map fun arg => .str .x arg.2 .x19 arg.1)) s fun t =>
      Saved s t args ∧ ∀ arg ∈ args, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 arg.1) 64 = s.gpr arg.2 := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩, by simp⟩
  | cons arg args ih =>
    obtain ⟨headSep, tailSep⟩ := List.pairwise_cons.mp separate
    rw [List.map_cons]
    change WP isa (.block (([.str .x arg.2 .x19 arg.1] : List Instr) ++ _)) s _
    rw [WP.block_append_iff]
    refine (store_ok s arg.1 arg.2 (encoding arg (List.mem_cons_self ..)).1
      (encoding arg (List.mem_cons_self ..)).2 (write arg (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t (fun a ha => encoding a (List.mem_cons_of_mem arg ha)) (fun a ha => by rw [ht.wr, ht.regs]; exact write a (List.mem_cons_of_mem arg ha))
      tailSep (fun a ha => bounds a (List.mem_cons_of_mem arg ha))).mono ?_
    rintro u ⟨hu, values⟩
    have saved : Saved s u (arg :: args) := by
      refine ⟨?_, hu.regs.trans ht.regs, hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.sp.trans ht.sp, ?_⟩
      · rw [hu.mem]; unfold saveMemory; rw [ht.regs, ht.mem, List.foldl_cons]
      · apply (ht.frame.mono ?_).trans
        · have frame := hu.frame
          rw [ht.regs] at frame
          exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
        · intro region hr
          simp only [List.mem_singleton] at hr; subst region
          exact List.mem_cons_self ..
    refine ⟨saved, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [hu.other_word a.1 (bounds a (List.mem_cons_self ..)) headSep
        (fun b hb => bounds b (List.mem_cons_of_mem a hb))]
      exact ht.word
    · rw [values a ha, ht.regs]

end VG.Proof.Argon2.AArch64.Derive
