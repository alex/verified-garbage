import VerifiedGarbage.Proof.Argon2.X86_64.DeriveStore

/-! Compose argument stores without re-executing a growing symbolic memory state. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def saveMemory (s : State) (args : List (Nat × Reg)) : Mem :=
  args.foldl (fun m arg => m.writeW (s.gpr .rbp + BitVec.ofNat 64 arg.1) (s.gpr arg.2)) s.mem

structure Saved (s t : State) (args : List (Nat × Reg)) : Prop where
  mem : t.mem = saveMemory s args
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem stores_ok (args : List (Nat × Reg)) (s : State)
    (write : ∀ arg ∈ args, InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 arg.1) 8) :
    WP isa (.block (args.map fun arg => .store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2)) s (Saved s · args) := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons arg args ih =>
    rw [List.map_cons]
    change WP isa (.block (([.store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2] : List Instr) ++ _)) s _
    rw [WP.block_append_iff]
    refine (store_ok s arg.1 arg.2 (write arg (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t (fun a ha => by rw [ht.wr, ht.regs]; exact write a (List.mem_cons_of_mem arg ha))).mono ?_
    intro u hu
    refine ⟨?_, hu.regs.trans ht.regs, hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.mxcsr.trans ht.mxcsr⟩
    rw [hu.mem]
    unfold saveMemory
    rw [ht.regs, ht.mem, List.foldl_cons]

end VG.Proof.Argon2.X86_64.Derive
