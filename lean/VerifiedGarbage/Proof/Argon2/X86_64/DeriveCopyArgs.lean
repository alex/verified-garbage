import VerifiedGarbage.Proof.Argon2.X86_64.DeriveCopyArg

/-! Copy all stack arguments without modifying their caller-owned storage. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure CopiedArgs (s t : State) (js : List Nat) : Prop where
  values : ∀ j ∈ js, t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 (copyDestination j)) 64 =
    s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 64
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  frame : Frame (js.map fun j => (⟨s.gpr .rsp + BitVec.ofNat 64 (copyDestination j), 8⟩ : Region)) s.mem t.mem

theorem CopiedArgs.other_word {s t : State} {js : List Nat} (h : CopiedArgs s t js)
    (d : Nat) (bound : d + 8 ≤ 2 ^ 64)
    (separate : ∀ j ∈ js, d + 8 ≤ copyDestination j ∨ copyDestination j + 8 ≤ d)
    (bounds : ∀ j ∈ js, copyDestination j + 8 ≤ 2 ^ 64) :
    t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 d) 64 := by
  rw [h.regs .rsp (by decide)]
  apply h.frame.readW (r := ⟨s.gpr .rsp + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate j hj) bound (bounds j hj)

theorem copyArgs_ok (js : List Nat) (s : State) (bounds : ∀ j ∈ js, j < 12)
    (distinct : js.Nodup)
    (read : ∀ j ∈ js, InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 8)
    (write : ∀ j ∈ js, InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 (copyDestination j)) 8) :
    WP isa (.block (js.flatMap Impl.Argon2.X86_64.Derive.copyArg)) s (CopiedArgs s · js) := by
  induction js generalizing s with
  | nil => exact WP.block_nil ⟨by simp, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons j js ih =>
    have nodup := List.nodup_cons.mp distinct
    have jBound := bounds j (List.mem_cons_self ..)
    have tailBounds : ∀ x ∈ js, x < 12 := fun x hx => bounds x (List.mem_cons_of_mem _ hx)
    rw [List.flatMap_cons, WP.block_append_iff]
    refine (copyArg_ok s j (read j (List.mem_cons_self ..)) (write j (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t tailBounds nodup.2
      (fun x hx => by rw [ht.rd, ht.wr, ht.regs .rsp (by decide)]; exact read x (List.mem_cons_of_mem _ hx))
      (fun x hx => by rw [ht.wr, ht.regs .rsp (by decide)]; exact write x (List.mem_cons_of_mem _ hx))).mono ?_
    intro u hu
    refine ⟨?_, fun r hr => (hu.regs r hr).trans (ht.regs r hr),
      hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.mxcsr.trans ht.mxcsr, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hu.other_word (copyDestination x) (by unfold copyDestination; omega) (by
          intro y hy
          have ne : y ≠ x := fun eq => nodup.1 (eq ▸ hy)
          unfold copyDestination; omega) (by
          intro y hy; have := tailBounds y hy; unfold copyDestination; omega)]
        exact ht.word
      · rw [hu.values x hx, ht.regs .rsp (by decide), ht.mem]
        apply Mem.readW_writeW_sep ?_ (by decide)
        have xBound := tailBounds x hx
        exact Offset.sep _ (Or.inr (by unfold copyDestination copySource; omega))
          (by unfold copySource; omega) (by unfold copyDestination; omega)
    · apply (ht.frame.mono ?_).trans
      · have frame := hu.frame
        rw [ht.regs .rsp (by decide)] at frame
        exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
      · intro region hr
        simp only [List.mem_singleton] at hr; subst region
        exact List.mem_cons_self ..

end VG.Proof.Argon2.X86_64.Derive
