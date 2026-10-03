import VerifiedGarbage.Proof.Argon2.X86_64.Parameters
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveAbi
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveSaved
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveNormalize
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-! Merged from `Proof.Argon2.X86_64.DeriveStore`. -/
section
/-! Save each incoming argument with one short symbolic execution. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure Stored (s t : State) (d : Nat) (r : Reg) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 d) (s.gpr r)
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem store_ok (s : State) (d : Nat) (r : Reg)
    (write : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 d) 8) :
    WP isa (.block [.store (Impl.Argon2.X86_64.at_ .rbp d) r]) s (Stored s · d r) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    State.ea, Impl.Argon2.X86_64.at_, BitVec.ofInt_natCast, write,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Stored.word {s t : State} {d : Nat} {r : Reg} (h : Stored s t d r) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 = s.gpr r := by
  rw [h.regs, h.mem, Mem.readW_writeW_self64]

theorem Stored.frame {s t : State} {d : Nat} {r : Reg} (h : Stored s t d r) :
    Frame [⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem Stored.other_word {s t : State} {d : Nat} {r : Reg} (h : Stored s t d r)
    (e : Nat) (separate : e + 8 ≤ d ∨ d + 8 ≤ e) (ed : e + 8 ≤ 2 ^ 64) (dd : d + 8 ≤ 2 ^ 64) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 e) 64 := by
  rw [h.regs, h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ separate ed dd) (by decide)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveStores`. -/
section
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
  frame : Frame (args.map fun arg => (⟨s.gpr .rbp + BitVec.ofNat 64 arg.1, 8⟩ : Region)) s.mem t.mem

theorem stores_ok (args : List (Nat × Reg)) (s : State)
    (write : ∀ arg ∈ args, InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 arg.1) 8) :
    WP isa (.block (args.map fun arg => .store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2)) s (Saved s · args) := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons arg args ih =>
    rw [List.map_cons]
    change WP isa (.block (([.store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2] : List Instr) ++ _)) s _
    rw [WP.block_append_iff]
    refine (store_ok s arg.1 arg.2 (write arg (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t (fun a ha => by rw [ht.wr, ht.regs]; exact write a (List.mem_cons_of_mem arg ha))).mono ?_
    intro u hu
    refine ⟨?_, hu.regs.trans ht.regs, hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.mxcsr.trans ht.mxcsr, ?_⟩
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
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 e) 64 := by
  rw [h.regs]
  apply h.frame.readW (r := ⟨s.gpr .rbp + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨arg, member, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate arg member) bound (bounds arg member)

theorem stores_values_ok (args : List (Nat × Reg)) (s : State)
    (write : ∀ arg ∈ args, InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 arg.1) 8)
    (separate : args.Pairwise fun a b => a.1 + 8 ≤ b.1 ∨ b.1 + 8 ≤ a.1)
    (bounds : ∀ arg ∈ args, arg.1 + 8 ≤ 2 ^ 64) :
    WP isa (.block (args.map fun arg => .store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2)) s fun t =>
      Saved s t args ∧ ∀ arg ∈ args, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = s.gpr arg.2 := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩, by simp⟩
  | cons arg args ih =>
    obtain ⟨headSep, tailSep⟩ := List.pairwise_cons.mp separate
    rw [List.map_cons]
    change WP isa (.block (([.store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2] : List Instr) ++ _)) s _
    rw [WP.block_append_iff]
    refine (store_ok s arg.1 arg.2 (write arg (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t (fun a ha => by rw [ht.wr, ht.regs]; exact write a (List.mem_cons_of_mem arg ha))
      tailSep (fun a ha => bounds a (List.mem_cons_of_mem arg ha))).mono ?_
    rintro u ⟨hu, values⟩
    have saved : Saved s u (arg :: args) := by
      refine ⟨?_, hu.regs.trans ht.regs, hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.mxcsr.trans ht.mxcsr, ?_⟩
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

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveSetup`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveScratch`. -/
section
/-! Load the caller-supplied hash workspace after saving incoming arguments. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure ScratchLoaded (s t : State) : Prop where
  scratch : t.gpr .rbx = s.mem.readW (s.gpr .rbp + 248) 64
  regs : ∀ r, r ≠ .rbx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem scratch_ok (s : State) (read : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 248) 8) :
    WP isa (.block [.mov .rbx (.mem (Impl.Argon2.X86_64.at_ .rbp 248))]) s (ScratchLoaded s) := by
  have ea : s.ea (Impl.Argon2.X86_64.at_ .rbp 248) = s.gpr .rbp + 248 := rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea, read,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact RegUpd.gpr_setReg_self ..
  · intro r hr
    exact RegUpd.gpr_setReg_of_ne _ _ hr

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveEntry`. -/
section
/-! Establish the local frame base and normalize register-passed u32 arguments. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure Entered (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rsp
  kind : t.gpr .rdi = ((s.gpr .rdi).setWidth 32).setWidth 64
  passes : t.gpr .r9 = ((s.gpr .r9).setWidth 32).setWidth 64
  regs : ∀ r, r ≠ .rbp → r ≠ .rdi → r ≠ .r9 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem entry_ok (s : State) :
    WP isa (.block [.mov .rbp (.reg .rsp), .mov32 .rdi (.reg .rdi), .mov32 .r9 (.reg .r9)]) s (Entered s) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.setReg32, RegUpd.gpr_setReg, reduceCtorEq,
    ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r hb hd h9
  simp only [RegUpd.gpr_setReg, hb, hd, h9, ite_false]

end VG.Proof.Argon2.X86_64.Derive
end

/-! Save the register arguments into the local derivation frame. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def arguments : List (Nat × Reg) :=
  [(72, .r9), (80, .r8), (88, .rcx), (96, .rdx), (104, .rsi), (112, .rdi)]

def argumentValue (s : State) (r : Reg) : Addr :=
  if r = .rdi ∨ r = .r9 then ((s.gpr r).setWidth 32).setWidth 64 else s.gpr r

theorem Entered.argument {s t : State} (h : Entered s t) (r : Reg) (bp : r ≠ .rbp) :
    t.gpr r = argumentValue s r := by
  unfold argumentValue
  by_cases di : r = .rdi
  · subst r; rw [ite_eq_left (Or.inl rfl)]; exact h.kind
  · by_cases nine : r = .r9
    · subst r; rw [ite_eq_left (Or.inr rfl)]; exact h.passes
    · rw [ite_eq_right (by simp only [di, nine, or_self, not_false_eq_true])]
      exact h.regs r bp di nine

structure SetupDone (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rsp
  sp : t.gpr .rsp = s.gpr .rsp
  scratch : t.gpr .rbx = s.mem.readW (s.gpr .rsp + 248) 64
  values : ∀ arg ∈ arguments, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2
  regs : ∀ r ∈ calleeSaved, r ≠ .rbp → r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  frame : Frame [⟨s.gpr .rsp, 120⟩] s.mem t.mem

theorem setup_ok (s : State) (frameWrite : Covers [⟨s.gpr .rsp, 120⟩] s.wr)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 248) 8) :
    WP isa (.block Impl.Argon2.X86_64.Derive.setup) s (SetupDone s) := by
  change WP isa (.block (([.mov .rbp (.reg .rsp), .mov32 .rdi (.reg .rdi), .mov32 .r9 (.reg .r9)] : List Instr) ++
    (arguments.map fun arg => .store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2) ++
    ([.mov .rbx (.mem (Impl.Argon2.X86_64.at_ .rbp 248))] : List Instr))) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine (entry_ok s).mono ?_
  intro a entered
  rw [WP.block_append_iff]
  have write : ∀ arg ∈ arguments, InRegions a.wr (a.gpr .rbp + BitVec.ofNat 64 arg.1) 8 := by
    intro arg ha
    rw [entered.wr, entered.bp]
    apply frameWrite
    have bounds : ∀ arg ∈ arguments, arg.1 + 8 ≤ 120 := by decide
    exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (bounds arg ha) (by have := bounds arg ha; omega)⟩
  refine (stores_values_ok arguments a write (by decide) (by decide)).mono ?_
  rintro b ⟨saved, values⟩
  have bp : b.gpr .rbp = s.gpr .rsp := by rw [saved.regs, entered.bp]
  have scratchWord : b.mem.readW (b.gpr .rbp + 248) 64 = s.mem.readW (s.gpr .rsp + 248) 64 := by
    have kept := saved.other_word 248 (by decide) (by decide) (by decide)
    change b.mem.readW (b.gpr .rbp + 248) 64 = a.mem.readW (a.gpr .rbp + 248) 64 at kept
    rw [kept, entered.bp, entered.mem]
  refine (scratch_ok b (by rw [saved.rd, saved.wr, bp, entered.rd, entered.wr]; exact read)).mono ?_
  intro t loaded
  refine ⟨(loaded.regs .rbp (by decide)).trans bp, ?_, loaded.scratch.trans scratchWord, ?_, ?_,
    loaded.rd.trans (saved.rd.trans entered.rd), loaded.wr.trans (saved.wr.trans entered.wr),
    loaded.mxcsr.trans (saved.mxcsr.trans entered.mxcsr), ?_⟩
  · rw [loaded.regs .rsp (by decide), saved.regs]
    exact entered.regs .rsp (by decide) (by decide) (by decide)
  · intro arg ha
    rw [loaded.mem, loaded.regs .rbp (by decide), values arg ha]
    have notBp : ∀ arg ∈ arguments, arg.2 ≠ .rbp := by decide
    exact entered.argument arg.2 (notBp arg ha)
  · intro r hr hb hx
    have other : ∀ r ∈ calleeSaved, r ≠ .rdi ∧ r ≠ .r9 := by decide
    rw [loaded.regs r hx, saved.regs]
    exact entered.regs r hb (other r hr).1 (other r hr).2
  · rw [loaded.mem, ← entered.mem]
    have frame := saved.frame
    rw [entered.bp] at frame
    apply frame.sub
    intro region hr
    obtain ⟨arg, ha, rfl⟩ := List.mem_map.mp hr
    have bounds : ∀ arg ∈ arguments, arg.1 + 8 ≤ 120 := by decide
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (bounds arg ha)⟩

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DerivePrologue`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DerivePrivatePrepare`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DerivePrepare`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveNormalizeArgs`. -/
section
/-! Normalize distinct stack slots while retaining every other frame word. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def normalizedWord (s : State) (d : Nat) : Addr :=
  (((s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)

structure NormalizedArgs (s t : State) (ds : List Nat) : Prop where
  values : ∀ d ∈ ds, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 = normalizedWord s d
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  frame : Frame (ds.map fun d => (⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩ : Region)) s.mem t.mem

theorem NormalizedArgs.other_word {s t : State} {ds : List Nat} (h : NormalizedArgs s t ds)
    (e : Nat) (bound : e + 8 < 2 ^ 64)
    (separate : ∀ d ∈ ds, e + 8 ≤ d ∨ d + 8 ≤ e)
    (bounds : ∀ d ∈ ds, d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 e) 64 := by
  rw [h.regs .rbp (by decide)]
  apply h.frame.readW (r := ⟨s.gpr .rbp + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate d hd) (Nat.le_of_lt bound) (Nat.le_of_lt (bounds d hd))

theorem normalizeArgs_ok (ds : List Nat) (s : State)
    (read : ∀ d ∈ ds, InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 d) 8)
    (write : ∀ d ∈ ds, InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 d) 8)
    (separate : ds.Pairwise fun d e => d + 8 ≤ e ∨ e + 8 ≤ d)
    (bounds : ∀ d ∈ ds, d + 8 < 2 ^ 64) :
    WP isa (Impl.Argon2.X86_64.Derive.normalizeArgs ds) s (NormalizedArgs s · ds) := by
  induction ds generalizing s with
  | nil => exact WP.block_nil ⟨by simp, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons d ds ih =>
    cases ds with
    | nil =>
      refine (normalize_ok s d (read d (by simp)) (write d (by simp))).mono ?_
      intro t ht
      exact ⟨fun e he => by simp only [List.mem_singleton] at he; subst e; exact ht.word,
        ht.regs, ht.rd, ht.wr, ht.mxcsr, ht.frame⟩
    | cons e ds =>
      obtain ⟨headSep, tailSep⟩ := List.pairwise_cons.mp separate
      refine WP.seq ((normalize_ok s d (read d (List.mem_cons_self ..))
        (write d (List.mem_cons_self ..))).mono ?_)
      intro t ht
      refine (ih t
        (fun x hx => by rw [ht.rd, ht.wr, ht.regs .rbp (by decide)]; exact read x (List.mem_cons_of_mem d hx))
        (fun x hx => by rw [ht.wr, ht.regs .rbp (by decide)]; exact write x (List.mem_cons_of_mem d hx))
        tailSep (fun x hx => bounds x (List.mem_cons_of_mem d hx))).mono ?_
      intro u hu
      refine ⟨?_, fun r hr => (hu.regs r hr).trans (ht.regs r hr),
        hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.mxcsr.trans ht.mxcsr, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [hu.other_word x (bounds x (List.mem_cons_self ..)) headSep
            (fun a ha => bounds a (List.mem_cons_of_mem x ha))]
          exact ht.word
        · rw [hu.values x hx]
          unfold normalizedWord
          have sep : x + 8 ≤ d ∨ d + 8 ≤ x := (headSep x hx).symm
          rw [ht.other_word x sep (bounds x (List.mem_cons_of_mem d hx)) (bounds d (List.mem_cons_self ..))]
      · apply (ht.frame.mono ?_).trans
        · have frame := hu.frame
          rw [ht.regs .rbp (by decide)] at frame
          exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
        · intro region hr
          simp only [List.mem_singleton] at hr; subst region
          exact List.mem_cons_self ..

end VG.Proof.Argon2.X86_64.Derive
end

/-! Complete ABI preparation retains the inputs and exposes normalized public arguments. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def normalizedOffsets : List Nat := [176, 184, 192]

def prepareWrites (s : State) : List Region :=
  ⟨s.gpr .rsp, 120⟩ :: normalizedOffsets.map fun d => ⟨s.gpr .rsp + BitVec.ofNat 64 d, 8⟩

theorem SetupDone.other_word {s t : State} (h : SetupDone s t) (d : Nat)
    (afterFrame : 120 ≤ d) (bound : d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 d) 64 := by
  rw [h.bp]
  apply h.frame.readW (r := ⟨s.gpr .rsp + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  simp only [List.mem_singleton] at hr; subst region
  simpa only [BitVec.add_zero] using Offset.disjoint (s.gpr .rsp) (d := d) (n := 8) (e := 0) (k := 120)
    (Or.inr afterFrame) (Nat.le_of_lt bound) (by decide)

structure Prepared (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rsp
  sp : t.gpr .rsp = s.gpr .rsp
  scratch : t.gpr .rbx = s.mem.readW (s.gpr .rsp + 248) 64
  values : ∀ arg ∈ arguments, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2
  normalized : ∀ d ∈ normalizedOffsets, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 =
    (((s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)
  regs : ∀ r ∈ calleeSaved, r ≠ .rbp → r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  frame : Frame (prepareWrites s) s.mem t.mem

theorem Prepared.other_word {s t : State} (h : Prepared s t) (d : Nat)
    (afterFrame : 120 ≤ d) (bound : d + 8 < 2 ^ 64)
    (separate : ∀ e ∈ normalizedOffsets, d + 8 ≤ e ∨ e + 8 ≤ d) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 =
      s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 d) 64 := by
  rw [h.bp]
  apply h.frame.readW (r := ⟨s.gpr .rsp + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simpa only [BitVec.add_zero] using Offset.disjoint (s.gpr .rsp) (d := d) (n := 8) (e := 0) (k := 120)
      (Or.inr afterFrame) (Nat.le_of_lt bound) (by decide)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have bounds : ∀ e ∈ normalizedOffsets, e + 8 ≤ 2 ^ 64 := by decide
    exact Offset.disjoint _ (separate e he) (Nat.le_of_lt bound) (bounds e he)

theorem prepareLocal_ok (s : State) (frameWrite : Covers [⟨s.gpr .rsp, 120⟩] s.wr)
    (read : ∀ d ∈ 248 :: normalizedOffsets, InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 d) 8)
    (write : ∀ d ∈ normalizedOffsets, InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 d) 8) :
    WP isa Impl.Argon2.X86_64.Derive.prepareLocal s (Prepared s) := by
  unfold Impl.Argon2.X86_64.Derive.prepareLocal
  have scratchRead : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 248) 8 := read 248 (List.mem_cons_self ..)
  refine WP.seq ((setup_ok s frameWrite scratchRead).mono ?_)
  intro a setup
  refine (normalizeArgs_ok normalizedOffsets a
    (fun d hd => by rw [setup.rd, setup.wr, setup.bp]; exact read d (List.mem_cons_of_mem _ hd))
    (fun d hd => by rw [setup.wr, setup.bp]; exact write d hd) (by decide) (by decide)).mono ?_
  intro t normalized
  refine ⟨(normalized.regs .rbp (by decide)).trans setup.bp,
    (normalized.regs .rsp (by decide)).trans setup.sp,
    (normalized.regs .rbx (by decide)).trans setup.scratch, ?_, ?_, ?_,
    normalized.rd.trans setup.rd, normalized.wr.trans setup.wr, normalized.mxcsr.trans setup.mxcsr, ?_⟩
  · intro arg ha
    have bound : ∀ arg ∈ arguments, arg.1 + 8 < 2 ^ 64 := by decide
    have separate : ∀ arg ∈ arguments, ∀ d ∈ normalizedOffsets, arg.1 + 8 ≤ d ∨ d + 8 ≤ arg.1 := by decide
    rw [normalized.other_word arg.1 (bound arg ha) (separate arg ha) (by decide)]
    exact setup.values arg ha
  · intro d hd
    rw [normalized.values d hd]
    unfold normalizedWord
    have afterFrame : ∀ d ∈ normalizedOffsets, 120 ≤ d := by decide
    have bound : ∀ d ∈ normalizedOffsets, d + 8 < 2 ^ 64 := by decide
    rw [setup.other_word d (afterFrame d hd) (bound d hd)]
  · intro r hr hb hx
    have notAx : ∀ r ∈ calleeSaved, r ≠ .rax := by decide
    exact (normalized.regs r (notAx r hr)).trans (setup.regs r hr hb hx)
  · apply (setup.frame.mono (by
      intro region hr
      simp only [List.mem_singleton] at hr
      subst region
      exact List.mem_cons_self ..)).trans
    have frame := normalized.frame
    rw [setup.bp] at frame
    exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveCopyArgs`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveCopyArg`. -/
section
/-! Copy a read-only caller argument into the private derivation frame. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def copySource (j : Nat) : Nat := 328 + 8 * j
def copyDestination (j : Nat) : Nat := 176 + 8 * j

structure CopiedArg (s t : State) (j : Nat) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .rsp + BitVec.ofNat 64 (copyDestination j))
    (s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 64)
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem copyArg_ok (s : State) (j : Nat)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 8)
    (write : InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 (copyDestination j)) 8) :
    WP isa (.block (Impl.Argon2.X86_64.Derive.copyArg j)) s (CopiedArg s · j) := by
  change InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (328 + 8 * j)) 8 at read
  change InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 (176 + 8 * j)) 8 at write
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.Derive.copyArg, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.load64, State.store64, readSrc, State.ea, Impl.Argon2.X86_64.at_,
    BitVec.ofInt_natCast, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, read, write, reduceCtorEq,
    ite_true, ite_false, Option.some.injEq, Option.map_some, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  exact RegUpd.gpr_setReg_of_ne _ _ hr

theorem CopiedArg.frame {s t : State} {j : Nat} (h : CopiedArg s t j) :
    Frame [⟨s.gpr .rsp + BitVec.ofNat 64 (copyDestination j), 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem CopiedArg.word {s t : State} {j : Nat} (h : CopiedArg s t j) :
    t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 (copyDestination j)) 64 =
      s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 64 := by
  rw [h.regs .rsp (by decide), h.mem, Mem.readW_writeW_self64]

end VG.Proof.Argon2.X86_64.Derive
end

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
end

/-! Prepare private copies of every ABI argument, preserving caller-owned storage. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def privateWrites (s : State) : List Region := [⟨s.gpr .rsp, 120⟩, ⟨s.gpr .rsp + 176, 96⟩]

structure PrivatePrepared (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rsp
  sp : t.gpr .rsp = s.gpr .rsp
  scratch : t.gpr .rbx = s.mem.readW (s.gpr .rsp + 400) 64
  values : ∀ arg ∈ arguments, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2
  stackWords : ∀ j < 12, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 (copyDestination j)) 64 =
    let w := s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 64
    if j < 3 then (w.setWidth 32).setWidth 64 else w
  regs : ∀ r ∈ calleeSaved, r ≠ .rbp → r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (privateWrites s) s.mem t.mem

theorem private_prepare_ok (s : State) (locals : Covers [⟨s.gpr .rsp, 272⟩] s.wr)
    (read : ∀ j < 12, InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 8) :
    WP isa Impl.Argon2.X86_64.Derive.prepare s (PrivatePrepared s) := by
  have localWord : ∀ d, d + 8 ≤ 272 → InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 d) 8 := by
    intro d hd
    exact locals _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ hd (by omega)⟩
  unfold Impl.Argon2.X86_64.Derive.prepare Impl.Argon2.X86_64.Derive.copyArgs
  refine WP.seq ((copyArgs_ok (List.range 12) s
    (fun _ h => List.mem_range.mp h) List.nodup_range (fun j h => read j (List.mem_range.mp h))
    (fun j h => localWord _ (by have := List.mem_range.mp h; unfold copyDestination; omega))).mono ?_)
  intro a copied
  have sp := copied.regs .rsp (by decide)
  refine (prepareLocal_ok a (by
    intro p n h
    rw [copied.wr]
    rw [sp] at h
    apply locals p n
    exact Covers.of_sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨_, List.mem_singleton_self _, 0, (BitVec.add_zero _).symm, show 0 + 120 ≤ 272 by decide⟩) p n h)
    (by
      intro d hd
      rw [copied.rd, copied.wr, sp]
      have bound : ∀ d ∈ 248 :: normalizedOffsets, d + 8 ≤ 272 := by decide
      obtain ⟨region, member, contains⟩ := localWord d (bound d hd)
      exact ⟨region, List.mem_append_right _ member, contains⟩)
    (by
      intro d hd; rw [copied.wr, sp]
      have bound : ∀ d ∈ normalizedOffsets, d + 8 ≤ 272 := by decide
      exact localWord d (bound d hd))).mono ?_
  intro t prepared
  refine ⟨prepared.bp.trans sp, prepared.sp.trans sp, ?_, ?_, ?_, ?_,
    prepared.rd.trans copied.rd, prepared.wr.trans copied.wr, ?_⟩
  · have word := copied.values 9 (by decide)
    change a.mem.readW (a.gpr .rsp + 248) 64 = s.mem.readW (s.gpr .rsp + 400) 64 at word
    exact prepared.scratch.trans word
  · intro arg ha
    rw [prepared.values arg ha]
    unfold argumentValue
    have notAx : ∀ arg ∈ arguments, arg.2 ≠ .rax := by decide
    rw [copied.regs arg.2 (notAx arg ha)]
  · intro j hj
    by_cases small : j < 3
    · have slot : ∀ j < 3, copyDestination j ∈ normalizedOffsets := by decide
      rw [prepared.normalized _ (slot j small), copied.values j (List.mem_range.mpr hj), ite_eq_left small]
    · rw [ite_eq_right small, prepared.other_word _ (by unfold copyDestination; omega)
        (by unfold copyDestination; omega) (by
          intro d hd
          have upper : ∀ d ∈ normalizedOffsets, d + 8 ≤ 200 := by decide
          have := upper d hd; unfold copyDestination; omega)]
      exact copied.values j (List.mem_range.mpr hj)
  · intro r hr hb hx
    have notAx : ∀ r ∈ calleeSaved, r ≠ .rax := by decide
    exact (prepared.regs r hr hb hx).trans (copied.regs r (notAx r hr))
  · apply (copied.frame.sub ?_).trans (prepared.frame.sub ?_)
    · intro region hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have bound := List.mem_range.mp hj
      refine ⟨⟨s.gpr .rsp + 176, 96⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      unfold copyDestination
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact Offset.sub_base _ (by omega)
    · intro region hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [sp]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
        rw [sp]
        have bounds : ∀ d ∈ normalizedOffsets, 176 ≤ d ∧ d + 8 ≤ 272 := by decide
        obtain ⟨lo, hi⟩ := bounds d hd
        refine ⟨⟨s.gpr .rsp + 176, 96⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
        rw [show d = 176 + (d - 176) by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
        exact Offset.sub_base _ (by omega)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Private frame permissions and caller argument values after the ABI prologue. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def prologueState (s : State) : State := frameStart s Impl.Argon2.X86_64.Derive.saved

theorem prologue_sp (s : State) : (prologueState s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 320 :=
  frameStart_sp s _

theorem frameStart_locals (s : State) (rs : List Reg) :
    (⟨(frameStart s rs).gpr .rsp, 272⟩ : Region) ∈ (frameStart s rs).wr := by
  induction rs generalizing s with
  | nil => rw [frameStart, pushed_wr, pushed_rsp]; exact List.mem_cons_self ..
  | cons r rs ih => exact ih (pushed [r] s)

theorem prologue_locals (s : State) : Covers [⟨(prologueState s).gpr .rsp, 272⟩] (prologueState s).wr := by
  intro p n ⟨region, member, contains⟩
  simp only [List.mem_singleton] at member; subst region
  exact ⟨_, frameStart_locals s _, contains⟩

theorem prologue_source (s : State) (j : Nat) :
    (prologueState s).gpr .rsp + BitVec.ofNat 64 (copySource j) =
      s.gpr .rsp + BitVec.ofNat 64 (8 * (j + 1)) := by
  rw [prologue_sp]
  unfold copySource
  rw [show 328 + 8 * j = 320 + 8 * (j + 1) by omega,
    BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem prologue_reads {s : State} (h : AbiEnvironment s) :
    ∀ j < 12, InRegions ((prologueState s).rd ++ (prologueState s).wr)
      ((prologueState s).gpr .rsp + BitVec.ofNat 64 (copySource j)) 8 := by
  intro j hj
  rw [prologue_source]
  refine ⟨abiArguments s, List.mem_append_left _ ?_, ?_⟩
  · change abiArguments s ∈ (frameStart s Impl.Argon2.X86_64.Derive.saved).rd
    rw [frameStart_rd, h.rd]; exact List.mem_append_right _ (List.mem_singleton_self _)
  · unfold abiArguments
    rw [show 8 * (j + 1) = 8 + 8 * j by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact Offset.contains_base _ (by omega) (by omega)

theorem prologue_word {s : State} (h : AbiEnvironment s) (j : Nat) (hj : j < 12) :
    (prologueState s).mem.readW ((prologueState s).gpr .rsp + BitVec.ofNat 64 (copySource j)) 64 =
      abiWord s (8 * (j + 1)) := by
  rw [prologue_source]
  have frame := frameStart_frame s Impl.Argon2.X86_64.Derive.saved (by decide) (by
    have space := h.stack; change 320 ≤ (s.gpr .rsp).toNat; omega)
  apply frame.readW (r := abiArguments s) ?_ ?_ (by decide)
  · unfold abiArguments
    rw [show 8 * (j + 1) = 8 + 8 * j by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact Offset.contains_base _ (by omega) (by omega)
  · intro region hr
    simp only [List.mem_singleton] at hr; subst region
    unfold abiArguments
    exact Offset.disjoint_below _ (by decide)

theorem prologue_prepare (s : State) (h : AbiEnvironment s) :
    WP isa Impl.Argon2.X86_64.Derive.prepare (prologueState s) (PrivatePrepared (prologueState s)) :=
  private_prepare_ok _ (prologue_locals s) (prologue_reads h)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveMetadata`. -/
section
/-! The private frame contains the exact arguments decoded by the shared contract. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_stack_word {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (j : Nat) (hj : j < 12) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 (copyDestination j)) 64 =
      let word := abiWord s (8 * (j + 1))
      if j < 3 then (word.setWidth 32).setWidth 64 else word := by
  rw [prepared.stackWords j hj, prologue_word h j hj]

theorem private_argument_word {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (arg : Nat × Reg) (member : arg ∈ arguments) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2 := by
  rw [prepared.values arg member]
  unfold argumentValue
  have notSp : ∀ arg ∈ arguments, arg.2 ≠ .rsp := by decide
  unfold prologueState
  rw [frameStart_reg s _ arg.2 (notSp arg member)]

theorem private_local_write {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (d n : Nat) (bound : d + n ≤ 272) : InRegions t.wr (t.gpr .rbp + BitVec.ofNat 64 d) n := by
  rw [prepared.wr, prepared.bp]
  apply prologue_locals s
  exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ bound (by omega)⟩

theorem private_local_read {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (d n : Nat) (bound : d + n ≤ 272) :
    InRegions (t.rd ++ t.wr) (t.gpr .rbp + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := private_local_write prepared d n bound
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem private_parameters {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : Parameters.Ready (abiParams s) t := by
  refine ⟨private_local_read prepared 176 8 (by decide), private_local_read prepared 184 8 (by decide),
    ?_, ?_, h.valid.1, h.valid.2.2.2.2.2.1, h.valid.2.1⟩
  · have word := private_stack_word h prepared 0 (by decide)
    change t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 176) 64 =
      (((abiWord s 8).setWidth 32).setWidth 64) at word
    change t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 176) 64 =
      BitVec.ofNat 64 ((abiWord s 8).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]
  · have word := private_stack_word h prepared 1 (by decide)
    change t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 184) 64 =
      (((abiWord s 16).setWidth 32).setWidth 64) at word
    change t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 184) 64 =
      BitVec.ofNat 64 ((abiWord s 16).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]

end VG.Proof.Argon2.X86_64.Derive
end

/-! The private frame and called functions stay within the reviewed stack allowance. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem frameStart_wr_member (s : State) (rs : List Reg) (region : Region) (member : region ∈ s.wr) :
    region ∈ (frameStart s rs).wr := by
  induction rs generalizing s with
  | nil => rw [frameStart, pushed_wr]; exact List.mem_cons_of_mem _ member
  | cons r rs ih => apply ih; rw [pushed_wr]; exact List.mem_cons_of_mem _ member

theorem private_wr_member {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (region : Region) (member : region ∈ s.wr) : region ∈ t.wr := by
  rw [prepared.wr]
  exact frameStart_wr_member s _ region member

theorem private_bp {s t : State} (prepared : PrivatePrepared (prologueState s) t) :
    t.gpr .rbp = s.gpr .rsp - BitVec.ofNat 64 320 := prepared.bp.trans (prologue_sp s)

theorem private_sp {s t : State} (prepared : PrivatePrepared (prologueState s) t) :
    t.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 320 := prepared.sp.trans (prologue_sp s)

theorem private_frame_sub {s t : State} (prepared : PrivatePrepared (prologueState s) t) :
    Region.Sub ⟨t.gpr .rbp, 272⟩ (below (s.gpr .rsp) 344) := by
  rw [private_bp prepared]
  exact Offset.sub_below _ (by decide) (by decide)

theorem private_stack_sub {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (n : Nat) (bound : n ≤ 24) : Region.Sub (below (t.gpr .rsp) n) (below (s.gpr .rsp) 344) := by
  rw [private_sp prepared]
  unfold below
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  exact Offset.sub_below _ (by omega) (by omega)

theorem private_frame_disjoint {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (buffer : Region × Bool)
    (member : buffer ∈ abiBuffers s ++ [(abiArguments s, false)]) :
    (⟨t.gpr .rbp, 272⟩ : Region).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) buffer member).sub_left
    (private_frame_sub prepared)

theorem private_stack_disjoint {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (buffer : Region × Bool)
    (member : buffer ∈ abiBuffers s ++ [(abiArguments s, false)]) (n : Nat) (bound : n ≤ 24) :
    (below (t.gpr .rsp) n).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) buffer member).sub_left
    (private_stack_sub prepared n bound)

theorem private_frame_stack {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (n : Nat) (bound : n ≤ 24) : (⟨t.gpr .rbp, 272⟩ : Region).Disjoint (below (t.gpr .rsp) n) := by
  rw [prepared.bp, prepared.sp]
  exact Offset.base_disjoint_below _ (by omega)

theorem private_work_member {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : abiWork s ∈ t.wr := by
  apply private_wr_member prepared
  rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

end VG.Proof.Argon2.X86_64.Derive
