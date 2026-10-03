import VerifiedGarbage.Proof.Argon2.X86.CompressContract

/-!
# Argon2 compression on x86 (32-bit): correctness

The prologue (`prologue_ok`), the initialization of both halves of scratch
with X XOR Y (`init_ok`, one word at a time), the rows and columns
(`Proof/Argon2/X86/Rounds.lean`), and the epilogue writing the output and
restoring `esi` (`epilogue_ok`): `correct`.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Impl.Argon2.X86 (prologue initWord finishWord epilogue savedOff)
open VG.Proof.Sha512.X86 (Acc rd64 mem_rd ea_of)
open VG.Proof.Sha256.X86.Stream (contains_addr Upd Mupd wp_movm wp_store wp_mov readW_writeW_addr)

/-- 32-bit word `i` of X XOR Y. -/
def xy (s₀ : State) (i : Nat) : BitVec 32 :=
  s₀.mem.readW (addr (xp s₀) (4 * i)) 32 ^^^ s₀.mem.readW (addr (yp s₀) (4 * i)) 32

/-- After the prologue and the first `n` words of the initialization. -/
structure InitInv (s₀ s : State) (n : Nat) : Prop where
  esi : s.gpr .esi = scr s₀
  ecx : s.gpr .ecx = xp s₀
  edx : s.gpr .edx = yp s₀
  regs : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [outR s₀, scrR s₀] s₀.mem s.mem
  saved : s.mem.readW (addr (scr s₀) savedOff) 32 = s₀.gpr .esi
  low : Words s.mem (scr s₀) 0 (xy s₀) n
  high : Words s.mem (scr s₀) 1024 (xy s₀) n

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem scr_contains {d : Nat} (hd : d + 4 ≤ 4096) : (scrR s₀).Contains (addr (scr s₀) d) (32 / 8) :=
  contains_addr hd (by omega) hp.scr_fits

theorem prologue_ok :
    WP isa (.block prologue) s₀ (InitInv s₀ · 0) := by
  have hm : scrR s₀ ∈ [outR s₀, scrR s₀] := by simp
  unfold prologue
  refine wp_movm (ea_of rfl 16) (hp.in_arg (d := 16) rfl (by omega) (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (ea_of e₁ savedOff) (by rw [u₁.wr]; exact hp.acc rfl _ (by decide)) fun s₂ u₂ => ?_
  have f₂ : Frame [outR s₀, scrR s₀] s₀.mem s₂.mem := by
    rw [u₂.mem, u₁.mem]; exact (Frame.refl _ _).writeW hm _ (scr_contains hp (by decide))
  refine wp_mov fun s₃ u₃ => ?_
  have sp₃ : s₃.gpr .esp = esp₀ s₀ := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  refine wp_movm (ea_of sp₃ 4) (by rw [u₃.rd, u₂.rd, u₁.rd, u₃.wr, u₂.wr, u₁.wr]; exact hp.in_arg (d := 4) rfl (by omega) (by omega))
    fun s₄ u₄ => ?_
  refine wp_movm (ea_of (by rw [u₄.other _ (by decide), sp₃]) 8)
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hp.in_arg (d := 8) rfl (by omega) (by omega)) fun s₅ u₅ => ?_
  have m₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  refine WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero _),
    fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, e₁]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, hp.arg_frame f₂ (by omega) (by omega)]; rfl
  · rw [u₅.gpr, u₄.mem, u₃.mem, hp.arg_frame f₂ (by omega) (by omega)]; rfl
  · intro r h0 h6 h1 h2
    rw [u₅.other _ h2, u₄.other _ h1, u₃.other _ h6, u₂.gpr, u₁.other _ h0]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [m₅]; exact f₂
  · rw [m₅, u₂.mem, Mem.readW_writeW_self32, u₁.other _ (by decide)]

/-- One word of the initialization. -/
theorem initWord_ok {s : State} {n : Nat} (hn : n < 256) (h : InitInv s₀ s n) :
    WP isa (.block (initWord n)) s (InitInv s₀ · (n + 1)) := by
  have hm : scrR s₀ ∈ [outR s₀, scrR s₀] := by simp
  have fits := hp.scr_fits
  unfold initWord
  refine wp_movm (ea_of h.ecx _) (hp.in_x h.rd (by omega)) fun s₁ u₁ => ?_
  refine VG.Proof.Sha512.X86.wp_xorS (VG.Proof.Sha512.X86.readSrc_mem
    (by rw [u₁.other _ (by decide), h.edx]) (by rw [u₁.rd, u₁.wr]; exact hp.in_y h.rd (by omega)))
    fun s₂ u₂ => ?_
  have v₂ : s₂.gpr .eax = xy s₀ n := by
    rw [u₂.gpr, u₁.gpr, u₁.mem, hp.x_frame h.frame (by omega), hp.y_frame h.frame (by omega)]; rfl
  have esi₂ : s₂.gpr .esi = scr s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esi]
  refine wp_store (ea_of esi₂ _) (by rw [u₂.wr, u₁.wr, h.wr]; exact hp.acc rfl _ (by omega))
    fun s₃ u₃ => ?_
  have w₃ : InRegions s₃.wr (addr (scr s₀) (1024 + 4 * n)) 4 := by
    rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hp.acc rfl _ (by omega)
  refine wp_store (ea_of (by rw [u₃.gpr, esi₂]) _) w₃ fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = (s.mem.writeW (addr (scr s₀) (4 * n)) (xy s₀ n)).writeW
      (addr (scr s₀) (1024 + 4 * n)) (xy s₀ n) := by
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.mem, v₂]
  have r₄ : ∀ e, e + 4 ≤ 4096 → (e + 4 ≤ 4 * n ∨ 4 * n + 4 ≤ e) →
      (e + 4 ≤ 1024 + 4 * n ∨ 1024 + 4 * n + 4 ≤ e) →
      s₄.mem.readW (addr (scr s₀) e) 32 = s.mem.readW (addr (scr s₀) e) 32 := by
    intro e he h1 h2
    rw [m₄, readW_writeW_addr _ _ (by omega) (by omega) h2,
      readW_writeW_addr _ _ (by omega) (by omega) h1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.gpr, u₃.gpr, esi₂]
  · rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
  · rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.edx]
  · intro r h0 h6 h1 h2
    rw [u₄.gpr, u₃.gpr, u₂.other _ h0, u₁.other _ h0, h.regs r h0 h6 h1 h2]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [m₄]
    exact (h.frame.writeW hm _ (scr_contains hp (by omega))).writeW hm _ (scr_contains hp (by omega))
  · rw [r₄ _ (by decide) (by simp only [savedOff]; omega) (by simp only [savedOff]; omega)]
    exact h.saved
  · intro i hi
    by_cases e : i = n
    · subst e
      rw [m₄, readW_writeW_addr _ _ (by omega) (by omega) (by omega), Nat.zero_add,
        Mem.readW_writeW_self32]
    · rw [r₄ _ (by omega) (by omega) (by omega)]; exact h.low i (by omega)
  · intro i hi
    by_cases e : i = n
    · subst e; rw [m₄, Mem.readW_writeW_self32]
    · rw [r₄ _ (by omega) (by omega) (by omega)]; exact h.high i (by omega)

theorem init_ok {s : State} (h : InitInv s₀ s 0) (n : Nat) (hn : n ≤ 256) :
    WP isa (.block ((List.range n).flatMap initWord)) s (InitInv s₀ · n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact WP.block_append ((ih (by omega)).mono fun t ht => initWord_ok hp (by omega) ht)

end

/-! ## The epilogue -/

/-- Word `i` of the output: the permuted block XOR R, in memory `m`. -/
def outWord (B : BitVec 32) (m : Mem) (i : Nat) : BitVec 32 :=
  m.readW (addr B (1024 + 4 * i)) 32 ^^^ m.readW (addr B (4 * i)) 32

/-- After the first `n` words of the output, from the state `s₄` after the rounds. -/
structure FinInv (s₀ s₄ s : State) (n : Nat) : Prop where
  esi : s.gpr .esi = scr s₀
  ecx : s.gpr .ecx = op s₀
  regs : ∀ r, r ≠ .eax → r ≠ .ecx → s.gpr r = s₄.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [outR s₀] s₄.mem s.mem
  out : Words s.mem (op s₀) 0 (outWord (scr s₀) s₄.mem) n

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem finishWord_ok {s₄ s : State} {n : Nat} (hn : n < 256) (h : FinInv s₀ s₄ s n) :
    WP isa (.block (finishWord n)) s (FinInv s₀ s₄ · (n + 1)) := by
  have hm : outR s₀ ∈ [outR s₀] := List.mem_singleton_self _
  have fits := hp.out_fits
  unfold finishWord
  refine wp_movm (ea_of h.esi _) (hp.in_scr h.wr (by omega)) fun s₁ u₁ => ?_
  refine VG.Proof.Sha512.X86.wp_xorS (VG.Proof.Sha512.X86.readSrc_mem
    (by rw [u₁.other _ (by decide), h.esi]) (by rw [u₁.rd, u₁.wr]; exact hp.in_scr h.wr (by omega)))
    fun s₂ u₂ => ?_
  have v₂ : s₂.gpr .eax = outWord (scr s₀) s₄.mem n := by
    rw [u₂.gpr, u₁.gpr, u₁.mem, hp.scr_frame h.frame (by omega), hp.scr_frame h.frame (by omega)]; rfl
  refine wp_store (ea_of (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]) _)
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hp.out_wr rfl (by omega)) fun s₃ u₃ => WP.block_nil ?_
  have m₃ : s₃.mem = s.mem.writeW (addr (op s₀) (4 * n)) (outWord (scr s₀) s₄.mem n) := by
    rw [u₃.mem, u₂.mem, u₁.mem, v₂]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.esi]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
  · intro r h0 h1
    rw [u₃.gpr, u₂.other _ h0, u₁.other _ h0, h.regs r h0 h1]
  · rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [m₃]; exact h.frame.writeW hm _ (contains_addr (by omega) (by omega) fits)
  · intro i hi
    rw [m₃, Nat.zero_add]
    by_cases e : i = n
    · subst e; rw [Mem.readW_writeW_self32]
    · rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega)]
      have := h.out i (by omega); rwa [Nat.zero_add] at this

theorem finish_ok {s₄ s : State} (h : FinInv s₀ s₄ s 0) (n : Nat) (hn : n ≤ 256) :
    WP isa (.block ((List.range n).flatMap finishWord)) s (FinInv s₀ s₄ · n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact WP.block_append ((ih (by omega)).mono fun t ht => finishWord_ok hp (by omega) ht)

end

end VG.Proof.Argon2.X86
