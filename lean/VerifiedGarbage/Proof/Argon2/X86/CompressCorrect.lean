import VerifiedGarbage.Proof.Argon2.X86.Compress

/-!
# Argon2 compression on x86 (32-bit): the whole function

`correct`: the prologue, the initialization, the rows and columns and the
epilogue, with the calling convention's obligations.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Impl.Argon2.X86 (prologue initWord finishWord epilogue savedOff)
open VG.Proof.Sha512.X86 (Acc rd64 ea_of)
open VG.Proof.Sha256.X86.Stream (contains_addr wp_movm)

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)
include hfit

theorem permR_sub : Region.Sub (permR B) ⟨B.setWidth 64, 4096⟩ := by
  show Region.Sub ⟨addr B 1024, 1024⟩ _
  rw [addr_off hfit (by decide)]
  exact Offset.sub_base _ (by decide)

/-- A word of `scratch` outside the permuted block is unchanged by its writes. -/
theorem outside_perm {m m' : Mem} (hf : Frame [permR B] m m') {d : Nat} (hd : d + 4 ≤ 4096)
    (ho : d + 4 ≤ 1024 ∨ 2048 ≤ d) : m'.readW (addr B d) 32 = m.readW (addr B d) 32 := by
  refine hf.readW (r := ⟨addr B d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  show Region.Disjoint _ ⟨addr B 1024, 1024⟩
  rw [addr_off hfit (by omega), addr_off hfit (by decide)]
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem low_perm {m m' : Mem} (hf : Frame [permR B] m m') : blk m' B 0 = blk m B 0 := by
  apply Vector.ext
  intro j hj
  simp only [blk, Vector.getElem_ofFn, rd64]
  rw [outside_perm hfit hf (by omega) (by omega), outside_perm hfit hf (by omega) (by omega)]

end

theorem words_zero {m : Mem} {B : BitVec 32} {f : Nat → BitVec 32} (h : Words m B 0 f 256) :
    blk m B 0 = ofWords f := blk_of_words fun i hi => h i hi

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Argon2.X86.compress s₀ fun t => abiPreserved s₀ t ∧ compressX86.post s₀ t := by
  have fits := hp.scr_fits
  unfold Impl.Argon2.X86.compress Impl.Argon2.X86.rounds
  refine WP.seq (WP.block_append ((prologue_ok hp).mono fun s₁ h₁ =>
    (init_ok hp h₁ 256 (Nat.le_refl _)).mono fun s₂ h₂ => ?_))
  have A₂ : At (scr s₀) s₂ := ⟨h₂.esi, hp.acc h₂.wr⟩
  refine WP.seq (WP.seq ((rounds_ok fits rowIndex Proof.Argon2.rowIndex_injective (List.finRange 8)
    A₂).mono fun s₃ st₃ => (rounds_ok fits colIndex Proof.Argon2.colIndex_injective
      (List.finRange 8) (A₂.of_step st₃)).mono fun s₄ st₄ => ?_))
  have k₄ := st₃.keep.trans st₄.keep
  have pf : Frame [permR (scr s₀)] s₂.mem s₄.mem := st₃.frame.trans st₄.frame
  have f₄ : Frame [outR s₀, scrR s₀] s₀.mem s₄.mem :=
    h₂.frame.trans (pf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, permR_sub fits⟩)
  have g₄ : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ecx → r ≠ .edx → s₄.gpr r = s₀.gpr r := fun r h0 h6 h1 h2 =>
    (k₄.gpr r (by simp [temps, h0, h1, h2])).trans (h₂.regs r h0 h6 h1 h2)
  have sp₄ : s₄.gpr .esp = esp₀ s₀ := g₄ _ (by decide) (by decide) (by decide) (by decide)
  unfold epilogue
  simp only [List.cons_append]
  refine wp_movm (ea_of sp₄ 12) (by rw [k₄.rd, k₄.wr, h₂.rd, h₂.wr]; exact hp.in_arg rfl (by omega) (by omega))
    fun s₅ u₅ => ?_
  have h₅ : FinInv s₀ s₄ s₅ 0 :=
    ⟨by rw [u₅.other _ (by decide), k₄.esi, h₂.esi], by rw [u₅.gpr, hp.arg_frame f₄ (by omega) (by omega)]; rfl,
      fun r _ h1 => u₅.other r h1, by rw [u₅.rd, k₄.rd, h₂.rd], by rw [u₅.wr, k₄.wr, h₂.wr],
      by rw [u₅.mem]; exact Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine WP.block_append ((finish_ok hp h₅ 256 (Nat.le_refl _)).mono fun s₆ h₆ => ?_)
  refine wp_movm (ea_of h₆.esi savedOff) (hp.in_scr h₆.wr (by decide)) fun t u => WP.block_nil ?_
  have ft : Frame [outR s₀, scrR s₀] s₀.mem t.mem := by
    rw [u.mem]
    exact f₄.trans (h₆.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  have gt : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ecx → r ≠ .edx → t.gpr r = s₀.gpr r := fun r h0 h6 h1 h2 => by
    rw [u.other r h6, h₆.regs r h0 h1, g₄ r h0 h6 h1 h2]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact gt _ (by decide) (by decide) (by decide) (by decide)
    · rw [u.gpr, hp.scr_frame h₆.frame (by decide), outside_perm fits pf (by decide) (by decide)]
      exact h₂.saved
    · exact gt _ (by decide) (by decide) (by decide) (by decide)
    · exact gt _ (by decide) (by decide) (by decide) (by decide)
    · exact gt _ (by decide) (by decide) (by decide) (by decide)
  · refine ft.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hp.ret_out, hp.ret_scr⟩
  · -- The output.
    have R₂ : blk s₂.mem (scr s₀) 0 = ofWords (xy s₀) := words_zero h₂.low
    have W₂ : working s₂.mem (scr s₀) = ofWords (xy s₀) := by
      rw [working_eq]; exact blk_of_words fun i hi => h₂.high i hi
    have X : xorBlock (blockAt s₀.mem ((xp s₀).setWidth 64)) (blockAt s₀.mem ((yp s₀).setWidth 64)) =
        ofWords (xy s₀) := by
      rw [blockAt_eq hp.x_fits, blockAt_eq hp.y_fits,
        blk_of_words (f := fun i => s₀.mem.readW (addr (xp s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]),
        blk_of_words (f := fun i => s₀.mem.readW (addr (yp s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]), xor_words]
      rfl
    have O : blk t.mem (op s₀) 0 = xorBlock (working s₄.mem (scr s₀)) (blk s₄.mem (scr s₀) 0) := by
      rw [u.mem, words_zero h₆.out, working_eq,
        blk_of_words (f := fun i => s₄.mem.readW (addr (scr s₀) (1024 + 4 * i)) 32) (fun _ _ => rfl),
        blk_of_words (f := fun i => s₄.mem.readW (addr (scr s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]), xor_words]
      rfl
    show blockAt t.mem ((op s₀).setWidth 64) = _
    rw [blockAt_eq hp.out_fits, O, low_perm fits pf, R₂, st₄.working, st₃.working, W₂, ← X]
    simp only [compress]

end VG.Proof.Argon2.X86
