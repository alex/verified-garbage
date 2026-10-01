import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Prune

/-! The frame wipe preserves the signature and the calling convention. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (stk)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey (ea_stk add_add)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem wipe_word {t : State} (hc : Ctx L g mx m₀ t) (i : Nat) (hi : i < 24) :
    WP isa (.block [.store (stk (8 * i)) .rax]) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [L.DATA] t.mem t'.mem := by
  have hw := hc.inFrW (d := 16 + 8 * i) (by omega) (by omega)
  have hf : Frame [L.DATA] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 (16 + 8 * i)) (t.gpr .rax)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, hc.rsp,
    add_add, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨hc.store (by decide) (by decide) rfl rfl rfl (fun _ _ => rfl) hf, hf⟩

theorem wipe_words (is : List Nat) (hi : ∀ i ∈ is, i < 24) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block (is.map fun i => .store (stk (8 * i)) .rax)) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [L.DATA] t.mem t'.mem := by
  induction is generalizing t with
  | nil => exact WP.of_runBlock ⟨t, rfl, hc, Frame.refl _ _⟩
  | cons i is ih =>
    change WP isa (.block (([.store (stk (8 * i)) .rax] : List Instr) ++
      is.map (fun j => .store (stk (8 * j)) .rax))) t _
    rw [WP.block_append_iff]
    refine WP.mono (wipe_word hc i (hi i (by simp))) fun u ⟨hu, hf⟩ => ?_
    exact WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem i hj)) hu)
      fun w ⟨hw, hf'⟩ => ⟨hw, hf.trans hf'⟩

theorem wipe_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block wipe) t fun t' => Ctx L g mx m₀ t' ∧ Frame [L.DATA] t.mem t'.mem := by
  rw [wipe, WP.block_append_iff]
  have hz : WP isa (.block [.alu32 .xor .rax (.reg .rax)]) t
      fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
      State.setReg32,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), rfl⟩
  refine WP.mono hz fun u ⟨hu, hm⟩ => ?_
  exact WP.mono (wipe_words (List.range 24) (fun _ h => List.mem_range.mp h) hu)
    fun w ⟨hw, hf⟩ => ⟨hw, hm ▸ hf⟩

end VG.Proof.Ed25519.X86_64.SignCached
