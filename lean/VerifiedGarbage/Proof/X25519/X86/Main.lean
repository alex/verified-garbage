import VerifiedGarbage.Proof.X25519.X86.Finish

/-!
# X25519 on x86 (32-bit): the whole function

The setup, the ladder, the last swap, the inversion and the result, composed:
`vg_x25519` writes `X25519(k, u)` to `out` (`x25519_eq`), and restores the
callee-saved registers.
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

theorem x25519_code : Impl.X25519.X86.x25519 =
    .seq (.block setup) (.seq (.seq (.block [.mov .esi (.imm 255)]) (.loop (.block step) .ne))
      (.seq (.block lastSwap) (.seq Impl.X25519.X86.invert (.block finish)))) := rfl

theorem finish_eq : finish = ops ([.mul X2 X2 T1] : List Op) ++ (freeze X2 ++ (.mov .esi (.mem (at_ .esp 4)) ::
    (((List.range 8).flatMap fun k => ([.mov .eax (.mem (sc (X2 + 4 * k))), .store (at_ .esi (4 * k)) .eax] :
      List Instr)) ++ restore))) := by
  simp only [finish, ops, List.flatMap_cons, List.flatMap_nil, Op.code, List.append_nil, List.append_assoc,
    List.cons_append]

/-- The result `r`, as the words of its value at `[x + X2]`, to `out`, and the registers restored. -/
theorem finish_ok {s₀ s : State} (hp : Pre s₀) (hb : Base (arg s₀ 3) (kOf s₀) s₀ s) :
    WP isa (.block finish) s fun s' => abiPreserved s₀ s' ∧
      Spec.X25519.bytesAt s'.mem ((arg s₀ 0).setWidth 64) 32 =
        encodeUCoordinate (F s.mem (arg s₀ 3) X2 * F s.mem (arg s₀ 3) T1) := by
  have hfit := hp.sc_fit
  rw [finish_eq]
  refine WP.block_append (WP.mono (ops_ok [.mul X2 X2 T1] hb.ctx (by decide)) fun s₁ ⟨k₁, f₁, e₁⟩ => ?_)
  have b₁ := hb.ops k₁ f₁
  refine WP.block_append (WP.mono (freeze_ok b₁.ctx (o := X2) (by decide)) fun s₂ ⟨k₂, f₂, e₂⟩ => ?_)
  have b₂ := b₁.ops k₂ f₂
  -- The value: fully reduced.
  have hv : fe s₂.mem (arg s₀ 3) X2 = (F s.mem (arg s₀ 3) X2 * F s.mem (arg s₀ 3) T1).val := by
    rw [e₂, ← toFe_val]
    have := e₁ X2 (by decide)
    simp only [X86.run, opOut, opVal, Function.update_self] at this
    exact congrArg Fin.val this
  refine Wp.wp_ldm (B := s₂.gpr .esp) (o := 4) rfl (by rw [b₂.esp, b₂.rd, b₂.wr]; exact hp.argIn (i := 0) (by decide))
    fun s₃ u₃ => ?_
  have o₃ : OInv s₀ s₃ 0 s₃ := ⟨by rw [u₃.other _ (by decide)]; exact b₂.ctx.edi,
    by rw [u₃.gpr, b₂.esp]; exact hp.arg_same b₂.frame (i := 0) (by decide), rfl, rfl, rfl, Frame.refl _ _,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have w₃ : s₃.wr = s₀.wr := by rw [u₃.wr, b₂.wr]
  refine WP.block_append (WP.mono (outWords_ok hp w₃ 8 (Nat.le_refl _) s₃ o₃) fun s₄ o₄ => ?_)
  have c₄ : Ctx (arg s₀ 3) s₄ := ⟨o₄.edi, hfit, by rw [o₄.wr, w₃]; exact hp.sc_in⟩
  refine WP.mono (restore_ok c₄) fun s₅ ⟨m₅, esp₅, ebx₅, esi₅, ebp₅, edi₅⟩ => ⟨?_, ?_⟩
  · -- The saved words, unchanged by the stores to `out`.
    have sv : ∀ j < 4, wd s₄.mem (arg s₀ 3) (4 * j) = s₀.gpr (savedReg j) := fun j hj => by
      rw [wd_frame o₄.frame fun r hr => by
        rw [List.mem_singleton.mp hr]
        refine Region.Disjoint.symm (hp.out_sc.sub_right ?_)
        rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by omega_using [hj]) (by omega_using [hj]),
        u₃.mem]
      exact b₂.saved j hj
    refine ⟨fun r hr => ?_, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [ebx₅]; exact sv 0 (by decide)
      · rw [esi₅]; exact sv 1 (by decide)
      · rw [edi₅]; exact sv 2 (by decide)
      · rw [ebp₅]; exact sv 3 (by decide)
      · rw [esp₅, o₄.esp, u₃.other _ (by decide), b₂.esp]
    · rw [m₅]
      have r₄ : s₄.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₃.mem.readW ((s₀.gpr .esp).setWidth 64) 32 :=
        o₄.frame.readW (Region.contains_self _ _) (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_out)
          (by decide)
      rw [r₄, u₃.mem]
      exact b₂.frame.readW (Region.contains_self _ _) (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_sc)
        (by decide)
  · rw [m₅, encodeUCoordinate_eq]
    refine bytesAt_leBytes_words32 _ _ _ fun j hj => ?_
    have hof := hp.out_fit
    rw [← addr_eq (by omega_using [hof, hj]), ← wd, o₄.words j hj, u₃.mem, ← hv, Nat.pow_mul]
    exact (num_digit j (f := fun k => wv s₂.mem (arg s₀ 3) (X2 + 4 * k)) (fun _ _ => wv_lt _ _ _) hj).symm

theorem ladderAfter_255_eq (k : Nat) (x1 : Fe) :
    ladderAfter k x1 255 = { x2 := 1, z2 := 0, x3 := x1, z3 := 1, swap := 0 } := rfl

/-- The function's correctness. -/
theorem x25519_correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.X25519.X86.x25519 s₀ fun s' => abiPreserved s₀ s' ∧ Proof.X25519.x25519X86.post s₀ s' := by
  rw [x25519_code]
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨b₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁⟩ => ?_)
  refine WP.seq (WP.seq (Wp.wp_movi fun s₂ u₂ => WP.block_nil ?_))
  have b₂ : Base (arg s₀ 3) (kOf s₀) s₀ s₂ := b₁.of_frame (o := 288) (n := 640) (u₂.other _ (by decide))
    (u₂.other _ (by decide)) u₂.rd u₂.wr (by rw [u₂.mem]; exact Frame.refl _ _) (by decide) (by decide)
    (.inr (Nat.le_refl _)) (by decide)
  have L₂ : LInv (arg s₀ 3) (kOf s₀) (uOf s₀) s₀ 255 s₂ :=
    ⟨b₂, u₂.gpr, by rw [u₂.mem]; exact x1₁, by rw [u₂.mem, ladderAfter_255_eq]; exact x2₁,
      by rw [u₂.mem, ladderAfter_255_eq]; exact z2₁, by rw [u₂.mem, ladderAfter_255_eq]; exact x3₁,
      by rw [u₂.mem, ladderAfter_255_eq]; exact z3₁, by rw [u₂.mem, ladderAfter_255_eq]; exact sw₁⟩
  refine WP.mono (ladderLoop_ok L₂) fun s₃ L₃ => ?_
  refine WP.seq (WP.mono (lastSwap_ok L₃) fun s₄ ⟨b₄, x2₄, z2₄⟩ => ?_)
  refine WP.seq (WP.mono (invert_ok b₄) fun s₅ ⟨b₅, t1₅, x2₅⟩ => ?_)
  refine WP.mono (finish_ok hp b₅) fun s₆ ⟨abi, out⟩ => ⟨abi, ?_⟩
  show Spec.X25519.bytesAt s₆.mem ((arg s₀ 0).setWidth 64) 32 = _
  rw [out, t1₅, x2₅, x2₄, z2₄, x25519_eq]

end VG.Proof.X25519.X86
