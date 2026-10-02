import VerifiedGarbage.Proof.Aes.X86.AesNi.Arith
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd

/-! AES-NI round execution on IA-32. Register updates stay folded; the same
proof applies to any distinct block registers other than the key temporary. -/
namespace VG.Proof.Aes.X86.AesNi
open VG.X86
open VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ keyOp round aes)
open VG.Spec.Aes (roundKey bytesAt cipher)

structure XFrame (rs : List XReg) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem XFrame.refl (rs : List XReg) (s : State) : XFrame rs s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem XFrame.trans {rs : List XReg} {s s' s'' : State}
    (h : XFrame rs s s') (h' : XFrame rs s' s'') : XFrame rs s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr => (h'.xmm r hr).trans (h.xmm r hr)⟩

theorem XFrame.mono {rs rs' : List XReg} {s s' : State}
    (h : XFrame rs s s') (hs : ∀ r ∈ rs, r ∈ rs') : XFrame rs' s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

theorem map_ok (op : XBinOp) : ∀ (regs : List XReg) (s : State),
    regs.Nodup → .xmm6 ∉ regs →
    WP isa (.block (regs.map fun b => .xop (.bin op b .xmm6))) s fun s' =>
      (∀ b ∈ regs, s'.xmm b = op.eval (s.xmm b) (s.xmm .xmm6)) ∧ XFrame regs s s'
  | [], s, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, XFrame.refl _ _⟩
  | b :: bs, s, hnd, h6 => by
    have hb6 : b ≠ .xmm6 := fun h => h6 (h ▸ List.mem_cons_self ..)
    have h6' : .xmm6 ∉ bs := fun h => h6 (List.mem_cons_of_mem _ h)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [List.map_cons, WP.block_cons_iff]
    refine ⟨s.setXmm b (op.eval (s.xmm b) (s.xmm .xmm6)), rfl, ?_⟩
    refine WP.mono (map_ok op bs _ (List.nodup_cons.mp hnd).2 h6')
      fun s' ⟨hv, hf⟩ => ⟨?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [hf.xmm _ hbs, xmm_setXmm_self]
      · have hcb : c ≠ b := fun h => hbs (h ▸ hc)
        rw [hv c hc, xmm_setXmm_of_ne _ _ hcb,
          xmm_setXmm_of_ne _ _ (Ne.symm hb6)]
    · refine ⟨hf.gpr, hf.mem, hf.rd, hf.wr, fun r hr => ?_⟩
      simp only [List.mem_cons, not_or] at hr
      rw [hf.xmm r hr.2, xmm_setXmm_of_ne _ _ hr.1]

theorem keyOp_ok (regs : List XReg) (op : XBinOp) (off : Nat) (s : State)
    (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .eax off)) 16) :
    WP isa (.block (keyOp regs op off)) s fun s' =>
      (∀ b ∈ regs, s'.xmm b = op.eval (s.xmm b)
        (s.mem.readW (s.ea (at_ .eax off)) 128)) ∧ XFrame (.xmm6 :: regs) s s' := by
  rw [keyOp, WP.block_cons_iff]
  refine ⟨s.setXmm .xmm6 (s.mem.readW (s.ea (at_ .eax off)) 128), by
    simp only [isa, exec, State.load128, hin, ite_true, Option.map_some], ?_⟩
  refine WP.mono (map_ok op regs _ hnd h6) fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, ?_⟩
  · have hb6 : b ≠ .xmm6 := fun h => h6 (h ▸ hb)
    rw [hv b hb, xmm_setXmm_of_ne _ _ hb6, xmm_setXmm_self]
  · refine ⟨hf.gpr, hf.mem, hf.rd, hf.wr, fun r hr => ?_⟩
    simp only [List.mem_cons, not_or] at hr
    rw [hf.xmm r hr.2, xmm_setXmm_of_ne _ _ hr.1]

def RInv (regs : List XReg) (w : List Byte) (x : XReg → Spec.Aes.State)
    (k : Nat) (s : State) : Prop := ∀ b ∈ regs, st (s.xmm b) = rnds w (x b) k

/-- The readable schedule and its byte representation. The ABI proof discharges
these facts using the public schedule address and its nonwrapping region. -/
structure Keys (nr : Nat) (w : List Byte) (s : State) : Prop where
  le : nr ≤ 14
  keys : ∀ j ≤ nr, InRegions (s.rd ++ s.wr) (s.ea (at_ .eax (16 * j))) 16
  bytes : ∀ j ≤ nr, ∀ i < 16,
    byte (s.mem.readW (s.ea (at_ .eax (16 * j))) 128) i = (roundKey w j).getD i 0

theorem Keys.of_frame {nr : Nat} {w : List Byte} {rs : List XReg} {s s' : State}
    (h : Keys nr w s) (hf : XFrame rs s s') : Keys nr w s' :=
  ⟨h.le, by simp only [State.ea, hf.rd, hf.wr, hf.gpr]; exact h.keys,
    by simp only [State.ea, hf.mem, hf.gpr]; exact h.bytes⟩

theorem round_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs)
    {nr : Nat} {w : List Byte} {x : XReg → Spec.Aes.State} {k : Nat}
    (hk : k + 1 ≤ nr) {s : State} (hK : Keys nr w s) (hI : RInv regs w x k s) :
    WP isa (.block (round regs (k + 1))) s fun s' =>
      RInv regs w x (k + 1) s' ∧ XFrame (.xmm6 :: regs) s s' := by
  refine WP.mono (keyOp_ok regs .aesenc _ s hnd h6 (hK.keys _ hk))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, aesenc_st _ _ (roundKey w (k + 1)) (hK.bytes _ hk), hI b hb, rnds_succ]

theorem rounds_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs)
    {nr : Nat} {w : List Byte} {x : XReg → Spec.Aes.State} (k : Nat) (s : State)
    (hk : k ≤ nr) (hK : Keys nr w s) (hI : RInv regs w x 0 s) :
    WP isa (.block ((List.range k).flatMap fun j => round regs (j + 1))) s fun s' =>
      RInv regs w x k s' ∧ XFrame (.xmm6 :: regs) s s' := by
  induction k with
  | zero => rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, XFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (round_ok regs hnd h6 (k := k) (by omega) (hK.of_frame hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩

theorem start_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs)
    {nr : Nat} {w : List Byte} (s : State) (hK : Keys nr w s) :
    WP isa (.block (keyOp regs .pxor 0)) s fun s' =>
      RInv regs w (fun b => st (s.xmm b)) 0 s' ∧ XFrame (.xmm6 :: regs) s s' := by
  refine WP.mono (keyOp_ok regs .pxor 0 s hnd h6 (hK.keys 0 (Nat.zero_le _)))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, pxor_st _ _ (roundKey w 0) (hK.bytes 0 (Nat.zero_le _)), rnds_zero]

theorem last_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs)
    {nr : Nat} {w : List Byte} {x : XReg → Spec.Aes.State} (s : State)
    (hK : Keys nr w s) (hI : RInv regs w x (nr - 1) s) :
    WP isa (.block (keyOp regs .aesenclast (16 * nr))) s fun s' =>
      (∀ b ∈ regs, st (s'.xmm b) = cipher nr w (x b)) ∧ XFrame (.xmm6 :: regs) s s' := by
  refine WP.mono (keyOp_ok regs .aesenclast _ s hnd h6 (hK.keys nr (Nat.le_refl _)))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, aesenclast_st _ _ (roundKey w nr) (hK.bytes nr (Nat.le_refl _)),
    hI b hb, cipher_eq]

theorem cmpEcx_ok (s : State) (c : BitVec 32) :
    WP isa (.block [.alu .cmp .ecx (.imm c)]) s fun s' =>
      s'.zf = some (s.gpr .ecx - c == 0) ∧ XFrame [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    isa, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, gpr_arithFlags .., mem_arithFlags .., rd_arithFlags ..,
    wr_arithFlags .., fun _ _ => congrFun (xmm_arithFlags ..) _⟩

theorem two_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs)
    {nr : Nat} {w : List Byte} {x : XReg → Spec.Aes.State} {k : Nat}
    (hk : k + 2 ≤ nr) {s : State} (hK : Keys nr w s) (hI : RInv regs w x k s) :
    WP isa (.block (round regs (k + 1) ++ round regs (k + 2))) s fun s' =>
      RInv regs w x (k + 2) s' ∧ XFrame (.xmm6 :: regs) s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (round_ok regs hnd h6 (k := k) (by omega) hK hI) fun s₁ ⟨hI₁, hf₁⟩ => ?_
  exact WP.mono (round_ok regs hnd h6 (k := k + 1) (by omega) (hK.of_frame hf₁) hI₁)
    fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩

theorem aes_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs)
    {nr : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte}
    (s : State) (hK : Keys nr w s) (hc : s.gpr .ecx = BitVec.ofNat 32 nr) :
    WP isa (aes regs) s fun s' =>
      (∀ b ∈ regs, st (s'.xmm b) = cipher nr w (st (s.xmm b))) ∧
      XFrame (.xmm6 :: regs) s s' := by
  let x := fun b => st (s.xmm b)
  have hstart : WP isa (.block (keyOp regs .pxor 0 ++
      (List.range 9).flatMap (fun j => round regs (j + 1)))) s fun s' =>
      RInv regs w x 9 s' ∧ XFrame (.xmm6 :: regs) s s' := by
    rw [WP.block_append_iff]
    refine WP.mono (start_ok regs hnd h6 s hK) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    have hn : 9 ≤ nr := by rcases hnr with h | h | h <;> omega
    exact WP.mono (rounds_ok regs hnd h6 9 s₁ hn (hK.of_frame hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩
  unfold aes
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono hstart fun s₁ ⟨hI₁, hf₁⟩ => ?_
  refine WP.mono (cmpEcx_ok s₁ 10) fun s₂ ⟨hz₂, hf₂⟩ => ?_
  have hf₀₂ := hf₁.trans (hf₂.mono (by simp))
  have hK₂ := hK.of_frame hf₀₂
  have hI₂ : RInv regs w x 9 s₂ := fun b hb => by
    rw [hf₂.xmm b (by simp)]; exact hI₁ b hb
  rcases hnr with rfl | rfl | rfl
  · refine WP.ite true (by simp [eval, hz₂, hf₁.gpr, hc]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact WP.mono (last_ok regs hnd h6 s₂ hK₂ hI₂)
      fun s' ⟨hv, hf⟩ => ⟨hv, hf₀₂.trans hf⟩
  all_goals
    refine WP.ite false (by simp [eval, hz₂, hf₁.gpr, hc]) (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (two_ok regs hnd h6 (k := 9) (by decide) hK₂ hI₂)
      fun s₃ ⟨hI₃, hf₃⟩ => ?_
    refine WP.mono (cmpEcx_ok s₃ 12)
      fun s₄ ⟨hz₄, hf₄⟩ => ?_
    have hf₀₄ := hf₀₂.trans (hf₃.trans (hf₄.mono (by simp)))
    have hK₄ := hK.of_frame hf₀₄
    have hI₄ : RInv regs w x 11 s₄ := fun b hb => by
      rw [hf₄.xmm b (by simp)]; exact hI₃ b hb
  · refine WP.ite true (by simp [eval, hz₄, hf₃.gpr, hf₀₂.gpr, hc]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact WP.mono (last_ok regs hnd h6 s₄ hK₄ hI₄)
      fun s' ⟨hv, hf⟩ => ⟨hv, hf₀₄.trans hf⟩
  · refine WP.ite false (by simp [eval, hz₄, hf₃.gpr, hf₀₂.gpr, hc]) (fun h => absurd h (by decide)) fun _ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (two_ok regs hnd h6 (k := 11) (by decide) hK₄ hI₄)
      fun s₅ ⟨hI₅, hf₅⟩ => ?_
    exact WP.mono (last_ok regs hnd h6 s₅ (hK₄.of_frame hf₅) hI₅)
      fun s' ⟨hv, hf⟩ => ⟨hv, hf₀₄.trans (hf₅.trans hf)⟩

end VG.Proof.Aes.X86.AesNi
