import VerifiedGarbage.Proof.Ed25519.X86.ScalarByte

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open VG.Spec.Ed25519 (L)

structure ScalarKeep (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem ScalarKeep.refl (s : State) : ScalarKeep s s := ⟨rfl, rfl, rfl, rfl⟩
theorem ScalarKeep.trans {s t u : State} (h : ScalarKeep s t) (k : ScalarKeep t u) : ScalarKeep s u :=
  ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd, k.wr.trans h.wr⟩
theorem ScalarKeep.ctx {x : BitVec 32} {s t : State} (h : ScalarKeep s t) (hc : Ctx x s) : Ctx x t :=
  hc.keep h.edi h.wr

theorem Keep.scalar {s t : State} (h : Keep s t) : ScalarKeep s t := ⟨h.edi, h.esp, h.rd, h.wr⟩
theorem scalarUpd {s t : State} {r : Reg} {v : BitVec 32} (h : Wp.Upd s t r v)
    (hr : r ≠ .edi ∧ r ≠ .esp := by decide) : ScalarKeep s t :=
  ⟨h.other _ hr.1.symm, h.other _ hr.2.symm, h.rd, h.wr⟩

theorem scalar_ld8 {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {o : Nat} {a : Addr}
    (ha : addr (s.gpr b) o = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ t, Wp.Upd s t d ((s.mem a).setWidth 32) → WP isa (.block is) t Q) :
    WP isa (.block (.movzx8 d ⟨b, o⟩ :: is)) s Q := by
  refine Wp.cons (s' := s.setReg d ((s.mem a).setWidth 32)) ?_ (k _ (Wp.Upd.setReg _ _ _))
  change Option.map _ (if InRegions (s.rd ++ s.wr) (addr (s.gpr b) o) 1 then
    some (s.mem (addr (s.gpr b) o)) else none) = _
  simp only [ha, hin, ite_true, Option.map_some]

theorem scalarRead_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {n : Nat} (hn : n < 64)
    (hs : s.gpr .esi = BitVec.ofNat 32 (n + 1)) :
    WP isa (.block scalarRead) s fun t => ScalarKeep s t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
      Frame [sub x 32 4] s.mem t.mem ∧ wv t.mem x 32 = 2 * (s.mem (addr x (128 + n))).toNat := by
  refine Wp.wp_subi fun s₁ h₁ _ _ => Wp.wp_mov fun s₂ h₂ => Wp.wp_add fun s₃ h₃ _ => ?_
  have e₁ : s₁.gpr .esi = BitVec.ofNat 32 n := by
    rw [h₁.gpr, hs]
    exact (Wp.ofNat_pred (by omega_using [])).trans (congrArg (BitVec.ofNat 32) (by omega_using []))
  have k₃ := (scalarUpd h₁).trans ((scalarUpd h₂).trans (scalarUpd h₃))
  have c₃ := k₃.ctx hc
  have a₃ : addr (s₃.gpr .eax) 128 = addr x (128 + n) := by
    rw [h₃.gpr, h₂.gpr, h₂.other .esi (by decide), e₁, h₁.other .edi (by decide), hc.edi]
    simp only [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm n 128]
  refine scalar_ld8 a₃ (c₃.inRW (by omega_using [hn]) (by decide)) fun s₄ h₄ => ?_
  refine Wp.wp_add fun s₅ h₅ _ => ?_
  have c₅ := ((scalarUpd h₄).trans (scalarUpd h₅)).ctx c₃
  refine Wp.wp_stm c₅.edi (c₅.inW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  have m₅ : s₅.mem = s.mem := by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨k₃.trans ((scalarUpd h₄).trans ((scalarUpd h₅).trans
    ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩)), ?_, ?_, ?_⟩
  · rw [ht.gpr, h₅.other .esi (by decide), h₄.other .esi (by decide), h₃.other .esi (by decide),
      h₂.other .esi (by decide), e₁]
  · rw [ht.mem, m₅]
    exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  · rw [ht.mem, wv, wd_write_self, h₅.gpr, h₄.gpr, h₃.mem, h₂.mem, h₁.mem,
      BitVec.toNat_add, BitVec.toNat_setWidth_of_le (by decide)]
    have hb := (s.mem (addr x (128 + n))).isLt
    rw [Nat.mod_eq_of_lt (by omega_using [hb])]
    omega_using []

def scalarBodyFrame (x : BitVec 32) : List Region := sub x 32 4 :: scalarFrame x

theorem scalarTest_ok (s : State) :
    WP isa (.block [.alu .test .esi (.reg .esi)]) s fun t =>
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.zf = some (s.gpr .esi == 0) := by
  refine Wp.wp_test fun t ht hz => WP.block_nil ?_
  exact ⟨ht.gpr, ht.mem, ht.rd, ht.wr, by rw [hz, BitVec.and_self]⟩

theorem scalarByte_ok {x : BitVec 32} {s : State} (hc : Ctx x s) {n : Nat} (hn : n < 64)
    (hs : s.gpr .esi = BitVec.ofNat 32 (n + 1)) (hr : fe s.mem x scalarR < L) :
    WP isa (.block scalarByte) s fun t => ScalarKeep s t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
      t.zf = some (decide (n = 0)) ∧ Frame (scalarBodyFrame x) s.mem t.mem ∧
      fe t.mem x scalarR = (256 * fe s.mem x scalarR + (s.mem (addr x (128 + n))).toNat) % L := by
  simp only [scalarByte, List.append_assoc]
  refine WP.block_append (WP.mono (scalarRead_ok hc hn hs) fun u ⟨ku, su, fu, eu⟩ => ?_)
  have vu : fe u.mem x scalarR = fe s.mem x scalarR :=
    fe_frame1 fu hc.fit (by decide) (by decide) (Or.inr (by decide))
  have bu : wv u.mem x 32 / 2 = (s.mem (addr x (128 + n))).toNat := by rw [eu]; omega_using []
  refine WP.block_append (WP.mono (scalarEight_ok (ku.ctx hc) (vu ▸ hr)
    (by rw [bu]; exact BitVec.isLt _)) fun v ⟨kv, fv, ev⟩ => ?_)
  refine WP.mono (scalarTest_ok v) fun t ⟨gt, mt, rt, wt, zt⟩ => ?_
  have st : t.gpr .esi = BitVec.ofNat 32 n := by rw [gt, kv.esi, su]
  refine ⟨ku.trans (kv.scalar.trans ⟨by rw [gt], by rw [gt], rt, wt⟩), st, ?_, ?_, ?_⟩
  · rw [zt, kv.esi, su, Wp.ofNat_beq_zero (by omega_using [hn])]
  · rw [mt]
    exact (fu.mono fun r h => by simp only [List.mem_singleton] at h; exact h ▸ List.mem_cons_self).trans
      (fv.mono fun r h => List.mem_cons_of_mem _ h)
  · rw [mt, ev, vu, bu]
end VG.Proof.Ed25519.X86
