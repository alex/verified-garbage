import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Blocks
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce

/-!
# Deterministic ECDSA on x86-64: the messages of steps d, f and h.3

`V ‖ b`, and `‖ d ‖ h` if `full`, at `scratch + 1024` (`msg_ok`): `V` copied
from the frame (`head_ok`), the byte `b`, then the private key and `h`
copied (`tail_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

variable {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

/-- 32 bytes copied to `scratch + d` by `copy4`, with `Ctx` kept. -/
theorem copy_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : Addr} (hs : u.gpr src = S)
    (hsr : src ≠ .rax) (hdi : u.gpr .rdi = L.scr) {so d : Nat} (hd : d + 32 ≤ 8192)
    (hr : ∀ j < 4, InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + 8 * j)) 8)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, 32⟩ ⟨L.scr + BitVec.ofNat 64 d, 32⟩) :
    WP isa (.block (Cfg.copy4 src so .rdi d)) u fun u' => Ctx L g m₀ u' ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 d, 32⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 d) 32 = Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) 32 :=
  WP.mono (copyN_ok (by decide) hsr hsep (by have := hL.nc; omega) 4 (by omega) u hs hdi hr
    fun j hj => hc.inScrW (by omega)) fun u' ⟨hrd, hwr, hg, hf, hb⟩ =>
    ⟨hc.keep hL hrd hwr (hg _ (by decide)) (fun r hr _ => hg r (ne_cs hr (by decide))) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L hd),
      hrd, hwr, hg, hf, hb⟩

theorem fr_add (B : Addr) (o : Nat) : B + BitVec.ofNat 64 24 + BitVec.ofNat 64 o = B + BitVec.ofNat 64 (24 + o) :=
  Offset.add_add _ _ _

/-- The pointers: `scratch` in `rdi`, `d` in `rsi`. -/
theorem ptrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.msgPtrs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .rdi = L.scr ∧
      u.gpr .rsi = L.d := by
  have h128 := hc.inFr (d := 128) (by omega) (by omega)
  have h144 := hc.inFr (d := 144) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [Cfg.msgPtrs, fScratch, fD, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_stk, hc.rsp, Offset.add_add, Nat.reduceAdd, h128, h144, ite_true, Option.map_some, hc.pScr, hc.pD,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, reduceCtorEq, ite_false,
    Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs hL rfl rfl rfl (by cs_tac), by triv, by triv, by triv⟩

/-- `V ‖ b`, with `scratch` in `rdi`. -/
theorem head_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.scr) (b : Nat) :
    WP isa (.block (Cfg.copy4 .rsp fV .rdi sMsg ++
      ([.mov32 .rax (.imm (BitVec.ofNat 32 b)), .store8 (at_ .rdi (sMsg + 32)) .rax] : List Instr))) t fun u =>
      Ctx L g m₀ u ∧ (∀ r, r ≠ .rax → u.gpr r = t.gpr r) ∧
      Frame [⟨L.scr + BitVec.ofNat 64 1024, 33⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 1024) 33 =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 56) 32 ++ [BitVec.ofNat 8 b] := by
  simp only [fV, sMsg, Nat.reduceAdd]
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok hL hc (S := L.B + BitVec.ofNat 64 24) (src := .rsp) hc.rsp (by decide) hdi
    (so := 32) (d := 1024) (by decide) (fun j hj => by rw [fr_add]; exact hc.inFr (by omega) (by omega))
    (by rw [fr_add]; exact hL.stk_scr (by decide) (by decide))) fun u₂ ⟨hc₂, hrd₂, hwr₂, hg₂, hf₂, hb₂⟩ => ?_
  have hdi₂ : u₂.gpr .rdi = L.scr := (hg₂ _ (by decide)).trans hdi
  have w := hc₂.inScrW (o := 1056) (n := 1) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, State.store8, ea_at,
    RegUpd.gpr_setReg, reduceCtorEq, ite_false, RegUpd.mem_setReg, hdi₂,
    RegUpd.wr_setReg, w, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  have hb8 : ((BitVec.ofNat 32 b).setWidth 64).setWidth 8 = BitVec.ofNat 8 b := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [hb8]
  have hf₃ : Frame [⟨L.scr + BitVec.ofNat 64 1056, 1⟩] u₂.mem (u₂.mem.writeW (L.scr + BitVec.ofNat 64 1056) (BitVec.ofNat 8 b)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc₂.keep hL rfl rfl (by trivial)
      (fun r hr hr' => by first | trivial | rfl | exact RegUpd.gpr_setReg_of_ne _ _ (ne_cs hr (by decide))) hf₃
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega)),
    fun r hr => ?_, ?_, ?_⟩
  · simp only [hr, ite_false]; exact hg₂ r hr
  · refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
  · rw [show (33 : Nat) = 32 + 1 from rfl, Proof.Hmac.Common.bytesAt_add, Offset.add_add]
    have e₁ : Spec.Sha256.bytesAt (u₂.mem.writeW (L.scr + BitVec.ofNat 64 1056) (BitVec.ofNat 8 b))
        (L.scr + BitVec.ofNat 64 1024) 32 = Spec.Sha256.bytesAt u₂.mem (L.scr + BitVec.ofNat 64 1024) 32 :=
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    rw [e₁, hb₂, fr_add, show 24 + 32 = 56 from rfl, show 1024 + 32 = 1056 from rfl]
    refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 56) 32 ++ y) ?_
    show [(u₂.mem.writeW (L.scr + BitVec.ofNat 64 1056) (BitVec.ofNat 8 b)) (L.scr + BitVec.ofNat 64 1056 + BitVec.ofNat 64 0)] = _
    rw [add_ofNat_zero, WriteBytes.writeW8_apply]; simp

/-- `‖ d ‖ h`, with `scratch` in `rdi` and `d` in `rsi`. -/
theorem tail_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hdi : u.gpr .rdi = L.scr) (hsi : u.gpr .rsi = L.d) :
    WP isa (.block (Cfg.copy4 .rsi 0 .rdi (sMsg + 33) ++ Cfg.copy4 .rsp fH .rdi (sMsg + 65))) u fun u' =>
      Ctx L g m₀ u' ∧ Frame [⟨L.scr + BitVec.ofNat 64 1057, 64⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 1057) 64 =
        Spec.Sha256.bytesAt u.mem L.d 32 ++ Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 88) 32 := by
  simp only [fH, sMsg, Nat.reduceAdd]
  rw [WP.block_append_iff]
  have hu₁ : Upd L g m₀ u .rsi L.d u := ⟨hc, rfl, hsi, fun _ _ => rfl⟩
  have hdi₁ : u.gpr .rdi = L.scr := hdi
  refine WP.mono (copy_ok hL hu₁.ctx (u := u) (src := .rsi) hu₁.val (by decide) hdi₁ (so := 0) (d := 1057) (by decide)
    (fun j hj => hu₁.ctx.inD (by omega)) (by rw [add_ofNat_zero]; exact hL.dc.sub_right (Offset.sub_base _ (by omega))))
    fun u₂ ⟨hc₂, hrd₂, hwr₂, hg₂, hf₂, hb₂⟩ => ?_
  have hdi₂ : u₂.gpr .rdi = L.scr := (hg₂ _ (by decide)).trans hdi₁
  refine WP.mono (copy_ok hL hc₂ (S := L.B + BitVec.ofNat 64 24) (src := .rsp) hc₂.rsp (by decide) hdi₂
    (so := 64) (d := 1089) (by decide) (fun j hj => by rw [fr_add]; exact hc₂.inFr (by omega) (by omega))
    (by rw [fr_add]; exact hL.stk_scr (by decide) (by decide))) fun u₃ ⟨hc₃, _, _, _, hf₃, hb₃⟩ => ?_
  refine ⟨hc₃, ?_, ?_⟩
  · rw [← hu₁.mem]
    refine (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub _ (by omega) (by omega)
  · rw [Proof.Hmac.Common.bytesAt_add _ _ 32 32, Offset.add_add,
      show 1057 + 32 = 1089 from rfl, hb₃, fr_add, show 24 + 64 = 88 from rfl,
      bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb₂, add_ofNat_zero, hu₁.mem]
    refine congrArg (fun y => Spec.Sha256.bytesAt u.mem L.d 32 ++ y) ?_
    rw [← hu₁.mem]
    exact bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega) (by omega)) (by omega)

/-- The message `V ‖ b` (`‖ d ‖ h` if `full`) at `scratch + 1024`. -/
theorem msg_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .rdi = L.scr) (hsi : t.gpr .rsi = L.d)
    (b : Nat) (full : Bool) :
    WP isa (.block (Cfg.msg b full)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 1024, 97⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 1024) (if full then 97 else 33) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 56) 32 ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d 32 ++ Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 88) 32
          else []) := by
  cases full
  · simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil]
    refine WP.mono (head_ok hL hc hdi b) fun u ⟨hcu, _, hf, hb⟩ => ⟨hcu, hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, hb⟩
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub _ (by omega) (by omega)
  · simp only [Cfg.msg, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (head_ok hL hc hdi b) fun u ⟨hcu, hg, hf, hb⟩ =>
      WP.mono (tail_ok hL hcu ((hg _ (by decide)).trans hdi) ((hg _ (by decide)).trans hsi))
      fun u' ⟨hcu', hf', hb'⟩ => ⟨hcu', ?_, ?_⟩
    · refine (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega) (by omega)
      · simp only [List.mem_singleton] at hr; subst hr
        exact Offset.sub _ (by omega) (by omega)
    · rw [Proof.Hmac.Common.bytesAt_add _ _ 33 64, Offset.add_add, show 1024 + 33 = 1057 from rfl, hb',
        bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb, List.append_assoc]
      refine congrArg (fun y => Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 56) 32 ++ [BitVec.ofNat 8 b] ++ y) ?_
      rw [bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hL.dc.sub_right (Offset.sub_base _ (by omega))) (by omega),
        bytesAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hL.stk_scr (by omega) (by omega)) (by omega)]

end VG.Proof.Ecdsa.Rfc6979.X86_64
