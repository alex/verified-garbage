import VerifiedGarbage.Proof.AesGcm.Arm.StreamVerify
import VerifiedGarbage.Proof.AesGcm.Arm.Init

/-!
# AES-GCM on ARMv7: the pieces of `vg_aes_gcm_seal` and `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. Both keep a streaming state at
`W + 16`: the entry saves our caller's registers (`one1_wp`), `oneAad` writes
`J₀` and absorbs the additional data, padded (`oneAad_ok`), `oneCrypt` runs
counter mode over the data from the first counter block (`oneCrypt_ok`), and
`oneTag o` absorbs the data as ciphertext, padded, then the lengths block,
and writes the tag to `W + o` (`oneTag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ghashInput fullTag zeros padLen j0 inc32 gctr ghash ghashFrom blocks
  toBytes ofBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

section
variable {n : Nat}

/-- The state, at `W + 16`. -/
abbrev oSt (s₀ : State) : BitVec 32 := arg s₀ 4 + BitVec.ofNat 32 16

theorem oneLay {s₀ : State} (h : onePre n s₀) : Lay (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp := by
  obtain ⟨-, -, -, dcW, -, -, -, -, -, -, -, bc, -, -, -, bW, fc, -, -, -, fW, sp8, -, -⟩ := h
  exact initLay fc fW sp8 dcW bc bW

theorem oSt_addr {s₀ : State} (h : onePre n s₀) :
    State.addr (oSt s₀) = State.addr (arg s₀ 4) + BitVec.ofNat 64 16 :=
  addr_add (by have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega)

/-- A buffer apart from `W` is apart from the state. -/
theorem oSt_disj {s₀ : State} (h : onePre n s₀) {R : Region} (hR : R.Disjoint ⟨State.addr (arg s₀ 4), 2560⟩) :
    R.Disjoint ⟨State.addr (oSt s₀), 80⟩ := by
  rw [oSt_addr h]; exact hR.sub_right (Lay.wSub (by decide))

/-- After the entry, from `s₀`. -/
structure SO1 (n : Nat) (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₀.gpr .r7) (s₀.gpr .r1) s₁
  r4 : s₁.gpr .r4 = s₀.gpr .r2
  r5 : s₁.gpr .r5 = s₀.gpr .r3
  args : ArgsKeep n s₀ s₁
  saved : SavedAt s₁.mem (arg s₀ 4) s₀
  frame : Frame [savedR (arg s₀ 4)] s₀.mem s₁.mem

theorem one1_wp {s₀ : State} (h : onePre n s₀) (hn : 5 ≤ n) {Q : State → Prop} (k : ∀ s₁, SO1 n s₀ s₁ → Q s₁) :
    WP isa (.block oneEntry) s₀ Q := by
  have hst := oSt_addr h
  have ww := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, dWA, -, -, -, -, -, -, -, -, -, fW, -, spf, -⟩ := h
  have hA : ∀ r ∈ [savedR (arg s₀ 4)], (args s₀ n).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) := by
    rw [hrd]; exact covers_of_mem (by simp)
  have hW : Covers [⟨State.addr (arg s₀ 4), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hS : Covers [⟨State.addr (oSt s₀), 80⟩] s₀.wr := by rw [hst]; exact covers_off hW (by decide) (by decide)
  have ha : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * 4))) 4 :=
    arg_in (n := n) (by omega) spf (by rw [hrd]; simp)
  refine entry_ok (off := 16) (by decide) ha fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  have hk : ArgsKeep n s₀ s₁ := (ArgsKeep.refl n s₀).frame spf fr hA sp rd wr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, ?_, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact hk.of_eq rfl rfl rfl rfl

end

theorem abs16_sub {st w sp : BitVec 32} : ∀ r ∈ absFrame st w sp 16, ∃ r' ∈ j0Frame st w sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem t16_sub {st w sp : BitVec 32} : ∀ r ∈ tFrame st w sp 16, ∃ r' ∈ j0Frame st w sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem abs16_j0Frame {st w sp : BitVec 32} {m m' : Mem} (h : Frame (absFrame st w sp 16) m m') :
    Frame (j0Frame st w sp) m m' := h.sub abs16_sub

theorem t16_j0Frame {st w sp : BitVec 32} {m m' : Mem} (h : Frame (tFrame st w sp 16) m m') :
    Frame (j0Frame st w sp) m m' := h.sub t16_sub

section
variable {n : Nat}

/-- The stack arguments are apart from what `j0` (and the other pieces) write. -/
theorem one_argsJ0 {s₀ : State} (h : onePre n s₀) :
    ∀ r ∈ j0Frame (oSt s₀) (arg s₀ 4) s₀.sp, (args s₀ n).Disjoint r := by
  have hst := oSt_addr h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [hst]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

/-- A buffer apart from `W` and the stack below `sp` is apart from what `j0` writes. -/
theorem one_dataJ0 {s₀ : State} (h : onePre n s₀) {R : Region} (hW : R.Disjoint ⟨State.addr (arg s₀ 4), 2560⟩)
    (hb : (below s₀.sp).Disjoint R) : ∀ r ∈ j0Frame (oSt s₀) (arg s₀ 4) s₀.sp, R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact oSt_disj h hW
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hb.symm

/-- After `oneAad`, from `m₁`. -/
structure OA (n : Nat) (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  env : ∃ k7, Env (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp k7 (s₀.gpr .r1) s
  args : ArgsKeep n s₀ s
  j : blockAt s.mem (State.addr (oSt s₀)) =
    j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)
  cb : blockAt s.mem (State.addr (oSt s₀) + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat))
  abs : Absorbed s.mem (State.addr (oSt s₀) + BitVec.ofNat 64 16) (State.addr (oSt s₀) + BitVec.ofNat 64 32)
    (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    (bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat ++
      zeros (padLen (bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat).length))
  hH : blockAt s.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0))
  frame : Frame (j0Frame (oSt s₀) (arg s₀ 4) s₀.sp) m₁ s.mem

theorem oneAad_ok {s₀ s₁ : State} (h : onePre n s₀) (hn : 5 ≤ n) (h1 : SO1 n s₀ s₁) :
    WP isa oneAad s₁ (OA n s₀ s₁.mem) := by
  have L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ n ∈ s₀.rd := by rw [h.1]; simp
  have hp := h
  obtain ⟨hrd, -, -, -, -, dnW, -, daW, -, -, -, -, bn, ba, -, -, -, fn, fa, -, -, -, -, -⟩ := hp
  have hH₁ := ctxH_keep h1.frame (ctx_saved L)
  have ji : J0In (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp (s₀.gpr .r7) (s₀.gpr .r1)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (s₀.gpr .r2) (s₀.gpr .r3).toNat s₁ :=
    ⟨h1.env, hH₁, h1.r4, by rw [h1.r5]; simp, ⟨by rw [h1.args.rd, h1.args.wr, hrd]; exact covers_of_mem (by simp),
      (s₀.gpr .r3).isLt, fn, oSt_disj h dnW, dnW, bn⟩⟩
  refine WP.seq (WP.mono (WP.with_rdwr (j0_ok L ji)) fun s₂ hh => ?_)
  obtain ⟨jo, rd₂, wr₂, sp₂⟩ := hh
  obtain ⟨k7, he₂⟩ := jo.env
  have hiv : bytesAt s₁.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat =
      bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat :=
    bytesAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnW.sub_right (Lay.wSub (by decide))) (by omega)
  rw [hiv] at jo
  have hk₂ := h1.args.frame spf jo.frame (one_argsJ0 h) sp₂ rd₂ wr₂
  obtain ⟨a0, v0⟩ := hk₂.at spf hin 0 (by omega) (show 4 * 0 = 0 from rfl)
  obtain ⟨a1, v1⟩ := hk₂.at spf hin 1 (by omega) (show 4 * 1 = 4 from rfl)
  obtain ⟨s₃, run₃, h4₃, h5₃, h6₃, g₃, k₃⟩ : ∃ s₃, runBlock isa [.ldrSp .r4 0, .ldrSp .r5 4, .mov .r6 (imm 0)] s₂ =
      some s₃ ∧ s₃.gpr .r4 = arg s₀ 0 ∧ s₃.gpr .r5 = arg s₀ 1 ∧ s₃.gpr .r6 = BitVec.ofNat 32 0 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    refine ⟨_, by arun [a0, v0, a1, v1], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, v0]
    · simp [gpr_setReg, v1]
    · simp [gpr_setReg]
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide) (by decide)) k₃.sp k₃.rd k₃.wr
  have hk₃ := hk₂.of_eq k₃.mem k₃.sp k₃.rd k₃.wr
  have hda : DataOk (oSt s₀) (arg s₀ 4) s₀.sp s₃ (arg s₀ 0) (arg s₀ 1).toNat :=
    ⟨by rw [hk₃.rd, hk₃.wr, hrd]; exact covers_of_mem (by simp), (arg s₀ 1).isLt, fa, oSt_disj h daW, daW, ba⟩
  have haad : bytesAt s₃.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat := by
    rw [k₃.mem, bytesAt_frame jo.frame (one_dataJ0 h daW ba) (by omega),
      bytesAt_frame h1.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact daW.sub_right (Lay.wSub (by decide))) (by omega)]
  have ai : AbsIn (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp k7 (s₀.gpr .r1) 16 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) []
      (arg s₀ 0) (arg s₀ 1).toNat s₃ :=
    ⟨he₃, h4₃, by rw [h5₃]; simp, by rw [h6₃]; rfl, hda, by rw [k₃.mem]; exact jo.hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) ai)) fun s₄ hh => ?_)
  obtain ⟨ab, rd₄, wr₄, sp₄⟩ := hh
  rw [haad, List.nil_append] at ab
  have hk₄ := hk₃.frame spf ab.frame (disj_sub (one_argsJ0 h) abs16_sub) sp₄ rd₄ wr₄
  obtain ⟨b1, w1⟩ := hk₄.at spf hin 1 (by omega) (show 4 * 1 = 4 from rfl)
  obtain ⟨s₅, run₅, h6₅, g₅, k₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r6 4, .dp .and .r6 .r6 (imm 15)] s₄ = some s₅ ∧
      s₅.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 1).toNat % 16) ∧ (∀ r, r ≠ .r6 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [b1, w1], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, w1, and15]
    · intro r x; simp [gpr_setReg, x]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := ab.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide)) k₅.sp k₅.rd k₅.wr
  have hk₅ := hk₄.of_eq k₅.mem k₅.sp k₅.rd k₅.wr
  have hH₄ : blockAt s₄.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl)), k₃.mem]; exact jo.hH
  refine WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl)
    (x := bytesAt s₀.mem (State.addr (arg s₀ 0)) (arg s₀ 1).toNat) (H := ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    ⟨he₅, by rw [k₅.mem]; exact hH₄⟩ (by rw [h6₅, length_bytesAt]))) fun s₆ hh => ?_
  obtain ⟨fl, rd₆, wr₆, sp₆⟩ := hh
  rw [k₅.mem] at fl
  have keepA : ∀ {d : Nat}, (d = 0 ∨ d = 48) → ∀ r ∈ absFrame (oSt s₀) (arg s₀ 4) s₀.sp 16,
      (⟨State.addr (oSt s₀) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.st_st (by omega) (by omega) (by decide)
    · exact Lay.st_st (by omega) (by omega) (by decide)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by omega)).symm
  have keepT : ∀ {d : Nat}, (d = 0 ∨ d = 48) → ∀ r ∈ tFrame (oSt s₀) (arg s₀ 4) s₀.sp 16,
      (⟨State.addr (oSt s₀) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.st_st (by omega) (by omega) (by decide)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by omega)).symm
  have blk : ∀ {d : Nat}, (d = 0 ∨ d = 48) → blockAt s₆.mem (State.addr (oSt s₀) + BitVec.ofNat 64 d) =
      blockAt s₂.mem (State.addr (oSt s₀) + BitVec.ofNat 64 d) := fun hd => by
    rw [blockAt_frame fl.frame (keepT hd), blockAt_frame ab.frame (keepA hd), k₃.mem]
  refine ⟨⟨k7, fl.env⟩, hk₄.frame spf fl.frame (disj_sub (one_argsJ0 h) t16_sub) (sp₆.trans k₅.sp) (rd₆.trans k₅.rd)
    (wr₆.trans k₅.wr), ?_, ?_, ?_, fl.hH, ?_⟩
  · have := blk (d := 0) (.inl rfl); rw [add_ofNat_zero] at this; rw [this]; exact jo.j0
  · rw [blk (.inr rfl)]; exact jo.cb
  · exact fl.abs (ab.abs (by rw [k₃.mem]; exact Proof.Gcm.absorbed_nil _ jo.y))
  · rw [k₃.mem] at ab
    exact (jo.frame.trans (abs16_j0Frame ab.frame)).trans (t16_j0Frame fl.frame)

/-- The data, for `crypt` and `absorb`. -/
theorem one_dataOk {s₀ s : State} (h : onePre n s₀) (hk : ArgsKeep n s₀ s) :
    DataOk (oSt s₀) (arg s₀ 4) s₀.sp s (arg s₀ 2) (arg s₀ 3).toNat := by
  have hp := h
  obtain ⟨-, hwr, -, -, -, -, -, -, dDW, -, -, -, -, -, bD, -, -, -, -, fD, -, -, -, -⟩ := hp
  exact ⟨by rw [hk.rd, hk.wr, hwr]; exact covers_left (covers_of_mem (by simp)), (arg s₀ 3).isLt, fD,
    oSt_disj h dDW, dDW, bD⟩

theorem dataArgs_run {s₀ s : State} (hk : ArgsKeep n s₀ s) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    (hin : args s₀ n ∈ s₀.rd) (hn : 5 ≤ n) :
    ∃ s', runBlock isa dataArgs s = some s' ∧ s'.gpr .r4 = arg s₀ 2 ∧ s'.gpr .r5 = arg s₀ 3 ∧
      s'.gpr .r6 = BitVec.ofNat 32 0 ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨a2, v2⟩ := hk.at hf hin 2 (by omega) (show 4 * 2 = 8 from rfl)
  obtain ⟨a3, v3⟩ := hk.at hf hin 3 (by omega) (show 4 * 3 = 12 from rfl)
  refine ⟨_, by simp only [dataArgs]; arun [a2, v2, a3, v3], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v2]
  · simp [gpr_setReg, v3]
  · simp [gpr_setReg]
  · intro r x y z; simp [gpr_setReg, x, y, z]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- After `oneCrypt`, from `m₀`. -/
structure OC (n : Nat) (s₀ : State) (k7 : BitVec 32) (icb : Block) (m₀ : Mem) (s : State) : Prop where
  env : Env (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp k7 (s₀.gpr .r1) s
  args : ArgsKeep n s₀ s
  out : bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
    gctr (ciphOf m₀ (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) icb (bytesAt m₀ (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)
  frame : Frame (crFrame (oSt s₀) (arg s₀ 4) s₀.sp (arg s₀ 2) (arg s₀ 3).toNat) m₀ s.mem

theorem oneCrypt_ok {s₀ s : State} (h : onePre n s₀) (hn : 5 ≤ n) {k7 : BitVec 32}
    (he : Env (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp k7 (s₀.gpr .r1) s) (hk : ArgsKeep n s₀ s) {icb : Block}
    (hcb : blockAt s.mem (State.addr (oSt s₀) + BitVec.ofNat 64 48) = icb) :
    WP isa oneCrypt s (OC n s₀ k7 icb s.mem) := by
  have L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ n ∈ s₀.rd := by rw [h.1]; simp
  have dcD := h.2.2.1
  have hwr := h.2.1
  obtain ⟨s₁, run₁, h4, h5, h6, g₁, k₁⟩ := dataArgs_run hk spf hin hn
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have hk₁ := hk.of_eq k₁.mem k₁.sp k₁.rd k₁.wr
  have ci : CrIn (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp k7 (s₀.gpr .r1) (s₀.gpr .r1).toNat icb 0 (arg s₀ 2)
      (arg s₀ 3).toNat s₁ :=
    ⟨he₁, h4, by rw [h5]; simp, by rw [h6], by rw [he₁.r8]; simp, hR,
      ⟨one_dataOk h hk₁, by rw [hk₁.wr, hwr]; exact covers_of_mem (by simp), dcD⟩⟩
  refine WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₂ hh => ?_
  obtain ⟨co, rd₂, wr₂, sp₂⟩ := hh
  have hA : ∀ r ∈ crFrame (oSt s₀) (arg s₀ 4) s₀.sp (arg s₀ 2) (arg s₀ 3).toNat, (args s₀ n).Disjoint r := by
    have hst := oSt_addr h
    obtain ⟨-, -, -, -, -, -, -, -, -, dDA, dWA, -⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact dDA.symm
    · rw [hst, add_ofNat_assoc]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
    · exact (dWA.sub_left (Lay.wSub (by decide))).symm
    · exact (below_args s₀ spf).symm
  rw [k₁.mem] at co
  have c0 := Proof.Gcm.ctr_zero s.mem _ (State.addr (oSt s₀) + BitVec.ofNat 64 64)
    (ciphOf s.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) hcb
  exact ⟨co.env, hk₁.frame spf (k₁.mem ▸ co.frame) hA sp₂ rd₂ wr₂, by rw [co.out c0, Proof.Gcm.gctr_eq],
    co.frame⟩

end

theorem padded_eq (a c : List Byte) :
    (a ++ zeros (padLen a.length) ++ c) ++ zeros (padLen (a ++ zeros (padLen a.length) ++ c).length) = padded a c := by
  by_cases hc : c = []
  · subst hc
    have h0 : padLen (a ++ zeros (padLen a.length) ++ []).length = 0 := by
      apply Proof.Gcm.padLen_of_mod
      simp only [List.append_nil, List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
    rw [h0]; simp [padded, Proof.Gcm.ghashInput_nil, zeros]
  · simp only [padded, Proof.Gcm.ghashInput_of_ne hc]

/-- The regions `oneTag o` writes. -/
abbrev otFrame (st w sp : BitVec 32) (o : Nat) : List Region :=
  [⟨State.addr st, 48⟩, ⟨State.addr w + BitVec.ofNat 64 96, 16⟩, ⟨State.addr w + BitVec.ofNat 64 o, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, below sp]

theorem abs_otSub {st w sp : BitVec 32} {o : Nat} : ∀ r ∈ absFrame st w sp 16, ∃ r' ∈ otFrame st w sp o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem t_otSub {st w sp : BitVec 32} {o : Nat} : ∀ r ∈ tFrame st w sp 16, ∃ r' ∈ otFrame st w sp o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem tag_otSub {st w sp : BitVec 32} {o : Nat} : ∀ r ∈ tagFrame st w sp o, ∃ r' ∈ otFrame st w sp o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

section
variable {n : Nat}

/-- After `oneTag o`, from `m₀`, for the tag of `a` and the bytes at `data`. -/
structure OT (n : Nat) (s₀ : State) (o : Nat) (a : List Byte) (J : Block) (m₀ : Mem) (s : State) : Prop where
  env : ∃ k7, Env (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp k7 (s₀.gpr .r1) s
  args : ArgsKeep n s₀ s
  out : bytesAt s.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (ghash (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (blocks (padded a (bytesAt m₀ (State.addr (arg s₀ 2)) (arg s₀ 3).toNat))))
      [ofBytes (lensBlock a.length (bytesAt m₀ (State.addr (arg s₀ 2)) (arg s₀ 3).toNat).length)] ^^^
      ciphOf m₀ (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat J)
  frame : Frame (otFrame (oSt s₀) (arg s₀ 4) s₀.sp o) m₀ s.mem

theorem one_argsOt {s₀ : State} (h : onePre n s₀) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ otFrame (oSt s₀) (arg s₀ 4) s₀.sp o, (args s₀ n).Disjoint r := by
  have hst := oSt_addr h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [hst]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by omega))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

theorem oneTag_ok {s₀ s : State} (h : onePre n s₀) (hn : 5 ≤ n) {o : Nat} (ho : o = 0 ∨ o = 112) {k7 : BitVec 32}
    (he : Env (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp k7 (s₀.gpr .r1) s) (hk : ArgsKeep n s₀ s)
    (hH : blockAt s.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    {a : List Byte} (hl : (arg s₀ 1).toNat = a.length)
    (hab : Absorbed s.mem (State.addr (oSt s₀) + BitVec.ofNat 64 16) (State.addr (oSt s₀) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (a ++ zeros (padLen a.length))) :
    WP isa (oneTag o) s (OT n s₀ o a (blockAt s.mem (State.addr (oSt s₀))) s.mem) := by
  have L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ n ∈ s₀.rd := by rw [h.1]; simp
  have hA := one_argsOt h ho
  have dC : ∀ r ∈ otFrame (oSt s₀) (arg s₀ 4) s₀.sp o, (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Region.sub_prefix (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by omega))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.kc.symm
  have dJ : ∀ r ∈ absFrame (oSt s₀) (arg s₀ 4) s₀.sp 16 ++ tFrame (oSt s₀) (arg s₀ 4) s₀.sp 16,
      (⟨State.addr (oSt s₀), 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have e1 : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ 80 →
        (⟨State.addr (oSt s₀), 16⟩ : Region).Disjoint ⟨State.addr (oSt s₀) + BitVec.ofNat 64 d, k⟩ := fun h1 h2 => by
      have := Lay.st_st (st := oSt s₀) (a := 0) (n := 16) (.inl h1) (by decide) h2
      rwa [add_ofNat_zero] at this
    have e2 : ∀ {d k : Nat}, 96 ≤ d → d + k ≤ 2560 →
        (⟨State.addr (oSt s₀), 16⟩ : Region).Disjoint ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, k⟩ := fun h1 h2 => by
      have := L.st_w (a := 0) (n := 16) (by decide) (.inr ⟨h1, h2⟩)
      rwa [add_ofNat_zero] at this
    have e3 : (⟨State.addr (oSt s₀), 16⟩ : Region).Disjoint (below s₀.sp) := by
      have := (L.stk_st (a := 0) (n := 16) (by decide)).symm
      rwa [add_ofNat_zero] at this
    rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
    · exact e1 (by decide) (by decide)
    · exact e1 (by decide) (by decide)
    · exact e2 (by decide) (by decide)
    · exact e3
    · exact e1 (by decide) (by decide)
    · exact e2 (by decide) (by decide)
    · exact e2 (by decide) (by decide)
    · exact e3
  have hx : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  obtain ⟨s₁, run₁, h4, h5, h6, g₁, k₁⟩ := dataArgs_run hk spf hin hn
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have hk₁ := hk.of_eq k₁.mem k₁.sp k₁.rd k₁.wr
  have ai : AbsIn (s₀.gpr .r0) (oSt s₀) (arg s₀ 4) s₀.sp k7 (s₀.gpr .r1) 16 (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (a ++ zeros (padLen a.length)) (arg s₀ 2) (arg s₀ 3).toNat s₁ :=
    ⟨he₁, h4, by rw [h5]; simp, by rw [h6, hx], one_dataOk h hk₁, by rw [k₁.mem]; exact hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) ai)) fun s₂ hh => ?_)
  obtain ⟨ab, rd₂, wr₂, sp₂⟩ := hh
  rw [k₁.mem] at ab
  have hk₂ := hk₁.frame spf (k₁.mem ▸ ab.frame) (disj_sub hA abs_otSub) sp₂ rd₂ wr₂
  obtain ⟨b3, w3⟩ := hk₂.at spf hin 3 (by omega) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₃, run₃, h6₃, g₃, k₃⟩ : ∃ s₃, runBlock isa [.ldrSp .r6 12, .dp .and .r6 .r6 (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 3).toNat % 16) ∧ (∀ r, r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    refine ⟨_, by arun [b3, w3], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, w3, and15]
    · intro r x; simp [gpr_setReg, x]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := ab.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) k₃.sp k₃.rd k₃.wr
  have hk₃ := hk₂.of_eq k₃.mem k₃.sp k₃.rd k₃.wr
  have hH₂ : blockAt s₂.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl))]; exact hH
  let ct := bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat
  have hlx : ((a ++ zeros (padLen a.length)) ++ ct).length % 16 = (arg s₀ 3).toNat % 16 := by
    simp only [List.length_append, Proof.Gcm.length_zeros, ct, length_bytesAt] at hx ⊢; omega
  refine WP.seq (WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl)
    (x := (a ++ zeros (padLen a.length)) ++ ct) (H := ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    ⟨he₃, by rw [k₃.mem]; exact hH₂⟩ (by rw [h6₃, hlx]))) fun s₄ hh => ?_)
  obtain ⟨fl, rd₄, wr₄, sp₄⟩ := hh
  rw [k₃.mem] at fl
  have hk₄ := hk₂.frame spf fl.frame (disj_sub hA t_otSub) (sp₄.trans k₃.sp) (rd₄.trans k₃.rd) (wr₄.trans k₃.wr)
  obtain ⟨c1, x1⟩ := hk₄.at spf hin 1 (by omega) (show 4 * 1 = 4 from rfl)
  obtain ⟨c3, x3⟩ := hk₄.at spf hin 3 (by omega) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₅, run₅, h4₅, h5₅, h6₅, h7₅, g₅, k₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r4 4, .mov .r5 (imm 0), .ldrSp .r6 12,
      .mov .r7 (imm 0)] s₄ = some s₅ ∧ s₅.gpr .r4 = arg s₀ 1 ∧ s₅.gpr .r5 = 0 ∧ s₅.gpr .r6 = arg s₀ 3 ∧
      s₅.gpr .r7 = 0 ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [c1, x1, c3, x3], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, x1]
    · simp [gpr_setReg]
    · simp [gpr_setReg, x3]
    · simp [gpr_setReg]
    · intro r x y z q; simp [gpr_setReg, x, y, z, q]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := fl.env.set7 h7₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide) (by decide) (by decide))
    k₅.sp k₅.rd k₅.wr
  have hk₅ := hk₄.of_eq k₅.mem k₅.sp k₅.rd k₅.wr
  refine WP.mono (WP.with_rdwr (tag_ok L ho he₅ (show s₀.gpr .r1 = BitVec.ofNat 32 (s₀.gpr .r1).toNat by simp) hR
    (H := ctxH s₀.mem (State.addr (s₀.gpr .r0))) (by rw [k₅.mem]; exact fl.hH) rfl)) fun s₆ hh => ?_
  obtain ⟨tg, rd₆, wr₆, sp₆⟩ := hh
  rw [h4₅, h5₅, h6₅, h7₅, k₅.mem] at tg
  have f₄ : Frame (absFrame (oSt s₀) (arg s₀ 4) s₀.sp 16 ++ tFrame (oSt s₀) (arg s₀ 4) s₀.sp 16) s.mem s₄.mem :=
    (ab.frame.mono (fun r hr => List.mem_append_left _ hr)).trans
      ((k₃.mem ▸ fl.frame : Frame _ s₂.mem s₄.mem).mono (fun r hr => List.mem_append_right _ hr))
  refine ⟨⟨_, tg.env⟩, hk₄.frame spf tg.frame (disj_sub hA tag_otSub) (sp₆.trans k₅.sp) (rd₆.trans k₅.rd)
    (wr₆.trans k₅.wr), ?_, ?_⟩
  · rw [tg.out]
    have hw := (fl.abs (ab.abs hab)).whole_eq (by
      simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
    rw [padded_eq] at hw
    rw [hw, ciph_frame f₄ (disj_sub dC (fun r hr => by
        simp only [List.mem_append] at hr
        rcases hr with hr | hr
        · exact abs_otSub r hr
        · exact t_otSub r hr)) hR,
      blockAt_frame f₄ dJ]
    have z0 : (0 : BitVec 32).toNat = 0 := rfl
    have l1 : ((0 : BitVec 32) ++ arg s₀ 1).toNat = a.length := by
      rw [Proof.Gcm.toNat_append, ← hl, z0, Nat.zero_mul, Nat.zero_add]
    have l3 : ((0 : BitVec 32) ++ arg s₀ 3).toNat = ct.length := by
      rw [Proof.Gcm.toNat_append, length_bytesAt, z0, Nat.zero_mul, Nat.zero_add]
    rw [l1, l3]
  · refine (f₄.sub fun r hr => ?_).trans (tg.frame.sub tag_otSub)
    simp only [List.mem_append] at hr
    rcases hr with hr | hr
    · exact abs_otSub r hr
    · exact t_otSub r hr

end

end VG.Proof.AesGcm.Arm
