import VerifiedGarbage.Proof.AesGcm.Arm.FinTag
import VerifiedGarbage.Proof.AesGcm.Arm.StreamCrypt

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_finish`

Untrusted: everything here is checked by Lean. `stream_finish` saves our
caller's registers in `work` (`W`) and writes the tag to its first 16 bytes
with `finTag` (`streamFinish_wp`). The entry is shared with `stream_verify`
(`fin1_wp`, for `n` words of stack arguments).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput fullTag)
open VG.Proof.Gcm (Absorbed lensBlock)

theorem lensBlock_mod (L c : Nat) : lensBlock (L % 2 ^ 64) c = lensBlock L c := by
  simp only [lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (L % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * L)]
  congr 2; omega

theorem toNat_of_eq {x : BitVec 64} {L : Nat} (h : x = BitVec.ofNat 64 L) : x.toNat = L % 2 ^ 64 := by
  rw [h, BitVec.toNat_ofNat]

section
variable {n : Nat}

theorem finLay {s₀ : State} (h : finPre n s₀) : Lay (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 4) s₀.sp := by
  obtain ⟨-, -, dcs, dcW, dsW, -, -, bc, bs, bW, fc, fs, fW, sp8, -, -⟩ := h
  exact Lay.of fc fs fW sp8 dcs dcW dsW bc bs bW

/-- After the entry, from `s₀`. -/
structure SF1 (n : Nat) (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 4) s₀.sp (s₀.gpr .r7) (s₀.gpr .r1) s₁
  args : ArgsKeep n s₀ s₁
  saved : SavedAt s₁.mem (arg s₀ 4) s₀
  frame : Frame [savedR (arg s₀ 4)] s₀.mem s₁.mem

theorem fin1_wp {s₀ : State} (h : finPre n s₀) (hn : 5 ≤ n) {Q : State → Prop} (k : ∀ s₁, SF1 n s₀ s₁ → Q s₁) :
    WP isa (.block finEntry) s₀ Q := by
  obtain ⟨hrd, hwr, -, -, -, -, dWA, -, -, -, -, -, fW, -, spf, -⟩ := h
  have hA : ∀ r ∈ [savedR (arg s₀ 4)], (args s₀ n).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) := by
    rw [hrd]; exact covers_of_mem (by simp)
  have hS : Covers [⟨State.addr (s₀.gpr .r2), 80⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hW : Covers [⟨State.addr (arg s₀ 4), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have ha : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * 4))) 4 :=
    arg_in (n := n) (by omega) spf (by rw [hrd]; simp)
  refine entry_ok (off := 16) (by decide) ha fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  have hk : ArgsKeep n s₀ s₁ := (ArgsKeep.refl n s₀).frame spf fr hA sp rd wr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact hk.of_eq rfl rfl rfl rfl

theorem fin_argsTag {s₀ : State} (h : finPre n s₀) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ tagFrame (s₀.gpr .r2) (arg s₀ 4) s₀.sp o, (args s₀ n).Disjoint r := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, dsA, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (dsA.sub_left (Region.sub_prefix (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by omega))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

/-- The tag, from the entry. -/
theorem fin_tag {s₀ s₁ : State} (h : finPre n s₀) (hn : 5 ≤ n) (h1 : SF1 n s₀ s₁) {o : Nat} (ho : o = 0 ∨ o = 112)
    {a ct : List Byte} (ha : a.length % 16 = (arg s₀ 0).toNat % 16) (hP : (arg s₀ 3 ++ arg s₀ 2).toNat = ct.length) :
    WP isa (finTag o) s₁ (FinOut (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 4) s₀.sp (s₀.gpr .r1) n s₀ o (s₀.gpr .r1).toNat
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) a ct s₁.mem) := by
  have L := finLay h
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact finTag_ok L (by omega) ho h1.env h1.args spf (by rw [h.1]; simp) (fin_argsTag h ho) (by simp) hR
    (ctxH_keep h1.frame (ctx_saved L)) ha hP

/-- The tag, for a state that represents `a` and `ct`. -/
theorem fin_out {s₀ s₁ s : State} (h : finPre n s₀) (h1 : SF1 n s₀ s₁) {o : Nat} {iv a ct : List Byte}
    (hf : FinOut (s₀.gpr .r0) (s₀.gpr .r2) (arg s₀ 4) s₀.sp (s₀.gpr .r1) n s₀ o (s₀.gpr .r1).toNat
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) a ct s₁.mem s)
    (hs : StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct) (hl : arg64 s₀ 0 = BitVec.ofNat 64 a.length) :
    bytesAt s.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 o) 16 =
      fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
        iv a ct := by
  have L := finLay h
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, -⟩ := hs
  simp only [ofNat_lit] at hab hj
  have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
  rw [hf.out (hab.congr (blockAt_frame h1.frame (stp_saved L (by decide)))
      (bytesAt_frame h1.frame (stp_saved L (by omega)) (by omega))),
    ciph_keep h1.frame (ctx_saved L) hR,
    blockAt_frame h1.frame (by simpa using stp_saved L (d := 0) (k := 16) (by decide)), hj,
    toNat_of_eq hl, lensBlock_mod, Proof.Gcm.fullTag_eq]

end

theorem streamFinish_wp {s₀ : State} (h : streamFinishArm.pre s₀) :
    WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ streamFinishArm.post s₀ s' := by
  have h' : finPre 5 s₀ := h
  have L := finLay h'
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.1
  have run : ∀ {a ct : List Byte}, a.length % 16 = (arg s₀ 0).toNat % 16 → (arg s₀ 3 ++ arg s₀ 2).toNat = ct.length →
      WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ ∀ iv,
        StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
          (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct → arg64 s₀ 0 = BitVec.ofNat 64 a.length →
        bytesAt s'.mem (State.addr (arg s₀ 4)) 16 =
          fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
            (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct := fun ha hP =>
    WP.seq (fin1_wp h' (by decide) fun s₁ h1 => WP.seq (WP.mono (fin_tag h' (by decide) h1 (.inl rfl) ha hP)
      fun s₂ hf => by
        obtain ⟨k7, he⟩ := hf.env
        exact WP.mono (restore_ok he.r11 fW (covers_left he.perm.w)
          (h1.saved.frame hf.frame (saved_tagFrame L (.inl rfl))) he.sp) fun s' hh => ⟨hh.1, fun iv hs hl => by
            have := fin_out h' h1 hf hs hl
            rwa [add_ofNat_zero, ← hh.2.1] at this⟩))
  have h₀ := run (a := List.replicate ((arg s₀ 0).toNat % 16) 0)
    (ct := List.replicate (arg s₀ 3 ++ arg s₀ 2).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
          (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1 i.2.1 i.2.2 ∧
        arg64 s₀ 0 = BitVec.ofNat 64 i.2.1.length ∧ (arg64 s₀ 2).toNat = i.2.2.length)
    fun i hi => WP.mono (run (a := i.2.1) (ct := i.2.2) (low_mod16 hi.2.1).symm hi.2.2)
      fun s' hh => hh.2 i.1 hi.1 hi.2.1)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩⟩

end VG.Proof.AesGcm.Arm
