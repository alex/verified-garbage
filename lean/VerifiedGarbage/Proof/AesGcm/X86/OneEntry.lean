import VerifiedGarbage.Proof.AesGcm.X86.Top

/-!
# AES-GCM on x86: the entry of `seal` and `open`

Untrusted: everything here is checked by Lean. The precondition of `seal`
and `open` (`OP`), the layout it gives in terms of the public data (`OL`),
what holds of the working space from the entry to the exit (`OEnv`, which
the pieces keep as they write only within `D :: oF p`), and the entry
(`oneEntry_pc`). The state is at `W + 16`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph)

/-- The state of `seal` and `open`, at `W + 16`. -/
abbrev stOf (W : BitVec 32) : BitVec 32 := W + BitVec.ofNat 32 16

/-- What the precondition of `seal` and `open` (with `nA` arguments) gives. -/
structure OP (nA : Nat) (s : State) : Prop where
  rd : s.rd = [⟨w64 (arg s 0), 256⟩, ⟨w64 (arg s 2), (arg s 3).toNat⟩, ⟨w64 (arg s 4), (arg s 5).toNat⟩]
  wr : s.wr = [⟨w64 (arg s 6), (arg s 7).toNat⟩, ⟨w64 (arg s 8), 2560⟩, ⟨argAddr s 0, 4 * nA⟩]
  c_d : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s 6), (arg s 7).toNat⟩
  c_w : (⟨w64 (arg s 0), 256⟩ : Region).Disjoint ⟨w64 (arg s 8), 2560⟩
  n_d : (⟨w64 (arg s 2), (arg s 3).toNat⟩ : Region).Disjoint ⟨w64 (arg s 6), (arg s 7).toNat⟩
  n_w : (⟨w64 (arg s 2), (arg s 3).toNat⟩ : Region).Disjoint ⟨w64 (arg s 8), 2560⟩
  a_d : (⟨w64 (arg s 4), (arg s 5).toNat⟩ : Region).Disjoint ⟨w64 (arg s 6), (arg s 7).toNat⟩
  a_w : (⟨w64 (arg s 4), (arg s 5).toNat⟩ : Region).Disjoint ⟨w64 (arg s 8), 2560⟩
  d_w : (⟨w64 (arg s 6), (arg s 7).toNat⟩ : Region).Disjoint ⟨w64 (arg s 8), 2560⟩
  d_a : (⟨w64 (arg s 6), (arg s 7).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 4 * nA⟩
  w_a : (⟨w64 (arg s 8), 2560⟩ : Region).Disjoint ⟨argAddr s 0, 4 * nA⟩
  r_d : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 6), (arg s 7).toNat⟩
  r_w : (⟨w64 (s.gpr .esp), 4⟩ : Region).Disjoint ⟨w64 (arg s 8), 2560⟩
  k_c : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 0), 256⟩
  k_n : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 2), (arg s 3).toNat⟩
  k_a : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 4), (arg s 5).toNat⟩
  k_d : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 6), (arg s 7).toNat⟩
  k_w : (below (s.gpr .esp) 28).Disjoint ⟨w64 (arg s 8), 2560⟩
  fc : (arg s 0).toNat + 256 ≤ 2 ^ 32
  fn : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  fa : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  fd : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  fw : (arg s 8).toNat + 2560 ≤ 2 ^ 32
  sp : 28 ≤ (s.gpr .esp).toNat
  fg : (s.gpr .esp).toNat + 4 + 4 * nA ≤ 2 ^ 32
  rounds : roundsOk s 1

theorem op_of {nA : Nat} {s : State} (h : onePre nA s) : OP nA s := by
  simp only [onePre] at h
  obtain ⟨hrd, hwr, c_d, c_w, -, n_d, n_w, -, a_d, a_w, -, d_w, d_a, w_a, -, -, -, r_d, r_w, -, k_c, k_n, k_a, k_d,
    k_w, -, fc, fn, fa, fd, fw, sp, fg, hR⟩ := h
  rw [ofNat_lit, below_eq sp] at k_c k_n k_a k_d k_w
  exact ⟨hrd, hwr, c_d, c_w, n_d, n_w, a_d, a_w, d_w, d_a, w_a, r_d, r_w, k_c, k_n, k_a, k_d, k_w, fc, fn, fa, fd,
    fw, sp, fg, hR⟩

theorem stOf_w64 {W : BitVec 32} (hw : W.toNat + 2560 ≤ 2 ^ 32) : w64 (stOf W) = w64 W + BitVec.ofNat 64 16 :=
  w64_add (by omega)

/-- The layout of `seal` and `open`, for the public data `p`. -/
structure OL (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  L : Lay (p.2 0) (stOf (p.2 8)) (p.2 8) p.1 28
  c_d : (⟨w64 (p.2 0), 256⟩ : Region).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  n_d : (⟨w64 (p.2 2), (p.2 3).toNat⟩ : Region).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  n_w : (⟨w64 (p.2 2), (p.2 3).toNat⟩ : Region).Disjoint ⟨w64 (p.2 8), 2560⟩
  a_d : (⟨w64 (p.2 4), (p.2 5).toNat⟩ : Region).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  a_w : (⟨w64 (p.2 4), (p.2 5).toNat⟩ : Region).Disjoint ⟨w64 (p.2 8), 2560⟩
  d_w : (⟨w64 (p.2 6), (p.2 7).toNat⟩ : Region).Disjoint ⟨w64 (p.2 8), 2560⟩
  r_d : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 8), 2560⟩
  k_n : (below p.1 28).Disjoint ⟨w64 (p.2 2), (p.2 3).toNat⟩
  k_a : (below p.1 28).Disjoint ⟨w64 (p.2 4), (p.2 5).toNat⟩
  k_d : (below p.1 28).Disjoint ⟨w64 (p.2 6), (p.2 7).toNat⟩
  fn : (p.2 2).toNat + (p.2 3).toNat ≤ 2 ^ 32
  fa : (p.2 4).toNat + (p.2 5).toNat ≤ 2 ^ 32
  fd : (p.2 6).toNat + (p.2 7).toNat ≤ 2 ^ 32
  rounds : (p.2 1).toNat = 10 ∨ (p.2 1).toNat = 12 ∨ (p.2 1).toNat = 14

theorem OP.ol {nA : Nat} (hnA : 9 ≤ nA) {s : State} (h : OP nA s) {p : BitVec 32 × (Nat → BitVec 32)}
    (hp : pubOf nA s = p) : OL p := by
  have a : ∀ i, i < nA → arg s i = p.2 i := fun i hi => pubOf_arg hp hi
  have esp : s.gpr .esp = p.1 := pubOf_esp hp
  obtain ⟨-, -, c_d, c_w, n_d, n_w, a_d, a_w, d_w, -, -, r_d, r_w, k_c, k_n, k_a, k_d, k_w, fc, fn, fa, fd, fw, sp,
    -, hR⟩ := h
  have e := fun i hi => a i hi
  simp only [e 0 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
    e 6 (by omega), e 7 (by omega), e 8 (by omega), esp] at c_d c_w n_d n_w a_d a_w d_w r_d r_w k_c k_n
  simp only [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
    e 6 (by omega), e 7 (by omega), e 8 (by omega), esp, roundsOk] at k_a k_d k_w fc fn fa fd fw sp hR
  have hs := stOf_w64 fw
  have sw : (⟨w64 (stOf (p.2 8)), 80⟩ : Region).Sub ⟨w64 (p.2 8), 2560⟩ := by
    rw [hs]; exact Lay.wSub (by decide)
  refine ⟨⟨fc, by rw [toNat_add32 (by omega)]; omega, fw, by decide, by decide, sp,
    c_w.sub_right sw, c_w, ?_, ?_, k_c, k_w.sub_right sw, k_w⟩, c_d, n_d, n_w, a_d, a_w, d_w,
    r_d, r_w, k_n, k_a, k_d, fn, fa, fd, hR⟩
  · rw [hs]
    have := Lay.w_w (W := p.2 8) (a := 16) (n := 80) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  · rw [hs]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)

/-- The regions of `W` and the stack the pieces write (but the tag at `W`). -/
abbrev oF (p : BitVec 32 × (Nat → BitVec 32)) : List Region :=
  [⟨w64 (p.2 8) + BitVec.ofNat 64 16, 112⟩, ⟨w64 (p.2 8) + BitVec.ofNat 64 auxO, 4⟩, ⟨w64 (p.2 8) + BitVec.ofNat 64 rO, 16⟩, wsR (p.2 8),
    below p.1 28]

/-- Those, the data and the first block of `W`: what `OEnv` survives. -/
abbrev oFF (p : BitVec 32 × (Nat → BitVec 32)) : List Region :=
  ⟨w64 (p.2 8), 16⟩ :: ⟨w64 (p.2 6), (p.2 7).toNat⟩ :: oF p

/-- What holds from the entry of `seal` or `open` to the exit. -/
structure OEnv (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  env : Env (p.2 0) (stOf (p.2 8)) (p.2 8) p.1 s
  rounds : RoundsAt s.mem (p.2 8) (p.2 1).toNat
  aadO : slotv s.mem (p.2 8) aadO = p.2 4
  alO : slotv s.mem (p.2 8) alO = p.2 5
  dataO : slotv s.mem (p.2 8) dataO = p.2 6
  lenO : slotv s.mem (p.2 8) lenO = p.2 7
  zO : slotv s.mem (p.2 8) zO = 0
  nlO : slotv s.mem (p.2 8) nlO = p.2 3
  saved : SavedAt s.mem (p.2 8) s₀
  ret : s.mem.readW (w64 p.1) 32 = s₀.mem.readW (w64 p.1) 32
  ciph : ciphOf s.mem (p.2 0) (p.2 1).toNat = ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat
  hk : Hk s.mem (p.2 0) = ctxH s₀.mem (w64 (p.2 0))
  aad : bytesAt s.mem (w64 (p.2 4)) (p.2 5).toNat = bytesAt s₀.mem (w64 (p.2 4)) (p.2 5).toNat
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  nIn : Covers [⟨w64 (p.2 2), (p.2 3).toNat⟩] (s.rd ++ s.wr)
  aIn : Covers [⟨w64 (p.2 4), (p.2 5).toNat⟩] (s.rd ++ s.wr)
  dIn : Covers [⟨w64 (p.2 6), (p.2 7).toNat⟩] s.wr

section
variable {p : BitVec 32 × (Nat → BitVec 32)} (G : OL p)
include G

/-- A part of the kept values, outside what the pieces write. -/
theorem slot_oF {o n : Nat} (h₁ : 128 ≤ o) (h₂ : o + n ≤ auxO ∨ (auxO + 4 ≤ o ∧ o + n ≤ rO)) :
    ∀ r ∈ oFF p, (⟨w64 (p.2 8) + BitVec.ofNat 64 o, n⟩ : Region).Disjoint r := by
  simp only [auxO, rO] at h₂
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have := Lay.w_w (W := p.2 8) (a := o) (n := n) (d := 0) (k := 16) (.inr (by omega)) (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  · exact (G.d_w.sub_right (Lay.wSub (by omega))).symm
  · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (by simp only [auxO]; omega) (by omega) (by decide)
  · exact Lay.w_w (.inl (by simp only [rO]; omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (G.L.stk_w (by omega)).symm

/-- The context, outside what the pieces write. -/
theorem ctx_oF : ∀ r ∈ oFF p, (⟨w64 (p.2 0), 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact G.L.cw.sub_right (Region.sub_prefix (by decide))
  · exact G.c_d
  · exact G.L.cw.sub_right (Lay.wSub (by decide))
  · exact G.L.cw.sub_right (Lay.wSub (by decide))
  · exact G.L.cw.sub_right (Lay.wSub (by decide))
  · exact G.L.cw.sub_right (Lay.wSub (by decide))
  · exact G.L.kc.symm

/-- The additional data, outside what the pieces write. -/
theorem aad_oF : ∀ r ∈ oFF p, (⟨w64 (p.2 4), (p.2 5).toNat⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact G.a_w.sub_right (Region.sub_prefix (by decide))
  · exact G.a_d
  · exact G.a_w.sub_right (Lay.wSub (by decide))
  · exact G.a_w.sub_right (Lay.wSub (by decide))
  · exact G.a_w.sub_right (Lay.wSub (by decide))
  · exact G.a_w.sub_right (Lay.wSub (by decide))
  · exact G.k_a.symm

/-- The return address, outside what the pieces write. -/
theorem ret_oF : ∀ r ∈ oFF p, (⟨w64 p.1, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact G.r_w.sub_right (Region.sub_prefix (by decide))
  · exact G.r_d
  · exact G.r_w.sub_right (Lay.wSub (by decide))
  · exact G.r_w.sub_right (Lay.wSub (by decide))
  · exact G.r_w.sub_right (Lay.wSub (by decide))
  · exact G.r_w.sub_right (Lay.wSub (by decide))
  · exact ret_below G.L.sp

/-- `OEnv` after code that writes within `oFF p` and keeps the registers. -/
theorem OEnv.frame {s₀ s s' : State} (h : OEnv p s₀ s)
    (hf : Frame (oFF p) s.mem s'.mem)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : OEnv p s₀ s' := by
  have sl : ∀ o, 128 ≤ o → (o + 4 ≤ auxO ∨ (auxO + 4 ≤ o ∧ o + 4 ≤ rO)) →
      slotv s'.mem (p.2 8) o = slotv s.mem (p.2 8) o := fun o h₁ h₂ => by
    rw [slotv_eq, slotv_eq]; exact slot_frame hf (slot_oF G h₁ h₂)
  have hR := G.rounds
  refine ⟨h.env.keep hbp hsi hsp hrd hwr ?_, ⟨by rw [sl _ (by decide) (by decide)]; exact h.rounds.1, h.rounds.2⟩,
    by rw [sl _ (by decide) (by decide)]; exact h.aadO, by rw [sl _ (by decide) (by decide)]; exact h.alO,
    by rw [sl _ (by decide) (by decide)]; exact h.dataO, by rw [sl _ (by decide) (by decide)]; exact h.lenO,
    by rw [sl _ (by decide) (by decide)]; exact h.zO, by rw [sl _ (by decide) (by decide)]; exact h.nlO,
    h.saved.frame hf fun r hr => ?_, by rw [ret_kept hf (ret_oF G)]; exact h.ret,
    by rw [ciph_frame hf (ctx_oF G) hR]; exact h.ciph,
    by rw [show Hk s'.mem (p.2 0) = Hk s.mem (p.2 0) from blockAt_frame hf fun r hr =>
      (ctx_oF G r hr).sub_left (Lay.ctxSub (by decide))]; exact h.hk,
    by rw [bytesAt_frame hf (aad_oF G) (by omega)]; exact h.aad, by rw [hrd]; exact h.rd, by rw [hwr]; exact h.wr,
    by rw [hrd, hwr]; exact h.nIn, by rw [hrd, hwr]; exact h.aIn, by rw [hwr]; exact h.dIn⟩
  · have := sl ctxO (by decide) (by decide); rwa [slotv_eq, slotv_eq] at this
  · exact slot_oF G (o := 128) (n := 16) (by decide) (by decide) r hr

theorem OEnv.frameE {s₀ s s' : State} (h : OEnv p s₀ s)
    (hf : Frame (oFF p) s.mem s'.mem)
    (he : Env (p.2 0) (stOf (p.2 8)) (p.2 8) p.1 s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : OEnv p s₀ s' :=
  h.frame G hf (by rw [he.ebp, h.env.ebp]) (by rw [he.esi, h.env.esi]) (by rw [he.esp, h.env.esp]) hrd hwr

/-- A part of the state, in `W`. -/
theorem st_eq {d : Nat} : w64 (stOf (p.2 8)) + BitVec.ofNat 64 d = w64 (p.2 8) + BitVec.ofNat 64 (16 + d) := by
  rw [stOf_w64 G.L.fw, Offset.add_add]

omit G in
/-- A part of `W` the pieces write. -/
theorem w_sub_oF {d k : Nat} (h₁ : 16 ≤ d) (h₂ : d + k ≤ 128) :
    ∃ r' ∈ oF p, Region.Sub ⟨w64 (p.2 8) + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨⟨w64 (p.2 8) + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ h₁ (by omega)⟩

theorem st_sub_oF {d k : Nat} (h : d + k ≤ 80) :
    ∃ r' ∈ oF p, Region.Sub ⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 d, k⟩ r' := by
  rw [st_eq G]; exact w_sub_oF (by omega) (by omega)

theorem st0_sub_oF {k : Nat} (h : k ≤ 80) : ∃ r' ∈ oF p, Region.Sub ⟨w64 (stOf (p.2 8)), k⟩ r' := by
  rw [stOf_w64 G.L.fw]; exact w_sub_oF (by omega) (by omega)

omit G in
theorem ws_sub_oF : ∃ r' ∈ oF p, Region.Sub (wsR (p.2 8)) r' :=
  ⟨_, by simp, fun _ h => h⟩

omit G in
theorem stk_sub_oF : ∃ r' ∈ oF p, Region.Sub (below p.1 28) r' :=
  ⟨_, by simp, fun _ h => h⟩

omit G in
theorem pslot_sub_oF : ∃ r' ∈ oF p, Region.Sub (pslotR (p.2 8)) r' :=
  ⟨_, by simp, pslot_ws _⟩

omit G in
theorem Frame.oD {m m' : Mem} (h : Frame (oF p) m m') : Frame (oFF p) m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)

omit G in
theorem Frame.oDD {m m' : Mem} (h : Frame (⟨w64 (p.2 6), (p.2 7).toNat⟩ :: oF p) m m') : Frame (oFF p) m m' :=
  h.mono fun _ hr => List.mem_cons_of_mem _ hr

omit G in
theorem d_sub_oF :
    ∃ r' ∈ ⟨w64 (p.2 6), (p.2 7).toNat⟩ :: oF p, Region.Sub ⟨w64 (p.2 6), (p.2 7).toNat⟩ r' :=
  ⟨_, by simp, fun _ h => h⟩

end

/-! ## The entry -/

abbrev oKeeps : List (Nat × Nat) :=
  [(0, ctxO), (1, roundsO), (2, dO), (3, nO), (3, nlO), (4, aadO), (5, alO), (6, dataO), (7, lenO)]

abbrev oPre : List Instr := [.mov .esi (.reg .ebp), .alu .add .esi (imm stO)]

theorem oneEntry_eq (rest : List Instr) : oneEntry rest = entry 8 (oPre ++
    (oKeeps.flatMap (fun (p : Nat × Nat) => keep p.1 p.2) ++ (([.mov .eax (imm 0), .store (at_ .ebp zO) .eax] : List Instr) ++ rest))) :=
  rfl

/-- The end of the entry: `zO` zeroed, and `tag_len` kept for `open`. -/
theorem oTail_ok {W SP : BitVec 32} {s : State} (rest : List Instr) (hrest : rest = [] ∨ rest = keep 9 tglO)
    (hbp : s.gpr .ebp = W) (hsp : s.gpr .esp = SP) (hw : Covers [⟨w64 W, 2560⟩] s.wr) (fw : W.toNat + 2560 ≤ 2 ^ 32)
    (hA : rest ≠ [] → InRegions (s.rd ++ s.wr) (argA SP 9) 4)
    (hd : rest ≠ [] → (⟨argA SP 9, 4⟩ : Region).Disjoint ⟨w64 W, 2560⟩) :
    ∃ s', runBlock isa (([.mov .eax (imm 0), .store (at_ .ebp zO) .eax] : List Instr) ++ rest) s = some s' ∧
      Frame [⟨w64 W + BitVec.ofNat 64 zO, 4⟩, ⟨w64 W + BitVec.ofNat 64 tglO, 4⟩] s.mem s'.mem ∧
      slotv s'.mem W zO = 0 ∧ (rest ≠ [] → slotv s'.mem W tglO = s.mem.readW (argA SP 9) 32) ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => w64_add (by omega)
  have wIn : ∀ {o}, o + 4 ≤ 2560 → InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 := fun ho => in_off hw ho (by decide)
  have f₁ : Frame [⟨w64 W + BitVec.ofNat 64 zO, 4⟩, ⟨w64 W + BitVec.ofNat 64 tglO, 4⟩] s.mem
      (s.mem.writeW (w64 W + BitVec.ofNat 64 zO) (BitVec.ofNat 32 0)) :=
    (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Region.contains_self _ _)
  rcases hrest with rfl | rfl
  · refine ⟨_, by xrun [hbp, aW, wIn], by mems []; exact f₁, by mems [slotv_eq]; rfl, fun h => absurd rfl h,
      by regs [], by regs [], by regs [], by mems [], by mems []⟩
  · have hi := hA (by simp [keep])
    have f₂ := f₁.writeW (r := ⟨w64 W + BitVec.ofNat 64 tglO, 4⟩) (by simp) (w := 32)
      ((s.mem.writeW (w64 W + BitVec.ofNat 64 zO) (BitVec.ofNat 32 0)).readW (argA SP 9) 32)
      (Region.contains_self _ _)
    have hr : (s.mem.writeW (w64 W + BitVec.ofNat 64 zO) (BitVec.ofNat 32 0)).readW (argA SP 9) 32 =
        s.mem.readW (argA SP 9) 32 := by
      have f : Frame [⟨w64 W + BitVec.ofNat 64 zO, 4⟩] s.mem
          (s.mem.writeW (w64 W + BitVec.ofNat 64 zO) (BitVec.ofNat 32 0)) :=
        (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Region.contains_self _ _)
      exact f.readW (r := ⟨argA SP 9, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hd (by simp [keep])).sub_right (Lay.wSub (by decide))) (by decide)
    refine ⟨_, by xrun [keep, hbp, hsp, aW, wIn, hi], by mems []; exact f₂, ?_, fun _ => ?_,
      by regs [], by regs [], by regs [], by mems [], by mems []⟩
    · mems [slotv_eq]; rfl
    · mems [slotv_eq]; exact hr

/-- After the entry of `seal` or `open`: the nonce ready for `j0`, and the
inputs as they were. -/
structure OEnt (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  o : OEnv p s₀ s
  dO : slotv s.mem (p.2 8) dO = p.2 2
  nO : slotv s.mem (p.2 8) nO = p.2 3
  iv : bytesAt s.mem (w64 (p.2 2)) (p.2 3).toNat = bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat
  data : bytesAt s.mem (w64 (p.2 6)) (p.2 7).toNat = bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat
  w0 : bytesAt s.mem (w64 (p.2 8)) 16 = bytesAt s₀.mem (w64 (p.2 8)) 16

theorem oneEntry_pc (nA : Nat) (hnA : nA = 9 ∨ nA = 10) (rest : List Instr) (hrest : rest = [] ∨ rest = keep 9 tglO)
    (hr10 : rest ≠ [] → nA = 10) (Pre : State → Prop) (hPre : ∀ s, Pre s → OP nA s)
    (p : BitVec 32 × (Nat → BitVec 32)) (G : OL p) {hh : Taint.Hint VG.X86.taint.T}
    (ht : (VG.X86.taint.check (τr [.eax, .esp]) (.block (saveAt ++ (oPre ++
      (oKeeps.flatMap (fun p => keep p.1 p.2) ++ (([.mov .eax (imm 0), .store (at_ .ebp zO) .eax] : List Instr) ++ rest)))))
      hh).isSome = true) :
    Pc (fun (s₀ : State) s => Pre s₀ ∧ pubOf nA s₀ = p ∧ s = s₀) (oneEntry rest)
      (fun s₀ s => OEnt p s₀ s ∧ (rest ≠ [] → slotv s.mem (p.2 8) tglO = p.2 9) ∧ pubOf nA s₀ = p ∧ Pre s₀) := by
  rw [oneEntry_eq]
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have h := hPre _ hpre
    have a : ∀ i, i < nA → arg s₀ i = p.2 i := fun i hi => pubOf_arg hpub hi
    have esp := pubOf_esp hpub
    have fw := h.fw
    rw [a 8 (by omega)] at fw
    have wW : Covers [⟨w64 (p.2 8), 2560⟩] s₀.wr := by
      rw [h.wr, a 8 (by omega)]; exact covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) nA] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, h.rd, h.wr]; exact covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) nA).Disjoint ⟨w64 (p.2 8), 2560⟩ := by
      rw [argsR_eq, ← a 8 (by omega)]; exact h.w_a.symm
    have hps : ∀ q ∈ oKeeps, q.1 < nA ∧ 144 ≤ q.2 ∧ q.2 + 4 ≤ 2560 ∧ q.2 % 4 = 0 := fun q hq => by
      have := (show ∀ q ∈ oKeeps, q.1 < 9 ∧ 144 ≤ q.2 ∧ q.2 + 4 ≤ 2560 ∧ q.2 % 4 = 0 by decide) q hq
      exact ⟨by omega, this.2⟩
    refine entry_gen (St := stOf (p.2 8)) _ oKeeps _ (by omega) hps (by decide) (a 8 (by omega)) wW rA aw h.fg fw
      (fun s₁ bp sp rd wr _ => ⟨_, by xrun [bp], by regs [bp], fun r hr => by
        simp only [gpr_arithFlags, gpr_setReg_of_ne _ _ hr], by mems [], by mems [], by mems []⟩) fun s₂ e => ?_
    obtain ⟨s₃, run, f₃, z₃, t₃, bp₃, si₃, sp₃, rd₃, wr₃⟩ := oTail_ok (W := p.2 8) (SP := s₀.gpr .esp) rest hrest
      e.ebp e.esp (by rw [e.wr]; exact wW) fw
      (fun hn => by rw [e.rd, e.wr]; exact argIn_of rA h.fg (by have := hr10 hn; omega))
      (fun hn => aw.sub_left (argA_sub (by have := hr10 hn; omega) h.fg))
    refine ⟨s₃, run, ?_, fun hn => by rw [t₃ hn, e.args 9 (by have := hr10 hn; omega), a 9 (by have := hr10 hn; omega)],
      hpub, hpre⟩
    have L := G.L
    -- What the tail writes.
    have st : ∀ o, 128 ≤ o → o + 4 ≤ 2560 → (o + 4 ≤ tglO ∨ (tglO + 4 ≤ o ∧ o + 4 ≤ zO) ∨ zO + 4 ≤ o) →
        slotv s₃.mem (p.2 8) o = slotv s₂.mem (p.2 8) o := fun o h₁ h₂ h₃ => by
      rw [slotv_eq, slotv_eq]
      refine slot_frame f₃ fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [tglO, zO] at h₃
      rcases hr with rfl | rfl
      · exact Lay.w_w (by simp only [zO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [tglO]; omega) (by omega) (by decide)
    have f₃' : Frame [⟨w64 (p.2 8) + BitVec.ofNat 64 128, 2432⟩] s₂.mem s₃.mem := f₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    have fE : Frame [⟨w64 (p.2 8) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s₃.mem := by
      exact e.frame.trans f₃'
    have dE : ∀ {q : Addr} {n : Nat}, (⟨q, n⟩ : Region).Disjoint ⟨w64 (p.2 8), 2560⟩ →
        ∀ r ∈ [(⟨w64 (p.2 8) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨q, n⟩ : Region).Disjoint r :=
      fun hq r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hq.sub_right (Lay.wSub (by decide))
    have sl : ∀ q ∈ oKeeps, slotv s₃.mem (p.2 8) q.2 = p.2 q.1 := fun q hq => by
      have := (show ∀ q ∈ oKeeps, 128 ≤ q.2 ∧ q.2 + 4 ≤ 2560 ∧
          (q.2 + 4 ≤ tglO ∨ (tglO + 4 ≤ q.2 ∧ q.2 + 4 ≤ zO) ∨ zO + 4 ≤ q.2) ∧ q.1 < 9 by decide) q hq
      rw [st _ this.1 this.2.1 this.2.2.1, e.slots q hq, a _ (by omega)]
    have hR := G.rounds
    have he : Env (p.2 0) (stOf (p.2 8)) (p.2 8) p.1 s₃ := by
      refine ⟨by rw [bp₃, e.ebp], by rw [si₃, e.esi], by rw [sp₃, e.esp, esp], ?_, ?_, by rw [wr₃, e.wr]; exact wW,
        by have := sl (0, ctxO) (by simp); rwa [slotv_eq] at this⟩
      · rw [rd₃, e.rd, h.rd, a 0 (by omega)]; exact covers_of_mem (by simp)
      · rw [wr₃, e.wr, stOf_w64 fw]; exact covers_off wW (by decide) (by decide)
    refine ⟨⟨he, ⟨by rw [sl (1, roundsO) (by simp), ofNat_toNat32], hR⟩, sl (4, aadO) (by simp), sl (5, alO) (by simp),
      sl (6, dataO) (by simp), sl (7, lenO) (by simp), z₃, sl (3, nlO) (by simp), ?_, ?_, ?_, ?_, ?_,
      by rw [rd₃, e.rd], by rw [wr₃, e.wr], ?_, ?_, ?_⟩, sl (2, dO) (by simp), sl (3, nO) (by simp), ?_, ?_, ?_⟩
    · have := e.saved.frame f₃ fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      exact this
    · rw [← esp, ret_kept fE (dE (by rw [esp]; exact G.r_w))]
    · exact ciph_frame fE (dE G.L.cw) hR
    · rw [ctxH_eq]; exact blockAt_frame fE (dE (G.L.cw.sub_left (Lay.ctxSub (by decide))))
    · exact bytesAt_frame fE (dE G.a_w) (by omega)
    · rw [rd₃, wr₃, e.rd, e.wr, h.rd, h.wr, a 2 (by omega), a 3 (by omega)]; exact covers_of_mem (by simp)
    · rw [rd₃, wr₃, e.rd, e.wr, h.rd, h.wr, a 4 (by omega), a 5 (by omega)]; exact covers_of_mem (by simp)
    · rw [wr₃, e.wr, h.wr, a 6 (by omega), a 7 (by omega)]; exact covers_of_mem (by simp)
    · exact bytesAt_frame fE (dE G.n_w) (by omega)
    · exact bytesAt_frame fE (dE G.d_w) (by omega)
    · refine bytesAt_frame fE (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      have := Lay.w_w (W := p.2 8) (a := 0) (n := 16) (d := 128) (k := 2432) (.inl (by decide)) (by decide) (by decide)
      rwa [BitVec.add_zero] at this
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 8 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [pubOf_esp h₁, pubOf_esp h₂]) (by taint_decide)) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) ht)
    subst s
    have h := hPre _ hpre
    have rA : Covers [argsR (s₀.gpr .esp) nA] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, h.rd, h.wr]; exact covers_of_mem (by simp)
    exact WP.mono (arg0_ok (argIn_of rA h.fg (by omega))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubOf_arg hpub (by omega), by rw [sp]; exact pubOf_esp hpub⟩

end VG.Proof.AesGcm.X86
