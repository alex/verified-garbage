import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Block

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: the rest of a block, the loop, and `pbkdf2`

As on x86 (`Proof/Pbkdf2/Whole/X86/Loop.lean`): a step copies `U₁` into `T`,
runs `iterate` for the rest of the chain, copies as much of `T` as the output
still needs (`copyLoop_ok`, `copy`'s loop for a length in `r9`), and moves on
to the next block; after the last one, `out` holds the derived key, and the
caller's registers are restored (`restore_ok`, HMAC's for any working space an
immediate offset reaches).
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Impl.Hmac.Generic.Arm (Hash scrAt copy)
open VG.Proof.Hmac.Generic.Arm (HashOK cclob count count_loop nm addr3 ofNat_succ32 left_val left_z CopyInv
  SavedRegs savedRegs saved8 saved8_fst saved8_sub saved_mem restoreList_ok restore_eq)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_subs wp_cmp wp_rev wp_ldr wp_str wp_ldrb wp_strb
  op2_imm op2_reg sub_beq sub_ofNat contains_offset eval_eq)
open VG.Proof.Hmac.Generic.Common (bytes_keep writeBytes_snoc bytesAt_snoc' not_mem_of_disjoint)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey xorPad ipad opad hmacBlockKey)

/-! ## `copy`'s loop, for a length in `r9` -/

/-- The loop of `copy`, from `r8 = 0` and `r9 = n > 0`. -/
theorem copyLoop_ok {src dst : Reg} (hs : src ∉ cclob) (hd : dst ∉ cclob)
    {so d n : Nat} (hso : so < 4096) (hdo : d < 4096) (hn : 0 < n) (hn' : n < 2 ^ 32) {s : State}
    (h8 : s.gpr .r8 = 0) (h9 : s.gpr .r9 = BitVec.ofNat 32 n)
    (hsw : (s.gpr src).toNat + so + n ≤ 2 ^ 32) (hdw : (s.gpr dst).toNat + d + n ≤ 2 ^ 32)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr (s.gpr src) + BitVec.ofNat 64 so + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨State.addr (s.gpr src) + BitVec.ofNat 64 so, n⟩
      ⟨State.addr (s.gpr dst) + BitVec.ofNat 64 d, n⟩) :
    WP isa (.loop (.block [.dp .add .r2 src (.reg .r8), .ldrb .r12 .r2 so, .dp .add .r2 dst (.reg .r8),
      .strb .r12 .r2 d, .dp .add .r8 .r8 (.imm 1), .subs .r9 .r9 (.imm 1)]) .ne) s
      (CopyInv s (State.addr (s.gpr src) + BitVec.ofNat 64 so) (State.addr (s.gpr dst) + BitVec.ofNat 64 d) n n) := by
  generalize eA : State.addr (s.gpr src) + BitVec.ofNat 64 so = A at hin hsep ⊢
  generalize eB : State.addr (s.gpr dst) + BitVec.ofNat 64 d = B at hout hsep ⊢
  have i0 : CopyInv s A B n 0 s :=
    ⟨rfl, rfl, rfl, fun _ _ => rfl, h8, h9, by rw [bytesAt, List.range_zero, List.map_nil, writeBytes_nil]⟩
  refine count_loop hn (CopyInv s A B n) (fun k hk t h => ?_) i0
  refine wp_add (op2_reg _ _) fun t₁ u₁ => ?_
  refine wp_ldrb (a := A + BitVec.ofNat 64 k) hso
    (by rw [u₁.gpr, h.other src hs, h.r8, addr3 (by omega), eA])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hin k hk) fun t₂ u₂ => ?_
  refine wp_add (op2_reg _ _) fun t₃ u₃ => ?_
  refine wp_strb (a := B + BitVec.ofNat 64 k) hdo
    (by rw [u₃.gpr, u₂.other dst (nm hd .r12), u₁.other dst (nm hd .r2), h.other dst hd,
      u₂.other .r8 (by decide), u₁.other .r8 (by decide), h.r8, addr3 (by omega), eB])
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₄ m₄ => ?_
  refine wp_add (op2_imm (by decide)) fun t₅ u₅ => wp_subs (op2_imm (by decide)) fun t₆ u₆ z₆ =>
    WP.block_nil ?_
  have h8' : t₅.gpr .r8 = BitVec.ofNat 32 (k + 1) := by
    rw [u₅.gpr, m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r8,
      ofNat_succ32]
  have h9' : t₅.gpr .r9 = BitVec.ofNat 32 (n - k) := by
    rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r9]
  refine ⟨⟨by rw [u₆.rd, u₅.rd, m₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, m₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₆.sp, u₅.sp, m₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr => by
      rw [u₆.other r (nm hr .r9), u₅.other r (nm hr .r8), m₄.gpr, u₃.other r (nm hr .r2), u₂.other r (nm hr .r12),
        u₁.other r (nm hr .r2), h.other r hr],
    by rw [u₆.other _ (by decide), h8'], by rw [u₆.gpr, h9', left_val hk], ?_⟩, ?_⟩
  · have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
    have v : (t₃.gpr .r12).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) := by
      rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, h.mem]
      simp only [writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega), ↓reduceIte]
      ext i hi; simp
    have e' := writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k))
      (by rw [hl]; omega)
    rw [hl] at e'
    rw [u₆.mem, u₅.mem, m₄.mem, v, u₃.mem, u₂.mem, u₁.mem, h.mem, bytesAt_snoc', e']
  · rw [z₆, h9', left_z hk hn']

/-! ## Restoring our caller's registers -/

/-- `VG.Proof.Hmac.Generic.Arm.restore_ok`, for any working space before
the save area that an immediate offset reaches. -/
theorem restore_ok (H : Hash) {s : State} {scr : BitVec 32} {L : Nat} (h11 : s.gpr .r11 = scr)
    (hW : 8 * H.W + 36 ≤ 4096) {s₀ : State} (hs : SavedRegs H scr s₀ s.mem) (hsc : ⟨State.addr scr, L⟩ ∈ s.wr)
    (hL : 8 * H.W + 36 ≤ L) (hfit : scr.toNat + L ≤ 2 ^ 32) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ (∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) := by
  have io : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ {d}, d + 4 ≤ L →
      InRegions (t.rd ++ t.wr) (State.addr scr + BitVec.ofNat 64 d) 4 := fun hr hw d hd => by
    rw [hr, hw]; exact Hmac.Generic.Common.InRegions.right' ⟨_, hsc, contains_offset hd (by omega)⟩
  rw [restore_eq]
  refine restoreList_ok (saved8 H) s _ (by rw [saved8_fst]; decide) (fun p hp => ?_)
    fun s₁ hl ho hm hrd hwr hsp => ?_
  · have := saved_mem H (saved8_sub H hp)
    refine ⟨?_, by omega, by rw [h11]; omega, by rw [h11]; exact io rfl rfl (by omega)⟩
    simp only [saved8, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
  have e11 : s₁.gpr .r11 = scr := by
    rw [ho _ (by rw [saved8_fst]; decide), h11]
  refine wp_ldr (by omega) (addr_add (by rw [e11]; omega)) (by rw [e11]; exact io hrd hwr (by omega))
    fun s₂ u => WP.block_nil ⟨by rw [u.mem, hm], by rw [u.rd, hrd], by rw [u.wr, hwr], by rw [u.sp, hsp],
      fun r hr => ?_⟩
  have hv : ∀ p ∈ saved8 H, s₂.gpr p.1 = s₀.gpr p.1 := fun p hp => by
    have h1 : p.1 ≠ .r11 := by
      simp only [saved8, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
    rw [u.other _ h1, hl p hp, h11, hs p (saved8_sub H hp)]
  simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hv (.r4, 8 * H.W) (by simp [saved8])
  · exact hv (.r5, 8 * H.W + 4) (by simp [saved8])
  · exact hv (.r6, 8 * H.W + 8) (by simp [saved8])
  · exact hv (.r7, 8 * H.W + 12) (by simp [saved8])
  · exact hv (.r8, 8 * H.W + 16) (by simp [saved8])
  · exact hv (.r9, 8 * H.W + 20) (by simp [saved8])
  · exact hv (.r10, 8 * H.W + 24) (by simp [saved8])
  · exact hv (.lr, 8 * H.W + 28) (by simp [saved8])
  · rw [u.gpr, e11, hm, hs (.r11, 8 * H.W + 32) (by simp [Hash.saved])]

variable {F : Fns}

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

/-! ## A step: `T`, from `U₁` and `iterate` -/

/-- `T ← U₁`. -/
theorem b6_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) {u : List Byte} (hu : bytesAt s.mem (A s₀ F.uO) F.H.D = u) :
    WP isa (copy .r11 F.uO .r11 F.tO F.H.D) s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (A s₀ F.uO) F.H.D = u ∧ bytesAt t.mem (A s₀ F.tO) F.H.D = u := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.reach
  refine WP.mono (copy_part_ok hp hz h.kr hz.D.1 (by omega) (by omega) (by omega) (Or.inl (by omega)))
    fun t ⟨kt, g, m⟩ => ?_
  have f : Frame [sR s₀ F.tO F.H.D] s.mem t.mem := by
    rw [m]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨h.keep hp hz (kt.rd.trans h.kr.rd.symm) (kt.wr.trans h.kr.wr.symm) (kt.sp.trans h.kr.sp.symm)
      (fun r hr => g r (by
        simp only [iregs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide))
      f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inl (.inr ⟨_, _, rfl, by omega, by omega⟩), ?_, ?_⟩
  · rw [bytes_keep f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega))
      (by omega)]
    exact hu
  · rw [m, Hmac.Generic.Common.bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega)]
    exact hu

/-- `iterate`'s arguments: the key's states, `U`, `c - 1`, `T` and `scratch`. -/
theorem b7_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.iterArgs) s fun t => Inv hF s₀ k t ∧ t.gpr .r0 = dO s₀ F.st0O ∧
      t.gpr .r1 = dO s₀ F.uO ∧ t.gpr .r3 = dO s₀ F.tO ∧ t.gpr .r2 = stackArg s₀ 0 - 1 ∧
      t.gpr .r12 = scr s₀ ∧ t.mem = s.mem := by
  have hl := layout (F := F); have he := end_le hz; have := hz.reach
  simp only [Fns.iterArgs, List.append_assoc]
  refine scr_ok h.kr (by omega) fun s₁ u₁ => ?_
  have i₁ := h.upd12 hp hz (by decide) u₁
  refine scr_ok i₁.kr (by omega) fun s₂ u₂ => ?_
  have i₂ := i₁.upd12 hp hz (by decide) u₂
  refine scr_ok i₂.kr (by omega) fun s₃ u₃ => ?_
  have i₃ := i₂.upd12 hp hz (by decide) u₃
  refine wp_arg hp i₃.kr (i := 0) (by decide) fun s₄ u₄ => wp_sub (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  have i₆ := ((i₃.upd hp hz (by decide) u₄).upd hp hz (by decide) u₅).upd hp hz (by decide) u₆
  refine ⟨i₆, ?_, ?_, ?_, ?_, ?_, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide) (by decide),
      u₂.other _ (by decide) (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide) (by decide),
      u₂.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), i₃.kr.r11]

theorem b8_args {k : Nat} {s : State} (h : Inv hF s₀ k s) (h0 : s.gpr .r0 = dO s₀ F.st0O)
    (h1 : s.gpr .r1 = dO s₀ F.uO) (h3 : s.gpr .r3 = dO s₀ F.tO) (h2 : s.gpr .r2 = stackArg s₀ 0 - 1)
    (h12 : s.gpr .r12 = scr s₀) :
    ItArgs hF.hH.SH hF.Wt s (dO s₀ F.st0O) (dO s₀ F.uO) (stackArg s₀ 0 - 1) (dO s₀ F.tO) (scr s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hF.hWt; have hS := hF.hH.hS; have hD := hF.hH.hD
  have hk := h.kr
  have e0 := dO_addr hp (o := F.st0O) (by omega)
  have eu := dO_addr hp (o := F.uO) (by omega)
  have et := dO_addr hp (o := F.tO) (by omega)
  exact
    { r0 := h0
      r1 := h1
      r2 := h2
      r3 := h3
      r12 := h12
      sp := by rw [hk.sp]; exact hp.sp24
      cr := by
        rw [hS, hD, e0, eu]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.st0O) (n := 2 * F.H.S) (by omega)
            exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
          · obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.uO) (n := F.H.D) (by omega)
            exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
      cw := by
        rw [hD, et]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp hk (by omega)
          · exact cov_low hp hk (by omega)
      k_t := by rw [hS, hD, e0, et]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      k_s := by rw [hS, e0]; exact (low_disj hz (by omega) (by omega)).symm
      u_t := by rw [hD, eu, et]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      u_s := by rw [hD, eu]; exact (low_disj hz (by omega) (by omega)).symm
      t_s := by rw [hD, et]; exact (low_disj hz (by omega) (by omega)).symm
      b_k := by rw [hS, e0]; exact b24 hp hk (part_sub (by omega))
      b_u := by rw [hD, eu]; exact b24 hp hk (part_sub (by omega))
      b_t := by rw [hD, et]; exact b24 hp hk (part_sub (by omega))
      b_s := b24 hp hk (low_sub (by omega))
      nk := by rw [hS, dO_toNat hp (by omega)]; have := hp.nsc; omega
      nu := by rw [hD, dO_toNat hp (by omega)]; have := hp.nsc; omega
      nt := by rw [hD, dO_toNat hp (by omega)]; have := hp.nsc; omega
      nsc := by have := hp.nsc; omega }

/-- `iterate`: `T_{k + 1}`. -/
theorem b8_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) (h0 : s.gpr .r0 = dO s₀ F.st0O)
    (h1 : s.gpr .r1 = dO s₀ F.uO) (h3 : s.gpr .r3 = dO s₀ F.tO) (h2 : s.gpr .r2 = stackArg s₀ 0 - 1)
    (h12 : s.gpr .r12 = scr s₀)
    (hu : bytesAt s.mem (A s₀ F.uO) F.H.D = prf hF s₀ (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)))
    (ht : bytesAt s.mem (A s₀ F.tO) F.H.D = prf hF s₀ (saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.frame (.push [.r12, .lr]) (.call F.itN F.itC) (.pop .r12 8)) s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (A s₀ F.tO) F.H.D = Tk hF s₀ (k + 1) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hF.hWt; have hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have e0 := dO_addr hp (o := F.st0O) (by omega)
  have eu := dO_addr hp (o := F.uO) (by omega)
  have et := dO_addr hp (o := F.tO) (by omega)
  refine it_frame (FnsOK.reprOK hF) (by rw [hS]; omega) (by rw [hD]; omega) hF.it hF.itSt
    (b8_args hp hz h h0 h1 h3 h2 h12) fun s' a post => ⟨h.after hp hz a fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [et, hD], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · have := post (K0 hF s₀) (by rw [h.k0l, hB]) (by rw [e0]; exact h.st.st0)
      (by rw [e0, hS, Hmac.Generic.Common.add_ofNat_add]; exact h.st.st1)
    rw [et, hD, eu, hu, ht] at this
    rw [this]
    have hc := hp.c0
    rw [show (stackArg s₀ 0 - 1).toNat = cc s₀ - 1 by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; show 1 ≤ (stackArg s₀ 0).toNat; exact hc)]; rfl]
    rfl

/-! ## A step: copying `T` out -/

omit hp hz in
theorem arg_ofNat (i : Nat) : stackArg s₀ i = BitVec.ofNat 32 (stackArg s₀ i).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

omit hp hz in
theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The bytes of `T` the output still needs. -/
theorem outLen_ok {k : Nat} (hk : k * F.H.D < ol s₀) {s : State} (h : Inv hF s₀ k s) :
    WP isa F.outLen s fun t => Inv hF s₀ k t ∧
      t.gpr .r9 = BitVec.ofNat 32 (min (ol s₀ - k * F.H.D) F.H.D) ∧ t.mem = s.mem := by
  have hD := hz.D; have hol : ol s₀ < 2 ^ 32 := (stackArg s₀ 2).isLt
  have hdn : dn F s₀ k = k * F.H.D := by show min _ _ = _; omega
  unfold Fns.outLen
  refine WP.seq (wp_arg hp h.kr (i := 2) (by decide) fun s₁ u₁ => wp_sub (op2_reg _ _) fun s₂ u₂ =>
    wp_lt hz.encD fun s₃ g₃ m₃ rd₃ wr₃ sp₃ z₃ => WP.block_nil ?_)
  have i₂ := (h.upd hp hz (by decide) u₁).upd hp hz (by decide) u₂
  have i₃ := i₂.same hp hz rd₃ wr₃ sp₃ (fun r hr => g₃ r (by
    simp only [iregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) m₃
  have e₂ : s₂.gpr .r9 = BitVec.ofNat 32 (ol s₀ - k * F.H.D) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.r4, hdn, arg_ofNat 2,
      sub_ofNat (by have : ol s₀ = (stackArg s₀ 2).toNat := rfl; omega)]
  have e₃ : s₃.gpr .r9 = BitVec.ofNat 32 (ol s₀ - k * F.H.D) := by rw [g₃ _ (by decide), e₂]
  have m₃' : s₃.mem = s.mem := by rw [m₃, u₂.mem, u₁.mem]
  have z : s₃.z = decide (ol s₀ - k * F.H.D < F.H.D) := by
    rw [z₃, e₂, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]
  refine WP.ite (decide (ol s₀ - k * F.H.D < F.H.D)) (by show eval .eq s₃ = _; rw [eval_eq, z])
    (fun hT => WP.block_nil ?_)
    fun hF' => Hmac.Generic.Arm.wp_movw fun s₄ u₄ => WP.block_nil ⟨i₃.upd hp hz (by decide) u₄, ?_, by rw [u₄.mem, m₃']⟩
  · have : ol s₀ - k * F.H.D < F.H.D := of_decide_eq_true hT
    exact ⟨i₃, by rw [e₃, Nat.min_eq_left (Nat.le_of_lt this)], m₃'⟩
  · have : ¬ ol s₀ - k * F.H.D < F.H.D := of_decide_eq_false hF'
    rw [u₄.gpr, Hmac.Generic.Arm.movw_ofNat (by omega), Nat.min_eq_right (by omega)]

/-- Copying `n` bytes of `T` to `out` after the `k D` written. -/
theorem outLoop_ok {k n : Nat} (hn : 0 < n) (hkn : k * F.H.D + n ≤ ol s₀) (hnD : n ≤ F.H.D) {s : State}
    (h : Inv hF s₀ k s) (h9 : s.gpr .r9 = BitVec.ofNat 32 n) (hkD : k * F.H.D < ol s₀) :
    WP isa F.outLoop s fun t => KR F s₀ t ∧ t.gpr .r4 = s.gpr .r4 ∧ t.gpr .r8 = BitVec.ofNat 32 n ∧
      t.mem = writeBytes s.mem (State.addr (out s₀) + BitVec.ofNat 64 (k * F.H.D))
        (bytesAt s.mem (A s₀ F.tO) n) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have hD := hz.D; have := hz.reach
  have hol : ol s₀ < 2 ^ 32 := (stackArg s₀ 2).isLt
  have hdn : dn F s₀ k = k * F.H.D := by show min _ _ = _; omega
  have hno := hp.no
  have eO : State.addr (out s₀ + BitVec.ofNat 32 (k * F.H.D)) = State.addr (out s₀) + BitVec.ofNat 64 (k * F.H.D) :=
    addr_add (by have : ol s₀ = (stackArg s₀ 2).toNat := rfl; omega)
  have tO' : (out s₀ + BitVec.ofNat 32 (k * F.H.D)).toNat = (out s₀).toNat + k * F.H.D := by
    rw [add_ofNat_eq _ (by have : ol s₀ = (stackArg s₀ 2).toNat := rfl; omega), toNat_ofNat32 (by omega)]
  have osub : Region.Sub ⟨State.addr (out s₀) + BitVec.ofNat 64 (k * F.H.D), n⟩ (outR s₀) :=
    Offset.sub_base _ hkn
  unfold Fns.outLoop
  refine WP.seq (wp_arg hp h.kr (i := 1) (by decide) fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ?_)
  have k₃ := ((h.kr.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃
  have e₉ : s₃.gpr .r9 = BitVec.ofNat 32 n := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h9]
  have e₁₀ : s₃.gpr .r10 = out s₀ + BitVec.ofNat 32 (k * F.H.D) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.r4, hdn]
  have e₄ : s₃.gpr .r4 = s.gpr .r4 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have eL : F.L8 = (F.W + F.H.S) * 8 := rfl
  refine WP.mono (copyLoop_ok (src := .r11) (dst := .r10) (so := F.tO) (d := 0) (by decide) (by decide)
    (by omega) (by decide) hn (by omega) u₃.gpr e₉
    (by rw [k₃.r11]; have := hp.nsc; omega) (by rw [e₁₀, tO']; omega)
    (fun j hj => by
      rw [k₃.r11]
      exact ⟨scR s₀ F, List.mem_append_right _ (by rw [k₃.wr]; exact sc_mem hp),
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    (fun j hj => by
      rw [e₁₀, eO, Hmac.Generic.Common.add_ofNat_add, Nat.zero_add]
      exact ⟨outR s₀, by rw [k₃.wr, hp.wr]; simp, by
        rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [k₃.r11, e₁₀, eO, Hmac.Generic.Common.add_ofNat_add, Nat.add_zero]
        exact (hp.o_s.sub_left osub).symm.sub_left (part_sub (F := F) (by omega)))) fun t c => ?_
  rw [k₃.r11, e₁₀, eO, Hmac.Generic.Common.add_ofNat_add, Nat.add_zero] at c
  have cm : t.mem = writeBytes s.mem (State.addr (out s₀) + BitVec.ofNat 64 (k * F.H.D))
      (bytesAt s.mem (A s₀ F.tO) n) := by rw [c.mem, m₃]
  have f : Frame [⟨State.addr (out s₀) + BitVec.ofNat 64 (k * F.H.D), n⟩] s₃.mem t.mem := by
    rw [cm, m₃]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨k₃.keep c.rd c.wr c.sp (fun r hr => c.other r (by
      simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    (rs := [⟨State.addr (out s₀) + BitVec.ofNat 64 (k * F.H.D), n⟩]) f
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.o_s.sub_left osub).symm.sub_left (sv_sub hz))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, osub⟩),
    by rw [c.other _ (by decide), e₄], by rw [c.r8], cm⟩

/-- The rest of a step: as much of `T` as the output needs, copied out,
`INT (k + 2)`, and whether that was the last block. -/
theorem tail_ok {k : Nat} (hk : k < nbk F s₀) {s : State} (h : Inv hF s₀ k s)
    (ht : bytesAt s.mem (A s₀ F.tO) F.H.D = Tk hF s₀ (k + 1)) :
    WP isa (.seq F.outLen (.seq F.outLoop (.block F.advance))) s fun t =>
      Inv hF s₀ (k + 1) t ∧ t.z = decide (k + 1 = nbk F s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have hD := hz.D; have := hz.reach
  have hol : ol s₀ < 2 ^ 32 := (stackArg s₀ 2).isLt
  have hno := hp.no
  have hkD : k * F.H.D < ol s₀ := (Whole.lt_nb hD.1).1 hk
  have hdn : dn F s₀ k = k * F.H.D := by show min _ _ = _; omega
  generalize en : min (ol s₀ - k * F.H.D) F.H.D = n
  have hn : 0 < n := by omega
  have hkn : k * F.H.D + n ≤ ol s₀ := by omega
  have hnD : n ≤ F.H.D := by omega
  have hdn' : dn F s₀ (k + 1) = k * F.H.D + n := by show min _ _ = _; rw [Nat.succ_mul]; omega
  have osub : Region.Sub ⟨State.addr (out s₀) + BitVec.ofNat 64 (k * F.H.D), n⟩ (outR s₀) :=
    Offset.sub_base _ hkn
  refine WP.seq (WP.mono (outLen_ok hp hz hkD h) fun s₁ ⟨i₁, c₁, m₁⟩ => ?_)
  rw [en] at c₁
  refine WP.seq (WP.mono (outLoop_ok hp hz hn hkn hnD i₁ c₁ hkD) fun s₂ ⟨k₂, b₂, e₂, m₂⟩ => ?_)
  unfold Fns.advance
  refine wp_add (op2_reg _ _) fun s₃ u₃ => ?_
  have k₃ := k₂.upd (by decide) u₃
  refine wp_ldr (a := A s₀ F.intO) (by omega) (addr_scr hp k₃ (by omega)) (by
      obtain ⟨r, hr, c⟩ := in_sc hp hz k₃.wr (o := F.intO) (n := 4) (by omega)
      exact ⟨r, List.mem_append_right _ hr, c⟩)
    fun s₄ u₄ => wp_rev fun s₅ u₅ => wp_add (op2_imm (by decide)) fun s₆ u₆ => wp_rev fun s₇ u₇ => ?_
  have k₇ := (((k₃.upd (by decide) u₄).upd (by decide) u₅).upd (by decide) u₆).upd (by decide) u₇
  refine wp_str (a := A s₀ F.intO) (by omega) (addr_scr hp k₇ (by omega)) (in_sc hp hz k₇.wr (by omega))
    fun s₈ m₈ => ?_
  have fr₈ : Frame [sR s₀ F.intO 4] s₇.mem s₈.mem := by
    rw [m₈.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have k₈ := k₇.write hz m₈.rd m₈.wr m₈.sp (fun r _ => by rw [m₈.gpr]) (by omega) (by omega) fr₈
  refine wp_arg hp k₈ (i := 2) (by decide) fun s₉ u₉ => wp_cmp (op2_reg _ _) fun s₁₀ f₁₀ z₁₀ => WP.block_nil ?_
  have m₁₀ : s₁₀.mem = s₂.mem.writeW (A s₀ F.intO) (s₇.gpr .r12) := by
    rw [f₁₀.mem, u₉.mem, m₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have fr₂ : Frame [sR s₀ F.intO 4] s₂.mem s₁₀.mem := by
    rw [m₁₀]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fr₁ : Frame [⟨State.addr (out s₀) + BitVec.ofNat 64 (k * F.H.D), n⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have dI : (sR s₀ F.intO 4).Disjoint ⟨State.addr (out s₀) + BitVec.ofNat 64 (k * F.H.D), n⟩ :=
    ((hp.o_s.sub_left osub).sub_right (part_sub (by omega))).symm
  have r₂ : s₂.mem.readW (A s₀ F.intO) 32 = byteRev32 (BitVec.ofNat 32 (k + 1)) := by
    rw [← i₁.intW]
    exact fr₁.readW (r := sR s₀ F.intO 4) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dI) (by decide)
  have e₇ : s₇.gpr .r12 = byteRev32 (BitVec.ofNat 32 (k + 1 + 1)) := by
    rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.mem, r₂, rev_eq, rev_eq, Whole.byteRev32_byteRev32, ofNat_succ32]
  have e₉ : s₉.gpr .r4 = BitVec.ofNat 32 (k * F.H.D + n) := by
    rw [u₉.other _ (by decide), m₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, b₂, e₂, i₁.r4, hdn, ← BitVec.ofNat_add]
  have hg : (Gk hF s₀ (k + 1)) = Gk hF s₀ k ++ Tk hF s₀ (k + 1) := Whole.G_succ _ _ _ _
  have tl : (Tk hF s₀ (k + 1)).length = F.H.D := by rw [← ht, bytesAt_length]
  refine ⟨⟨(k₈.upd (by decide) u₉).same f₁₀.rd f₁₀.wr f₁₀.sp (fun r _ => by rw [f₁₀.gpr]) f₁₀.mem, ?_, i₁.k0l,
    by rw [f₁₀.gpr, e₉, hdn'], by rw [m₁₀, Mem.readW_writeW_self32, e₇], ?_, ?_⟩, ?_⟩
  · refine i₁.st.keep hz (rs := [⟨State.addr (out s₀) + BitVec.ofNat 64 (k * F.H.D), n⟩, sR s₀ F.intO 4])
      ((fr₁.mono (by simp)).trans (fr₂.mono (by simp))) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.o_s.sub_left osub).sub_right (part_sub (by omega))).symm
    · exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  · rw [hg, List.length_append, i₁.glen, tl, Nat.succ_mul]
  · have osub' : Region.Sub ⟨State.addr (out s₀), k * F.H.D + n⟩ (outR s₀) := Region.sub_prefix hkn
    rw [hdn', bytes_keep fr₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.o_s.sub_left osub').sub_right (part_sub (by omega))) (by omega), m₂]
    have bw := VG.Proof.Sha256.Stream.bytesAt_writeBytes s₁.mem (State.addr (out s₀)) (k * F.H.D)
      (bytesAt s₁.mem (A s₀ F.tO) n) (by rw [bytesAt_length]; omega)
    rw [bytesAt_length] at bw
    have ob := i₁.outB
    rw [hdn] at ob
    rw [bw, ob, Hmac.Generic.Common.bytesAt_take _ _ hnD, m₁, ht, hg, List.take_append,
      i₁.glen, Nat.add_sub_cancel_left, List.take_of_length_le (l := Gk hF s₀ k) (i := k * F.H.D) (by rw [i₁.glen]),
      List.take_of_length_le (l := Gk hF s₀ k) (i := k * F.H.D + n) (by rw [i₁.glen]; omega)]
  · rw [z₁₀, e₉, u₉.gpr, arg_ofNat 2, sub_beq (by omega) (by omega)]
    have e1 : k + 1 < nbk F s₀ ↔ (k + 1) * F.H.D < ol s₀ := Whole.lt_nb hD.1
    rw [Nat.succ_mul] at e1
    have : (stackArg s₀ 2).toNat = ol s₀ := rfl
    refine decide_eq_decide.2 ⟨fun h1 => ?_, fun h1 => ?_⟩
    · by_contra h2
      have := e1.1 (by omega)
      omega
    · have : ¬ (k * F.H.D + F.H.D < ol s₀) := fun h' => absurd (e1.2 h') (by omega)
      omega

/-! ## The loop and `pbkdf2` -/

/-- A block of the output. -/
theorem block_ok {k : Nat} (hk : k < nbk F s₀) {s : State} (h : Inv hF s₀ k s) :
    WP isa F.block s fun t => Inv hF s₀ (k + 1) t ∧ t.z = decide (k + 1 = nbk F s₀) := by
  unfold Fns.block
  refine WP.seq (WP.mono (b1_ok hp hz h) fun s₁ ⟨i₁, r₁⟩ => ?_)
  refine WP.seq (WP.mono (b2_ok hp hz i₁) fun s₂ ⟨i₂, a₀, a₁, a₇, a₁₀, c₂, m₂⟩ => ?_)
  refine WP.seq (WP.mono (b3_ok hp hz i₂ a₀ a₁ a₇ a₁₀ c₂ (by rw [m₂]; exact r₁)) fun s₃ ⟨i₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (b4_ok hp hz i₃) fun s₄ ⟨i₄, a₀, a₁, a₁₀, a₁₂, c₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (b5_ok hp hz i₄ a₀ a₁ a₁₀ a₁₂ c₄ (by rw [m₄]; exact r₃)) fun s₅ ⟨i₅, u₅⟩ => ?_)
  refine WP.seq (WP.mono (b6_ok hp hz i₅ u₅) fun s₆ ⟨i₆, u₆, t₆⟩ => ?_)
  refine WP.seq (WP.mono (b7_ok hp hz i₆) fun s₇ ⟨i₇, a₀, a₁, a₃, a₂, a₁₂, m₇⟩ => ?_)
  refine WP.seq (WP.mono (b8_ok hp hz i₇ a₀ a₁ a₃ a₂ a₁₂ (by rw [m₇]; exact u₆) (by rw [m₇]; exact t₆))
    fun s₈ ⟨i₈, t₈⟩ => ?_)
  exact tail_ok hp hz hk i₈ t₈

/-- The loop over the blocks of the output, if there are any. -/
theorem loop_ok {s : State} (h : Inv hF s₀ 0 s) (hz' : s.z = decide (ol s₀ = 0)) :
    WP isa (.ite .eq (.block []) (.loop F.block .ne)) s (Inv hF s₀ (nbk F s₀)) := by
  have hD := hz.D
  have e0 : nbk F s₀ = 0 ↔ ol s₀ = 0 := Whole.nb_zero hD.1
  refine WP.ite (decide (ol s₀ = 0)) (by show eval .eq s = _; rw [eval_eq, hz'])
    (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · rw [e0.2 (of_decide_eq_true h0)]; exact h
  · have hpos : 0 < nbk F s₀ := by
      have := of_decide_eq_false h0; have : nbk F s₀ ≠ 0 := fun e => this (e0.1 e); omega
    exact count_loop hpos (Inv hF s₀) (fun k hk t ht => WP.mono (block_ok hp hz hk ht) fun t' ⟨i, z⟩ =>
      ⟨i, by rw [z]; exact decide_eq_decide.2 (by omega)⟩) h

/-- What `pbkdf2` leaves: our caller's registers, and the derived key in `out`. -/
theorem correct : WP isa F.pbkdf2 s₀ fun s' => abiPreserved s₀ s' ∧
    Spec.Pbkdf2.pbkdf2Hmac hF.hH.SH (bytesAt s₀.mem (State.addr (pw s₀)) (pwl s₀)) (saltB s₀) (cc s₀) (ol s₀) =
      some (bytesAt s'.mem (State.addr (out s₀)) (ol s₀)) := by
  have hD := hz.D
  unfold Fns.pbkdf2
  refine WP.seq (WP.mono (prologue_ok hp hz) fun s₁ k₁ => ?_)
  refine WP.seq (WP.mono (keyed_ok (hF := hF) hp hz k₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (setup_ok hp hz hF h₂) fun s₃ ⟨k₃, st₃, kl₃⟩ => ?_)
  refine WP.seq (WP.mono (loopInit_ok hp hz k₃ st₃ kl₃) fun s₄ ⟨i₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok hp hz i₄ z₄) fun s₅ h₅ => ?_)
  have k₅ := h₅.kr
  have hr := hz.reach; have := end_le hz; have := layout (F := F)
  refine WP.mono (restore_ok F.L k₅.r11 (by simp only [Fns.L]; omega) k₅.saved (by rw [k₅.wr]; exact sc_mem hp)
    (show 8 * F.W + 36 ≤ F.L8 by omega) hp.nsc)
    fun s' ⟨hm, _, _, hsp, hg⟩ => ⟨⟨fun r hr => hg r (Hmac.Generic.Arm.preserved_saved r hr), by rw [hsp, k₅.sp]⟩, ?_⟩
  have ob := h₅.outB
  have e : dn F s₀ (nbk F s₀) = ol s₀ := Whole.done_nb hD.1
  rw [e] at ob
  unfold Spec.Pbkdf2.pbkdf2Hmac
  rw [hF.hH.hD]
  exact Whole.pbkdf2_eq (prf hF s₀) (saltB s₀) hp.olD (by rw [hm, ob])

end

end VG.Proof.Pbkdf2.Whole.Arm
