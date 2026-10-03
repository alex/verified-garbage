import VerifiedGarbage.Proof.AesSiv.X86_64.Common
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Cmac.Block

/-!
# AES-SIV on x86-64: `vg_aes_siv_s2v_start`

The code zeroes a block of the working space and `D`, and calls
`vg_cmac_aes_finalize` on the zero block from the zero state `D`: `D` is then
`CIPH(0 ⊕ (0 ⊕ K1))`, the CMAC of `<zero>` with the context's subkeys
(`Spec.Siv.s2vStart`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 zero2 zero2_bytes frame_store2 mn)
open VG.Proof.CmacAes.Stream.X86_64 (FArgs fin_rel toNat_ofNat toNat_add_lt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The precondition, by name: the context `C`, the rounds `R`, `D` and the
working space `S`. -/
structure ZPre (s₀ : State) (C D S : Addr) (R : Nat) : Prop where
  rdi : s₀.gpr .rdi = C
  rsi : (s₀.gpr .rsi).toNat = R
  rdx : s₀.gpr .rdx = D
  rcx : s₀.gpr .rcx = S
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = [⟨C, 512⟩]
  wr : s₀.wr = [⟨D, 16⟩, ⟨S, 2560⟩]
  c_d : (⟨C, 512⟩ : Region).Disjoint ⟨D, 16⟩
  c_s : (⟨C, 512⟩ : Region).Disjoint ⟨S, 2560⟩
  d_s : (⟨D, 16⟩ : Region).Disjoint ⟨S, 2560⟩
  ret_c : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨C, 512⟩
  ret_d : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨D, 16⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2560⟩
  stk_c : (below (s₀.gpr .rsp) 16).Disjoint ⟨C, 512⟩
  stk_d : (below (s₀.gpr .rsp) 16).Disjoint ⟨D, 16⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint ⟨S, 2560⟩
  wC : C.toNat + 512 ≤ 2 ^ 64
  wD : D.toNat + 16 ≤ 2 ^ 64
  wS : S.toNat + 2560 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem ZPre.of {s₀ : State} (h : s2vStartX86_64.pre s₀) :
    ZPre s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

theorem ZPre.rsi_eq {s₀ : State} {C D S : Addr} {R : Nat} (hp : ZPre s₀ C D S R) :
    s₀.gpr .rsi = BitVec.ofNat 64 R :=
  BitVec.eq_of_toNat_eq (by rw [hp.rsi, toNat_ofNat (by rcases hp.rounds with h | h | h <;> omega)])

theorem startPre_ok {s₀ : State} {C D S : Addr} {R : Nat} (hp : ZPre s₀ C D S R) :
    ∃ s₁, runBlock isa startPre s₀ = some s₁ ∧ s₁.gpr .rdi = C ∧ s₁.gpr .rsi = BitVec.ofNat 64 R ∧
      s₁.gpr .rdx = D ∧ s₁.gpr .rcx = S + BitVec.ofNat 64 16 ∧ s₁.gpr .r8 = BitVec.ofNat 64 16 ∧
      s₁.gpr .r9 = S + BitVec.ofNat 64 256 ∧ (∀ r ∈ calleeSaved, s₁.gpr r = s₀.gpr r) ∧
      s₁.mem = zero2 (zero2 s₀.mem (S + BitVec.ofNat 64 16)) D ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have inS (d : Nat) (hd : d + 8 ≤ 2560) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨S, 2560⟩, by simp, Offset.contains_base _ hd (by have := hp.wS; omega)⟩
  have inD (d : Nat) (hd : d + 8 ≤ 16) : InRegions s₀.wr (D + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨D, 16⟩, by simp, Offset.contains_base _ hd (by have := hp.wD; omega)⟩
  refine ⟨_, by
    simp (config := {decide := true}) only [startPre, zero16, zOff, csOff, imm, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, readSrc32, execAlu,
      State.store64, State.ea, State.setReg32, offset_nat, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false, hp.rcx, hp.rdx,
      inS 16 (by decide), inS 24 (by decide), inD 0 (by decide), inD 8 (by decide)]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
    rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, hp.rdi, hp.rdx, hp.rcx, hp.rsi_eq,
    sx_ofNat (show 16 < 2 ^ 31 by decide), sx_ofNat (show 256 < 2 ^ 31 by decide)]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, ?_, trivial⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [zero2, zero2, Offset.add_add, k0]

/-- The arguments of the call. -/
theorem ZPre.fargs {s₀ s : State} {C D S : Addr} {R : Nat} (hp : ZPre s₀ C D S R)
    (rdi : s.gpr .rdi = C) (rsi : s.gpr .rsi = BitVec.ofNat 64 R) (rdx : s.gpr .rdx = D)
    (rcx : s.gpr .rcx = S + BitVec.ofNat 64 16) (r8 : s.gpr .r8 = BitVec.ofNat 64 16)
    (r9 : s.gpr .r9 = S + BitVec.ofNat 64 256) (rsp : s.gpr .rsp = s₀.gpr .rsp) (rd : s.rd = s₀.rd)
    (wr : s.wr = s₀.wr) :
    FArgs s C D (S + BitVec.ofNat 64 16) (S + BitVec.ofNat 64 256) 16 R where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := hp.rounds
  len := by decide
  kst := hp.c_d.sub_left (Region.sub_prefix (by decide))
  ks := (hp.c_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base S (by decide))
  pst := (hp.d_s.sub_right (Offset.sub_base S (by decide))).symm
  ps := Offset.disjoint S (by omega) (by omega) (by omega)
  sts := hp.d_s.sub_right (Offset.sub_base S (by decide))
  stkK := by rw [rsp]; exact hp.stk_c.sub_right (Region.sub_prefix (by decide))
  stkP := by rw [rsp]; exact hp.stk_s.sub_right (Offset.sub_base S (by decide))
  stkSt := by rw [rsp]; exact hp.stk_d
  stkS := by rw [rsp]; exact hp.stk_s.sub_right (Offset.sub_base S (by decide))
  wrapK := by have := hp.wC; omega
  wrapSt := hp.wD
  wrapP := by rw [toNat_add_lt S hp.wS (by decide)]; have := hp.wS; omega
  wrapS := by rw [toNat_add_lt S hp.wS (by decide)]; have := hp.wS; omega
  reads := by
    rw [rd, wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨C, 512⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2560⟩, by simp, 16, rfl, by simp⟩
    · exact ⟨⟨D, 16⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2560⟩, by simp, 256, rfl, by simp⟩
  writes := by
    rw [wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨D, 16⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨S, 2560⟩, by simp, 256, rfl, by simp⟩

theorem startPre_wp {s₀ : State} {C D S : Addr} {R : Nat} (hp : ZPre s₀ C D S R) :
    WP isa (.block startPre) s₀ fun s =>
      FArgs s C D (S + BitVec.ofNat 64 16) (S + BitVec.ofNat 64 256) 16 R ∧
        (∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r) ∧ s.mem = zero2 (zero2 s₀.mem (S + BitVec.ofNat 64 16)) D := by
  obtain ⟨s₁, run, rdi, rsi, rdx, rcx, r8, r9, g, m, rd, wr⟩ := startPre_ok hp
  exact WP.of_runBlock ⟨s₁, run, hp.fargs rdi rsi rdx rcx r8 r9 (g _ (by decide)) rd wr, g, m⟩

theorem xor_zeros {x : List Byte} (h : x.length = 16) : Spec.Cmac.xor x (Spec.Cmac.zeros 16) = x := by
  apply List.ext_getElem (by simp [Proof.Cmac.length_xor, Proof.Cmac.length_zeros, h])
  intro i h₁ h₂
  simp only [Spec.Cmac.xor, Spec.Cmac.zeros, List.getElem_zipWith, List.getElem_replicate]
  exact BitVec.xor_zero ..

theorem chain_blocks_nil (c : Spec.Cmac.Cipher) (z : List Byte) :
    Spec.Cmac.chain c z (Spec.Cmac.blocks 16 []) = z := rfl

/-- The last block of the zero block, with `K1` from memory: `K1 ⊕ 0`, and
XORing it into the zero state leaves it. -/
theorem xor_lastBlock_zeros (m : Mem) (p : Addr) (k2 : List Byte) :
    Spec.Cmac.xor (Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m p 16) k2 (Spec.Cmac.zeros 16)) (Spec.Cmac.zeros 16) =
      Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt m p 16) k2 (Spec.Cmac.zeros 16) :=
  xor_zeros (by simp [Spec.Cmac.lastBlock, Proof.Cmac.length_zeros, Proof.Cmac.length_xor,
    Proof.Cmac.bytesAt_length])

theorem s2v_start_wp (v : Ctr32Impl) {s₀ : State} (h0 : s2vStartX86_64.pre s₀) :
    WP isa (s2vStart v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ s2vStartX86_64.post s₀ s' := by
  have hp := ZPre.of h0
  generalize s₀.gpr .rdi = C at hp
  generalize s₀.gpr .rdx = D at hp
  generalize s₀.gpr .rcx = S at hp
  generalize (s₀.gpr .rsi).toNat = R at hp
  refine WP.seq (WP.mono (startPre_wp hp) fun s₁ ⟨h₁, g₁, m₁⟩ => ?_)
  refine WP.mono (finr_call v _ h₁) fun s₂ h₂ => ?_
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := g₁ _ (by decide)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have fz : Frame [⟨S + BitVec.ofNat 64 16, 16⟩, ⟨D, 16⟩] s₀.mem s₁.mem := by
    rw [m₁]
    exact ((frame_store2 _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans
      ((frame_store2 _ _ _).sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
  have ctx {d n : Nat} (hd : d + n ≤ 512) :
      Spec.Aes.bytesAt s₁.mem (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s₀.mem (C + BitVec.ofNat 64 d) n :=
    bytesAt_frame fz (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.c_s.sub_left (Offset.sub_base C hd)).sub_right (Offset.sub_base S (by decide))
      · exact hp.c_d.sub_left (Offset.sub_base C hd)) (by omega)
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, g₁ r hr], ?_⟩, ?_⟩
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    rw [h₂.frame.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.ret_d
        · exact hp.ret_s.sub_right (Offset.sub_base S (by decide))
        · rw [rsp₁]; exact Offset.base_disjoint_below _ (by decide)) (by decide),
      fz.readW c (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.ret_s.sub_right (Offset.sub_base S (by decide))
        · exact hp.ret_d) (by decide)]
  · show Spec.Aes.bytesAt s₂.mem (s₀.gpr .rdx) 16 =
      Spec.Siv.s2vStart (Spec.Siv.ctxMac s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat)
    have hz : Spec.Aes.bytesAt s₁.mem (S + BitVec.ofNat 64 16) 16 = Spec.Cmac.zeros 16 := by
      rw [← zero2_bytes s₀.mem (S + BitVec.ofNat 64 16), m₁]
      exact bytesAt_frame (frame_store2 _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.d_s.sub_right (Offset.sub_base S (by decide))).symm) (by decide)
    have hd : Spec.Aes.bytesAt s₁.mem D 16 = Spec.Cmac.zeros 16 := by rw [m₁]; exact zero2_bytes _ _
    have hk1 := ctx (d := 240) (n := 16) (by decide)
    have hk2 := ctx (d := 256) (n := 16) (by decide)
    have hs := ctx (d := 0) (n := 16 * (R + 1)) (by omega)
    rw [k0] at hs
    rw [hp.rdx, hp.rdi, hp.rsi, h₂.out, mn, hz, hd, hk1, hk2, hs, Spec.Siv.s2vStart, Spec.Siv.ctxMac,
      Spec.Siv.schedCiph, show Spec.Siv.zero = [] ++ Spec.Cmac.zeros 16 from rfl,
      Siv.cmacWith_split _ _ _ rfl (by decide) (Or.inl rfl), chain_blocks_nil, Proof.Cmac.xor_comm (Spec.Cmac.zeros 16)]
    simp only [xor_lastBlock_zeros]
    rfl

/-! ## Constant time -/

theorem s2v_start_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : s2vStartX86_64.pre s₀)
    (h0' : s2vStartX86_64.pre s₀') (hq : s2vStartX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (s2vStart v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := ZPre.of h0
  have hp' : ZPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat := by
    rw [q2, q3, q4, q5]; exact ZPre.of h0'
  generalize s₀.gpr .rdi = C at hp hp'
  generalize s₀.gpr .rdx = D at hp hp'
  generalize s₀.gpr .rcx = S at hp hp'
  generalize (s₀.gpr .rsi).toNat = R at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) (.block startPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption) hA).wp
    (F₁ := fun (s : State) => FArgs s C D (S + BitVec.ofNat 64 16) (S + BitVec.ofNat 64 256) 16 R ∧
      s.gpr .rsp = s₀.gpr .rsp)
    (F₂ := fun (s : State) => FArgs s C D (S + BitVec.ofNat 64 16) (S + BitVec.ofNat 64 256) 16 R ∧
      s.gpr .rsp = s₀'.gpr .rsp) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨WP.mono (startPre_wp hp) fun _ h => ⟨h.1, h.2.1 _ (by decide)⟩,
        WP.mono (startPre_wp hp') fun _ h => ⟨h.1, h.2.1 _ (by decide)⟩⟩
  have f := fin_rel v ("vg_cmac_aes_finalize" ++ v.suffix)
    (P := fun a b => (FArgs a C D (S + BitVec.ofNat 64 16) (S + BitVec.ofNat 64 256) 16 R ∧
      a.gpr .rsp = s₀.gpr .rsp) ∧
      FArgs b C D (S + BitVec.ofNat 64 16) (S + BitVec.ofNat 64 256) 16 R ∧ b.gpr .rsp = s₀'.gpr .rsp)
    fun a b h => ⟨_, _, _, _, _, _, h.1.1, h.2.1, by rw [h.1.2, h.2.2, q1]⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq f

theorem s2v_start_ct (v : Ctr32Impl) :
    ConstantTime isa s2vStartX86_64.pre s2vStartX86_64.pub (s2vStart v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (s2v_start_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesSiv.X86_64
