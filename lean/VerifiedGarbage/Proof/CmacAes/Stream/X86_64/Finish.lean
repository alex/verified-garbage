import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Common
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_finish`

Untrusted: everything here is checked by Lean. The code copies the
chaining value to `out`, computes the number of bytes held back, and calls
`vg_cmac_aes_finalize` with the state as its key and `out` as its state:
its result is the MAC of the message the state represents (`repr_finish`).
The code before the call is constant time by the taint analysis, and the
call by its own proof (`fin_rel`), its arguments pinned by `HMid`.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, `out` (`O`), the scratch
buffer `S` and the rounds `R`. -/
structure HPre (s₀ : State) (St O S : Addr) (R : Nat) : Prop where
  rdi : s₀.gpr .rdi = St
  rcx : s₀.gpr .rcx = O
  r8 : s₀.gpr .r8 = S
  rsi : (s₀.gpr .rsi).toNat = R
  sp : 16 ≤ (s₀.gpr .rsp).toNat
  rd : s₀.rd = []
  wr : s₀.wr = [⟨St, 304⟩, ⟨O, 16⟩, ⟨S, 2304⟩]
  st_o : (⟨St, 304⟩ : Region).Disjoint ⟨O, 16⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  o_s : (⟨O, 16⟩ : Region).Disjoint ⟨S, 2304⟩
  ret_st : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨St, 304⟩
  ret_o : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨O, 16⟩
  ret_s : (⟨s₀.gpr .rsp, 8⟩ : Region).Disjoint ⟨S, 2304⟩
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint ⟨St, 304⟩
  stk_o : (below (s₀.gpr .rsp) 16).Disjoint ⟨O, 16⟩
  stk_s : (below (s₀.gpr .rsp) 16).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wO : O.toNat + 16 ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem HPre.of {s₀ : State} (h : finishX86_64.pre s₀) :
    HPre s₀ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p⟩

theorem rsi_ofNat {s₀ : State} {R : Nat} (h : (s₀.gpr .rsi).toNat = R) (_hR : R = 10 ∨ R = 12 ∨ R = 14) :
    s₀.gpr .rsi = BitVec.ofNat 64 R :=
  BitVec.eq_of_toNat_eq (by rw [h, toNat_ofNat (by omega)])

/-! ## Before the call -/

theorem finishPre_ok {s₀ : State} {St O S : Addr} {R : Nat} (hp : HPre s₀ St O S R) :
    ∃ s₁, runBlock isa finishPre s₀ = some s₁ ∧ s₁.gpr .rdi = St ∧ s₁.gpr .rsi = s₀.gpr .rsi ∧
      s₁.gpr .rdx = O ∧ s₁.gpr .rcx = St + BitVec.ofNat 64 288 ∧ s₁.gpr .r8 = s₀.gpr .rdx ∧
      s₁.gpr .r9 = S ∧ (∀ r ∈ calleeSaved, s₁.gpr r = s₀.gpr r) ∧
      s₁.zf = some (s₀.gpr .rdx == 0) ∧
      s₁.mem = copyMem s₀.mem O (St + BitVec.ofNat 64 272) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have hw := hp.wSt
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions (s₀.rd ++ s₀.wr) (St + BitVec.ofNat 64 d) 8 := by
    rw [hp.rd, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  have inO (d : Nat) (hd : d + 8 ≤ 16) : InRegions s₀.wr (O + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨O, 16⟩, by simp, Offset.contains_base _ hd (by have := hp.wO; omega)⟩
  refine ⟨_, by
    simp (config := {decide := true}) only [finishPre, runBlock_cons, runStep_some, runBlock_nil, at_,
      exec, readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false,
      hp.rdi, hp.rcx, inSt 272 (by decide), inSt 280 (by decide), inO 0 (by decide), inO 8 (by decide)]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false,
    BitVec.and_self, hp.rdi, hp.rcx, hp.r8, sx288]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, trivial, ?_, trivial⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [copyMem, k0, Offset.add_add]

/-- What the code before the call leaves. -/
structure HMid (s₀ : State) (St O S : Addr) (R : Nat) (s : State) : Prop where
  args : FArgs s St O (St + BitVec.ofNat 64 288) S (held (s₀.gpr .rdx).toNat) R
  mem : s.mem = copyMem s₀.mem O (St + BitVec.ofNat 64 272)
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r

theorem HPre.fargs {s₀ s : State} {St O S : Addr} {R L : Nat} (hp : HPre s₀ St O S R) (hL : L ≤ 16)
    (rdi : s.gpr .rdi = St) (rsi : s.gpr .rsi = s₀.gpr .rsi) (rdx : s.gpr .rdx = O)
    (rcx : s.gpr .rcx = St + BitVec.ofNat 64 288) (r8 : s.gpr .r8 = BitVec.ofNat 64 L)
    (r9 : s.gpr .r9 = S) (rsp : s.gpr .rsp = s₀.gpr .rsp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    FArgs s St O (St + BitVec.ofNat 64 288) S L R := by
  have hw := hp.wSt
  have pSt : Region.Sub ⟨St + BitVec.ofNat 64 288, L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  exact
  { rdi := rdi, rdx := rdx, rcx := rcx, r8 := r8, r9 := r9
    rsi := by rw [rsi]; exact rsi_ofNat hp.rsi hp.rounds
    rounds := hp.rounds, len := hL
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := (hp.st_s.sub_left pSt).sub_right (Region.sub_prefix (by decide))
    sts := hp.o_s.sub_right (Region.sub_prefix (by decide))
    stkK := by rw [rsp]; exact hp.stk_st.sub_right (Region.sub_prefix (by decide))
    stkP := by rw [rsp]; exact hp.stk_st.sub_right pSt
    stkSt := by rw [rsp]; exact hp.stk_o
    stkS := by rw [rsp]; exact hp.stk_s.sub_right (Region.sub_prefix (by decide))
    wrapK := by omega
    wrapSt := hp.wO
    wrapP := by rw [toNat_add_lt St hw (by decide)]; omega
    wrapS := by have := hp.wS; omega
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega⟩
      · exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }

theorem finPre_wp {s₀ : State} {St O S : Addr} {R : Nat} (hp : HPre s₀ St O S R) :
    WP isa finPre s₀ (HMid s₀ St O S R) := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, sv₁, zf₁, m₁, rd₁, wr₁⟩ := finishPre_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := sv₁ _ (by simp [calleeSaved])
  by_cases h0 : (s₀.gpr .rdx).toNat = 0
  · refine WP.ite true (by show s₁.zf = _; rw [zf₁, beq_zero_iff, h0]; rfl)
      (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨hp.fargs (held_le _) rdi₁ rsi₁ rdx₁ rcx₁ ?_ r9₁ rsp₁ rd₁ wr₁, m₁, sv₁⟩
    rw [h0, r8₁]; exact BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  · refine WP.ite false (by show s₁.zf = _; rw [zf₁, beq_zero_iff]; simp [h0])
      (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
      rfl, ?_⟩
    simp only [gpr_setReg, gpr_arithFlags, ite_true, r8₁, sx1, sx15]
    have hne : s₀.gpr .rdx ≠ 0 := fun e => h0 (by rw [e]; rfl)
    have hc : ∀ r ∈ calleeSaved, r ≠ .r8 := by decide
    refine ⟨hp.fargs (held_le _) rdi₁ rsi₁ rdx₁ rcx₁ (held_bv _ hne) r9₁ rsp₁ rd₁ wr₁, m₁,
      fun r hr => by simp only [gpr_setReg, gpr_arithFlags, hc r hr, ite_false]; exact sv₁ r hr⟩

/-! ## The whole function -/

theorem finish_wp (v : Ctr32Impl) {s₀ : State} (h0 : finishX86_64.pre s₀) :
    WP isa (finish v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ finishX86_64.post s₀ s' := by
  have hp := HPre.of h0
  generalize s₀.gpr .rdi = St at hp
  generalize s₀.gpr .rcx = O at hp
  generalize s₀.gpr .r8 = S at hp
  generalize (s₀.gpr .rsi).toNat = R at hp
  have hw := hp.wSt
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (fin_call v _ h₁.args) fun s₂ h₂ => ?_
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := h₁.saved _ (by simp [calleeSaved])
  -- The state is unchanged before the call.
  have fSt : ∀ {d n : Nat}, d + n ≤ 304 → Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 d) n =
      Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
    rw [h₁.mem]
    exact bytesAt_frame (copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_o.sub_left (Offset.sub_base St hd)) (by omega)
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.saved r hr], ?_⟩, ?_⟩
  · have big : Frame [⟨O, 16⟩, ⟨S, 2176⟩, below (s₀.gpr .rsp) 16] s₀.mem s₂.mem := by
      refine ((h₁.mem ▸ copyMem_frame _ _ _ : Frame [⟨O, 16⟩] s₀.mem s₁.mem).mono (by simp)).trans ?_
      rw [← rsp₁]; exact h₂.frame
    refine big.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_o
    · exact hp.ret_s.sub_right (Region.sub_prefix (by decide))
    · exact Offset.base_disjoint_below _ (by decide)
  · intro key msg hr hR hc hlen
    rw [hp.rdi] at hr
    -- `St + 240` and the others, as offsets.
    rw [Proof.Cmac.Stream.repr_iff] at hr
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := hr
    have hn : (s₀.gpr .rdx).toNat = msg.length := by rw [hc, toNat_ofNat hlen]
    rw [hp.rcx]
    have hR' : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.rsi]; exact hR
    have hsch : Spec.Aes.bytesAt s₁.mem St (16 * (R + 1)) = Spec.Aes.expandKey key := by
      have := fSt (d := 0) (n := 16 * (R + 1)) (by rcases hp.rounds with h | h | h <;> omega)
      rw [k0] at this; rw [this, hR']; exact hks
    have hciph : Spec.Cmac.aesWith R (Spec.Aes.bytesAt s₁.mem St (16 * (R + 1))) = Spec.Cmac.aes key := by
      rw [hsch, hR']; rfl
    have e₁ : Spec.Aes.bytesAt s₁.mem (St + 240) 32 = Spec.Aes.bytesAt s₀.mem (St + 240) 32 :=
      fSt (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + 272) 16 := by
      rw [h₁.mem]; exact copyMem_bytes _ (hp.st_o.symm.sub_right (Offset.sub_base St (by decide)))
    have e₃ : Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 288) (held (s₀.gpr .rdx).toNat) =
        Spec.Aes.bytesAt s₀.mem (St + 288) (held msg.length) := by
      rw [hn]; exact fSt (by have := held_le msg.length; omega)
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish
      ((Proof.Cmac.Stream.repr_iff _ _ _ _).mpr ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩)
    have out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

/-! ## Constant time -/

theorem finish_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : finishX86_64.pre s₀)
    (h0' : finishX86_64.pre s₀') (hq : finishX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finish v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
  have hp := HPre.of h0
  have hp' : HPre s₀' (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat := by
    rw [q2, q3, q5, q6]; exact HPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption) hA).wp
    (F₁ := HMid s₀ _ _ _ _) (F₂ := HMid s₀' _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩
  have c := fin_rel v ("vg_cmac_aes_finalize" ++ v.suffix) (P := fun s₁ s₂ =>
      HMid s₀ (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat s₁ ∧
      HMid s₀' (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r8) (s₀.gpr .rsi).toNat s₂)
    fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.1.args, by rw [q4]; exact h.2.args, by
      rw [h.1.saved _ (by simp [calleeSaved]), h.2.saved _ (by simp [calleeSaved]), q1]⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq c

theorem finish_ct (v : Ctr32Impl) :
    ConstantTime isa finishX86_64.pre finishX86_64.pub (finish v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finish_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86_64
