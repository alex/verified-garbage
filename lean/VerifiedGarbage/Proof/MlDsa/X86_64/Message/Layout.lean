import VerifiedGarbage.Impl.MlDsa.X86_64.Message
import VerifiedGarbage.Proof.MlKem.X86_64.KCall
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.Message.Common

/-!
# ML-DSA on x86-64, `sign_message` and `verify_message`: where everything is

Untrusted: everything here is checked by Lean. The function's buffers and
the 112 bytes of stack below its return address, from `B` up (`Lay`): the
frame (72 bytes, from `SP = B + 32`, `rsp` between its push and pop) and the
32 bytes below it that the calls use. `X` is the 1 KiB of `scratch` after
the working space of the function on `μ`. `Ctx` is what holds between the
frame's setting of the formatted message's two bytes and its pop: the
permissions, `rsp`, the callee-saved registers, the arguments in the frame,
the two bytes, and that memory changed only in `X` and the stack. `call_ok`
runs a call of verified code that writes only within `X` in such a state.
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.Sha3 (bytesAt)

/-! ## Regions within others -/

theorem covers_of_within {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, o, hb, hl⟩ := h r hr
    exact ⟨R, hR, o, hb, hl⟩

/-! ## Addresses -/

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_stk (t : State) (d : Nat) : t.ea (stk d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  show t.gpr .rsp + BitVec.ofInt 64 (d : Int) = _
  rw [ofInt_nat]

theorem ea_base (t : State) (r : Reg) (d : Nat) :
    t.ea { base := r, disp := (d : Int) } = t.gpr r + BitVec.ofNat 64 d := by
  show t.gpr r + BitVec.ofInt 64 (d : Int) = _
  rw [ofInt_nat]

theorem sx32 {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n :=
  Proof.MlKem.X86_64.sx_ofNat h

theorem zx32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ≠ .rsp) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem rsp_ce (t : State) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rsp = t.gpr .rsp - 8 := by
  rw [State.withRegions_gpr, State.callEntry_rsp]

theorem ne_cs {r d : Reg} (hr : r ∈ calleeSaved) (hd : d ∉ calleeSaved) : r ≠ d :=
  fun e => hd (e ▸ hr)

/-! ## The layout -/

/-- The buffers, the lowest byte of the stack used (`rsp - 112` on entry),
the offset `E` of the 1 KiB `X` in `scratch`, and the permissions on entry. -/
structure Lay where
  B : Addr
  key : Addr
  keyLen : Nat
  msg : Addr
  len : BitVec 64
  ctx : Addr
  ctxLen : BitVec 64
  rnd : Addr
  sig : Addr
  scr : Addr
  E : Nat
  rd : List Region
  wr : List Region

namespace Lay

variable (L : Lay)

/-- `rsp` between the frame's push and pop. -/
abbrev SP : Addr := L.B + BitVec.ofNat 64 40
/-- The frame. -/
abbrev FR : Region := ⟨L.SP, 72⟩
/-- The stack used: the frame and the 40 bytes below it. -/
abbrev STK : Region := ⟨L.B, 112⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 112, 8⟩
/-- The 1 KiB of the external function in `scratch`. -/
abbrev X : Addr := L.scr + BitVec.ofNat 64 L.E
abbrev XS : Region := ⟨L.X, 1024⟩
/-- The Keccak state, the sponge functions' working space and `μ`. -/
abbrev ST : Addr := L.X
abbrev KS : Addr := L.X + BitVec.ofNat 64 200
abbrev MU : Addr := L.X + BitVec.ofNat 64 840
abbrev KEY : Region := ⟨L.key, L.keyLen⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev CTX : Region := ⟨L.ctx, L.ctxLen.toNat⟩

/-- What the contract says of where everything is. -/
structure Ok : Prop where
  ctxLt : L.ctxLen.toNat < 256
  hE : L.E + 1024 < 2 ^ 31
  hKey : 128 ≤ L.keyLen ∧ L.keyLen < 2 ^ 31
  nB : L.B.toNat + 112 < 2 ^ 64
  inX : ∃ R ∈ L.wr, Within L.XS R
  inKey : L.KEY ∈ L.rd
  inMsg : L.MSG ∈ L.rd
  inCtx : L.CTX ∈ L.rd
  xKey : L.XS.Disjoint L.KEY
  xMsg : L.XS.Disjoint L.MSG
  xCtx : L.XS.Disjoint L.CTX
  kX : L.STK.Disjoint L.XS
  kKey : L.STK.Disjoint L.KEY
  kMsg : L.STK.Disjoint L.MSG
  kCtx : L.STK.Disjoint L.CTX
  nKey : L.key.toNat + L.keyLen ≤ 2 ^ 64
  nMsg : L.msg.toNat + L.len.toNat ≤ 2 ^ 64
  nCtx : L.ctx.toNat + L.ctxLen.toNat ≤ 2 ^ 64
  lenW : ∀ R ∈ L.wr, R.len ≤ 2 ^ 64

end Lay

namespace Lay.Ok

variable {L : Lay}

theorem stk_x (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 112) (h₂ : e + k ≤ 1024) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.X + BitVec.ofNat 64 e, k⟩ :=
  (h.kX.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_r (_h : L.Ok) {r : Region} (hr : L.STK.Disjoint r) {d n : Nat} (h₁ : d + n ≤ 112) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r :=
  hr.sub_left (Offset.sub_base _ h₁)

theorem x_r (_h : L.Ok) {r : Region} (hr : L.XS.Disjoint r) {e k : Nat} (h₂ : e + k ≤ 1024) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 e, k⟩ r :=
  hr.sub_left (Offset.sub_base _ h₂)

/-- The 1 KiB is writable. -/
theorem covX (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) : ∃ R ∈ L.wr, Within ⟨L.X + BitVec.ofNat 64 e, k⟩ R := by
  obtain ⟨R, hR, hw⟩ := h.inX
  exact ⟨R, hR, (within_off L.X h₂).trans hw⟩

end Lay.Ok

/-- `B + 40 - 8 = B + 32`. -/
theorem sp_sub8 (B : Addr) : B + BitVec.ofNat 64 40 - 8 = B + BitVec.ofNat 64 32 := by
  bv_omega

/-- The stack a call from `rsp = B + 40` uses. -/
theorem below_call_sub (B : Addr) {m : Nat} (hm : m ≤ 40) :
    Region.Sub (below (B + BitVec.ofNat 64 40) m) ⟨B, 40⟩ := by
  have : B + BitVec.ofNat 64 40 - BitVec.ofNat 64 m = B + BitVec.ofNat 64 (40 - m) := by
    rw [Offset.sub_ofNat_eq (B + BitVec.ofNat 64 40) (a := m) (b := 40) hm, BitVec.add_sub_cancel]
  show Region.Sub ⟨B + BitVec.ofNat 64 40 - BitVec.ofNat 64 m, m⟩ _
  rw [this]
  exact Offset.sub_base _ (by omega)

theorem below24 (B : Addr) : below (B + BitVec.ofNat 64 32) 24 = ⟨B + BitVec.ofNat 64 8, 24⟩ := by
  show (⟨B + BitVec.ofNat 64 32 - BitVec.ofNat 64 24, 24⟩ : Region) = _
  congr 1; bv_omega

theorem below32 (B : Addr) : below (B + BitVec.ofNat 64 32) 32 = ⟨B, 32⟩ := by
  show (⟨B + BitVec.ofNat 64 32 - BitVec.ofNat 64 32, 32⟩ : Region) = _
  rw [BitVec.add_sub_cancel]

/-! ## Between the frame's push and pop -/

/-- The state between the setting of the formatted message's bytes and the
frame's pop: `g` and `mx` are the registers and MXCSR on entry, `m₀` the
memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 64) (mx : BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.FR :: L.wr
  rsp : t.gpr .rsp = L.SP
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  mx : t.mxcsr.extractLsb' 6 10 = mx.extractLsb' 6 10
  pScr : t.mem.readW (L.SP + BitVec.ofNat 64 8) 64 = L.scr
  pRnd : t.mem.readW (L.SP + BitVec.ofNat 64 16) 64 = L.rnd
  pSig : t.mem.readW (L.SP + BitVec.ofNat 64 24) 64 = L.sig
  pCtxLen : t.mem.readW (L.SP + BitVec.ofNat 64 32) 64 = L.ctxLen
  pCtx : t.mem.readW (L.SP + BitVec.ofNat 64 40) 64 = L.ctx
  pLen : t.mem.readW (L.SP + BitVec.ofNat 64 48) 64 = L.len
  pMsg : t.mem.readW (L.SP + BitVec.ofNat 64 56) 64 = L.msg
  pKey : t.mem.readW (L.SP + BitVec.ofNat 64 64) 64 = L.key
  hdr : bytesAt t.mem L.SP 2 = [0, BitVec.ofNat 8 L.ctxLen.toNat]
  frame : Frame [L.XS, L.STK] m₀ t.mem

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that writes only caller-saved registers. -/
theorem regs (hc : Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : Ctx L g mx m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    by rw [hm]; exact hc.pScr, by rw [hm]; exact hc.pRnd, by rw [hm]; exact hc.pSig,
    by rw [hm]; exact hc.pCtxLen, by rw [hm]; exact hc.pCtx, by rw [hm]; exact hc.pLen,
    by rw [hm]; exact hc.pMsg, by rw [hm]; exact hc.pKey, by rw [hm]; exact hc.hdr,
    by rw [hm]; exact hc.frame⟩

/-- The same state, with the entry registers, MXCSR and memory given by others equal to them. -/
theorem congr (hc : Ctx L g mx m₀ t) {g' : Reg → BitVec 64} {mx' : BitVec 32} {m₀' : Mem}
    (hg : ∀ r ∈ calleeSaved, r ≠ .rsp → g r = g' r) (hmx : mx = mx') (hm : m₀ = m₀') : Ctx L g' mx' m₀' t := by
  subst hmx hm
  exact ⟨hc.rd, hc.wr, hc.rsp, fun r hr hr' => (hc.cs r hr hr').trans (hg r hr hr'), hc.mx, hc.pScr, hc.pRnd,
    hc.pSig, hc.pCtxLen, hc.pCtx, hc.pLen, hc.pMsg, hc.pKey, hc.hdr, hc.frame⟩

/-- A slot of the frame is readable. -/
theorem inFr (hc : Ctx L g mx m₀ t) {d : Nat} (h₂ : d + 8 ≤ 72) :
    InRegions (t.rd ++ t.wr) (L.SP + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h₂ (by omega)⟩

theorem inFrW (hc : Ctx L g mx m₀ t) {d n : Nat} (h₂ : d + n ≤ 72) :
    InRegions t.wr (L.SP + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains_base _ h₂ (by omega)⟩

theorem ea_fr (hc : Ctx L g mx m₀ t) (d : Nat) : t.ea (stk d) = L.SP + BitVec.ofNat 64 d := by
  rw [ea_stk, hc.rsp]

/-- The return address of a call from the frame. -/
theorem ret (hc : Ctx L g mx m₀ t) : below (t.gpr .rsp) 8 = ⟨L.B + BitVec.ofNat 64 32, 8⟩ := by
  rw [hc.rsp]
  show (⟨L.B + BitVec.ofNat 64 40 - BitVec.ofNat 64 8, 8⟩ : Region) = _
  rw [show (BitVec.ofNat 64 8 : BitVec 64) = 8 from rfl, sp_sub8]

/-- A byte of a region apart from `X` and the stack, as on entry. -/
theorem byte (hc : Ctx L g mx m₀ t) {R : Region} (hx : L.XS.Disjoint R) (hk : L.STK.Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.mem (R.base + BitVec.ofNat 64 i) = m₀ (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (R := R) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx.symm
    · exact hk.symm) hR hi

theorem bytesAt_eq (hc : Ctx L g mx m₀ t) {p : Addr} {n : Nat} (hx : L.XS.Disjoint ⟨p, n⟩)
    (hk : L.STK.Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt m₀ p n :=
  Proof.MlKem.bytesAt_congr fun _ hi => hc.byte (R := ⟨p, n⟩) hx hk hn hi

/-- A byte on entry to a call from the frame, if the return address misses it. -/
theorem ce_byte (t : State) {R : Region} (hd : (below (t.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.callEntry.mem (R.base + BitVec.ofNat 64 i) = t.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (t.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using hd.symm) hR hi

theorem ce_bytesAt (hc : Ctx L g mx m₀ t) {p : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨L.B + BitVec.ofNat 64 32, 8⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    bytesAt t.callEntry.mem p n = bytesAt t.mem p n :=
  Proof.MlKem.bytesAt_congr fun _ hi => ce_byte t (R := ⟨p, n⟩) (by rw [hc.ret]; exact hd) hn hi

end Ctx

/-- A state whose memory differs from that of a `Ctx` state only within `X`
and the 32 bytes below the frame. -/
theorem Ctx.of_frame {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}
    (hc : Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hmx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10) {rs : List Region}
    (hf : Frame (rs ++ [⟨L.B, 40⟩]) t.mem t'.mem) (hrs : ∀ r ∈ rs, Within r L.XS) : Ctx L g mx m₀ t' := by
  have hdisj : ∀ d n, d + n ≤ 72 → ∀ r ∈ rs ++ [⟨L.B, 40⟩],
      Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ r := by
    intro d n h₁ r hr
    rw [Lay.SP, add_add]
    rcases List.mem_append.mp hr with hr | hr
    · exact (hL.stk_r hL.kX (d := 40 + d) (n := n) (by omega)).sub_right (hrs r hr).sub
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)
  have keep : ∀ d, d + 8 ≤ 72 →
      t'.mem.readW (L.SP + BitVec.ofNat 64 d) 64 = t.mem.readW (L.SP + BitVec.ofNat 64 d) 64 :=
    fun d h => hf.readW (Region.contains_self _ _) (hdisj d 8 h) (by decide)
  have khdr : bytesAt t'.mem L.SP 2 = bytesAt t.mem L.SP 2 :=
    Proof.MlKem.bytesAt_congr fun i hi => by
      have := hf.bytes (R := ⟨L.SP + BitVec.ofNat 64 0, 2⟩) (fun r hr => hdisj 0 2 (by omega) r hr)
        (by show 2 ≤ 2 ^ 64; decide) hi
      simpa only [BitVec.add_zero] using this
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hcs .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'),
    hmx.trans hc.mx, (keep 8 (by omega)).trans hc.pScr, (keep 16 (by omega)).trans hc.pRnd,
    (keep 24 (by omega)).trans hc.pSig, (keep 32 (by omega)).trans hc.pCtxLen,
    (keep 40 (by omega)).trans hc.pCtx, (keep 48 (by omega)).trans hc.pLen,
    (keep 56 (by omega)).trans hc.pMsg, (keep 64 (by omega)).trans hc.pKey, khdr.trans hc.hdr,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨L.XS, by simp, (hrs r hr).sub⟩
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨L.STK, by simp, ?_⟩
    have := Offset.sub_base L.B (d := 0) (n := 40) (k := 112) (by omega)
    simpa using this

/-! ## Calls that write only within `X` -/

/-- A call of verified code from the frame, reading regions within the
permissions and writing only within `X`, keeps `Ctx`. -/
theorem call_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 3) {t : State} (hc : Ctx L g mx m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd, ∃ R ∈ L.rd ++ L.FR :: L.wr, Within r R)
    (hwsub : ∀ r ∈ wr, Within r L.XS) {Q : State → Prop}
    (hQ : ∀ s', Ctx L g mx m₀ s' → Frame (wr ++ [⟨L.B, 40⟩]) t.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = t.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (t.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) t Q := by
  obtain ⟨RX, hRX, hX⟩ := hL.inX
  have hwX : ∀ r ∈ wr, ∃ R ∈ L.wr, Within r R := fun r hr => ⟨RX, hRX, (hwsub r hr).trans hX⟩
  have hcov : Covers (rd ++ wr) (t.rd ++ t.wr) := by
    rw [hc.rd, hc.wr]
    refine covers_of_within fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact hsub r hr
    · obtain ⟨R, hR, hw⟩ := hwX r hr
      exact ⟨R, by simp [hR], hw⟩
  have hcovw : Covers wr t.wr := by
    rw [hc.wr]
    refine covers_of_within fun r hr => ?_
    obtain ⟨R, hR, hw⟩ := hwX r hr
    exact ⟨R, List.mem_cons_of_mem _ hR, hw⟩
  refine WP.call_mx hv hsp (by omega) hpre hcov hcovw fun s' hrd hwr hcs hf hg hpost hmx => ?_
  have hf' : Frame (wr ++ [⟨L.B, 40⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.rsp]
      exact below_call_sub _ (by omega)
  -- The frame is apart from what the call writes.
  have hdisj : ∀ d n, d + n ≤ 72 → ∀ r ∈ wr ++ [⟨L.B, 40⟩],
      Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ r := by
    intro d n h₁ r hr
    rw [Lay.SP, add_add]
    rcases List.mem_append.mp hr with hr | hr
    · exact (hL.stk_r hL.kX (d := 40 + d) (n := n) (by omega)).sub_right (hwsub r hr).sub
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega) (by omega)
  have keep : ∀ d, d + 8 ≤ 72 →
      s'.mem.readW (L.SP + BitVec.ofNat 64 d) 64 = t.mem.readW (L.SP + BitVec.ofNat 64 d) 64 :=
    fun d h => hf'.readW (Region.contains_self _ _) (hdisj d 8 h) (by decide)
  have khdr : bytesAt s'.mem L.SP 2 = bytesAt t.mem L.SP 2 :=
    Proof.MlKem.bytesAt_congr fun i hi => by
      have := hf'.bytes (R := ⟨L.SP + BitVec.ofNat 64 0, 2⟩) (fun r hr => hdisj 0 2 (by omega) r hr)
        (by show 2 ≤ 2 ^ 64; decide) hi
      simpa only [BitVec.add_zero] using this
  refine hQ s' ⟨hrd.trans hc.rd, hwr.trans hc.wr, ?_, fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'),
    hmx.trans hc.mx, (keep 8 (by omega)).trans hc.pScr, (keep 16 (by omega)).trans hc.pRnd,
    (keep 24 (by omega)).trans hc.pSig, (keep 32 (by omega)).trans hc.pCtxLen,
    (keep 40 (by omega)).trans hc.pCtx, (keep 48 (by omega)).trans hc.pLen,
    (keep 56 (by omega)).trans hc.pMsg, (keep 64 (by omega)).trans hc.pKey, khdr.trans hc.hdr,
    hc.frame.trans (Frame.sub hf' fun r hr => ?_)⟩ hf' hg hpost
  · rw [hcs .rsp (by simp [calleeSaved]), hc.rsp]
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨L.XS, by simp, (hwsub r hr).sub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨L.STK, by simp, ?_⟩
      have := Offset.sub_base L.B (d := 0) (n := 40) (k := 112) (by omega)
      simpa using this

end VG.Proof.MlDsa.X86_64.Message
