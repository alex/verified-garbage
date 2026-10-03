import VerifiedGarbage.Impl.Ed448.X86_64.Verify
import VerifiedGarbage.Proof.MlKem.X86_64.KCall
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed448 verification on x86-64: where everything is

The function's buffers and the 272 bytes of stack below its return address,
from `B` up (`Lay`): the frame (256 bytes, from `SP = B + 16`, `rsp` between
its push and pop), whose first 200 bytes (`DAT`: the header of `dom4`, the
hash and `k`) calls may write, and the 16 bytes below it that the calls use.
`Ctx` is what holds between the frame's push and pop: the permissions, `rsp`,
the callee-saved registers, the arguments in the frame, and that memory
changed only in `scratch` and the stack. `call_ok` runs a call of verified
code that writes only within `scratch` and `DAT` in such a state.
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify
open VG.Spec.Sha3 (bytesAt)

/-! ## Regions within others -/

/-- `r` lies at an offset within `R`. -/
def Within (r R : Region) : Prop := ∃ off, r.base = R.base + BitVec.ofNat 64 off ∧ off + r.len ≤ R.len

theorem Within.sub {r R : Region} (h : Within r R) : Region.Sub r R := by
  obtain ⟨off, hb, hl⟩ := h
  obtain ⟨b, n⟩ := r
  simp only at hb hl
  subst hb
  exact Offset.sub_base _ hl

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem Within.trans {r R R' : Region} (h : Within r R) (h' : Within R R') : Within r R' := by
  obtain ⟨o, hb, hl⟩ := h
  obtain ⟨o', hb', hl'⟩ := h'
  exact ⟨o' + o, by rw [hb, hb', add_add], by omega⟩

theorem within_off (p : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Within ⟨p + BitVec.ofNat 64 d, n⟩ ⟨p, k⟩ := ⟨d, rfl, h⟩

theorem within_base (p : Addr) {n k : Nat} (h : n ≤ k) : Within ⟨p, n⟩ ⟨p, k⟩ :=
  ⟨0, (BitVec.add_zero p).symm, by simpa using h⟩

theorem within_self (r : Region) : Within r r := ⟨0, (BitVec.add_zero _).symm, by simp⟩

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

theorem bytesAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

/-! ## The layout -/

/-- The buffers, the lowest byte of the stack used (`rsp - 272` on entry),
and the permissions on entry. -/
structure Lay where
  B : Addr
  pk : Addr
  ctx : Addr
  ctxLen : BitVec 64
  msg : Addr
  len : BitVec 64
  sig : Addr
  scr : Addr
  rd : List Region
  wr : List Region

namespace Lay

variable (L : Lay)

/-- `rsp` between the frame's push and pop. -/
abbrev SP : Addr := L.B + BitVec.ofNat 64 16
/-- The frame. -/
abbrev FR : Region := ⟨L.SP, 256⟩
/-- What calls may write in the frame: the header, the hash and `k`. -/
abbrev DAT : Region := ⟨L.SP, 200⟩
/-- The stack used: the frame and the 16 bytes below it. -/
abbrev STK : Region := ⟨L.B, 272⟩
/-- The return address. -/
abbrev RET : Region := ⟨L.B + BitVec.ofNat 64 272, 8⟩
/-- The Keccak state, the sponge functions' working space. -/
abbrev ST : Addr := L.scr
abbrev KS : Addr := L.scr + BitVec.ofNat 64 256
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev PK : Region := ⟨L.pk, 57⟩
abbrev SIG : Region := ⟨L.sig, 114⟩
abbrev MSG : Region := ⟨L.msg, L.len.toNat⟩
abbrev CTX : Region := ⟨L.ctx, L.ctxLen.toNat⟩
/-- The hash and `k`, in the frame. -/
abbrev H : Addr := L.SP + BitVec.ofNat 64 16
abbrev K : Addr := L.SP + BitVec.ofNat 64 136

/-- What the contract says of where everything is. -/
structure Ok : Prop where
  ctxLt : L.ctxLen.toNat < 256
  nB : L.B.toNat + 280 < 2 ^ 64
  wr : L.wr = [L.SCR]
  inPk : L.PK ∈ L.rd
  inSig : L.SIG ∈ L.rd
  inMsg : L.MSG ∈ L.rd
  inCtx : L.CTX ∈ L.rd
  xPk : L.SCR.Disjoint L.PK
  xSig : L.SCR.Disjoint L.SIG
  xMsg : L.SCR.Disjoint L.MSG
  xCtx : L.SCR.Disjoint L.CTX
  kScr : L.STK.Disjoint L.SCR
  kPk : L.STK.Disjoint L.PK
  kSig : L.STK.Disjoint L.SIG
  kMsg : L.STK.Disjoint L.MSG
  kCtx : L.STK.Disjoint L.CTX
  rScr : L.RET.Disjoint L.SCR
  nPk : L.pk.toNat + 57 ≤ 2 ^ 64
  nSig : L.sig.toNat + 114 ≤ 2 ^ 64
  nMsg : L.msg.toNat + L.len.toNat ≤ 2 ^ 64
  nCtx : L.ctx.toNat + L.ctxLen.toNat ≤ 2 ^ 64
  nScr : L.scr.toNat + 8192 ≤ 2 ^ 64

end Lay

namespace Lay.Ok

variable {L : Lay}

theorem stk_x (h : L.Ok) {d n e k : Nat} (h₁ : d + n ≤ 272) (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kScr.sub_left (Offset.sub_base _ h₁)).sub_right (Offset.sub_base _ h₂)

theorem stk_r (_h : L.Ok) {r : Region} (hr : L.STK.Disjoint r) {d n : Nat} (h₁ : d + n ≤ 272) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r :=
  hr.sub_left (Offset.sub_base _ h₁)

theorem x_r (_h : L.Ok) {r : Region} (hr : L.SCR.Disjoint r) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ r :=
  hr.sub_left (Offset.sub_base _ h₂)

end Lay.Ok

/-- `B + 16 - 8 = B + 8`. -/
theorem sp_sub8 (B : Addr) : B + BitVec.ofNat 64 16 - 8 = B + BitVec.ofNat 64 8 := by
  bv_omega

theorem sp_sub8' (B : Addr) : B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8 = B + BitVec.ofNat 64 8 :=
  sp_sub8 B

theorem sub88 (B : Addr) : B + BitVec.ofNat 64 8 - 8 = B := by bv_omega

/-- The stack a call from `rsp = B + 16` uses. -/
theorem below_call_sub (B : Addr) {m : Nat} (hm : m ≤ 16) :
    Region.Sub (below (B + BitVec.ofNat 64 16) m) ⟨B, 16⟩ := by
  have : B + BitVec.ofNat 64 16 - BitVec.ofNat 64 m = B + BitVec.ofNat 64 (16 - m) := by
    rw [Offset.sub_ofNat_eq (B + BitVec.ofNat 64 16) (a := m) (b := 16) hm, BitVec.add_sub_cancel]
  show Region.Sub ⟨B + BitVec.ofNat 64 16 - BitVec.ofNat 64 m, m⟩ _
  rw [this]
  exact Offset.sub_base _ (by omega)

/-! ## Between the frame's push and pop -/

/-- The state between the frame's push and pop: `g` and `mx` are the
registers and MXCSR on entry, `m₀` the memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 64) (mx : BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.FR :: L.wr
  rsp : t.gpr .rsp = L.SP
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = g r
  mx : t.mxcsr.extractLsb' 6 10 = mx.extractLsb' 6 10
  pPk : t.mem.readW (L.SP + BitVec.ofNat 64 fPk) 64 = L.pk
  pCtx : t.mem.readW (L.SP + BitVec.ofNat 64 fCtx) 64 = L.ctx
  pCtxLen : t.mem.readW (L.SP + BitVec.ofNat 64 fCtxLen) 64 = L.ctxLen
  pMsg : t.mem.readW (L.SP + BitVec.ofNat 64 fMsg) 64 = L.msg
  pLen : t.mem.readW (L.SP + BitVec.ofNat 64 fLen) 64 = L.len
  pSig : t.mem.readW (L.SP + BitVec.ofNat 64 fSig) 64 = L.sig
  pScr : t.mem.readW (L.SP + BitVec.ofNat 64 fScr) 64 = L.scr
  frame : Frame [L.SCR, L.STK] m₀ t.mem

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that writes only caller-saved registers. -/
theorem regs (hc : Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : Ctx L g mx m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    by rw [hm]; exact hc.pPk, by rw [hm]; exact hc.pCtx, by rw [hm]; exact hc.pCtxLen,
    by rw [hm]; exact hc.pMsg, by rw [hm]; exact hc.pLen, by rw [hm]; exact hc.pSig,
    by rw [hm]; exact hc.pScr, by rw [hm]; exact hc.frame⟩

/-- The same state, with the entry registers, MXCSR and memory given by others equal to them. -/
theorem congr (hc : Ctx L g mx m₀ t) {g' : Reg → BitVec 64} {mx' : BitVec 32} {m₀' : Mem}
    (hg : ∀ r ∈ calleeSaved, r ≠ .rsp → g r = g' r) (hmx : mx = mx') (hm : m₀ = m₀') : Ctx L g' mx' m₀' t := by
  subst hmx hm
  exact ⟨hc.rd, hc.wr, hc.rsp, fun r hr hr' => (hc.cs r hr hr').trans (hg r hr hr'), hc.mx, hc.pPk, hc.pCtx,
    hc.pCtxLen, hc.pMsg, hc.pLen, hc.pSig, hc.pScr, hc.frame⟩

/-- A word of the frame is readable. -/
theorem inFr (hc : Ctx L g mx m₀ t) {d : Nat} (h₂ : d + 8 ≤ 256) :
    InRegions (t.rd ++ t.wr) (L.SP + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains_base _ h₂ (by omega)⟩

theorem inFrW (hc : Ctx L g mx m₀ t) {d n : Nat} (h₂ : d + n ≤ 256) :
    InRegions t.wr (L.SP + BitVec.ofNat 64 d) n :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains_base _ h₂ (by omega)⟩

/-- The return address of a call from the frame. -/
theorem ret (hc : Ctx L g mx m₀ t) : below (t.gpr .rsp) 8 = ⟨L.B + BitVec.ofNat 64 8, 8⟩ := by
  rw [hc.rsp]
  show (⟨L.B + BitVec.ofNat 64 16 - BitVec.ofNat 64 8, 8⟩ : Region) = _
  rw [sp_sub8']

/-- A byte of a region apart from `scratch` and the stack, as on entry. -/
theorem byte (hc : Ctx L g mx m₀ t) {R : Region} (hx : L.SCR.Disjoint R) (hk : L.STK.Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.mem (R.base + BitVec.ofNat 64 i) = m₀ (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (R := R) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx.symm
    · exact hk.symm) hR hi

theorem bytesAt_eq (hc : Ctx L g mx m₀ t) {p : Addr} {n : Nat} (hx : L.SCR.Disjoint ⟨p, n⟩)
    (hk : L.STK.Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt m₀ p n :=
  bytesAt_congr fun _ hi => hc.byte (R := ⟨p, n⟩) hx hk hn hi

/-- A byte on entry to a call from the frame, if the return address misses it. -/
theorem ce_byte (t : State) {R : Region} (hd : (below (t.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    t.callEntry.mem (R.base + BitVec.ofNat 64 i) = t.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (t.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using hd.symm) hR hi

theorem ce_bytesAt (hc : Ctx L g mx m₀ t) {p : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    bytesAt t.callEntry.mem p n = bytesAt t.mem p n :=
  bytesAt_congr fun _ hi => ce_byte t (R := ⟨p, n⟩) (by rw [hc.ret]; exact hd) hn hi

end Ctx

/-- The slots of the frame's arguments are apart from `DAT`, `scratch` and the stack below the frame. -/
theorem slot_disj {L : Lay} (hL : L.Ok) {d : Nat} (h₁ : 200 ≤ d) (h₂ : d + 8 ≤ 256) {r : Region}
    (hr : Within r L.SCR ∨ Within r L.DAT ∨ r = ⟨L.B, 16⟩) :
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, 8⟩ r := by
  rw [Lay.SP, add_add]
  rcases hr with hr | hr | rfl
  · exact (hL.stk_r hL.kScr (d := 16 + d) (n := 8) (by omega)).sub_right hr.sub
  · have := Offset.disjoint L.B (d := 16 + d) (n := 8) (e := 16) (k := 200) (by omega) (by omega) (by omega)
    exact this.sub_right (by simpa [Lay.DAT, Lay.SP] using hr.sub)
  · exact Offset.disjoint_base _ (by omega) (by omega)

/-- A state whose memory differs from that of a `Ctx` state only within
`scratch`, `DAT` and the 16 bytes below the frame. -/
theorem Ctx.of_frame {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t' : State}
    (hc : Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hmx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10) {rs : List Region}
    (hf : Frame (rs ++ [⟨L.B, 16⟩]) t.mem t'.mem) (hrs : ∀ r ∈ rs, Within r L.SCR ∨ Within r L.DAT) :
    Ctx L g mx m₀ t' := by
  have keep : ∀ d, 200 ≤ d → d + 8 ≤ 256 →
      t'.mem.readW (L.SP + BitVec.ofNat 64 d) 64 = t.mem.readW (L.SP + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (fun r hr => slot_disj hL h₁ h₂ (by
      rcases List.mem_append.mp hr with hr | hr
      · rcases hrs r hr with h | h
        exacts [.inl h, .inr (.inl h)]
      · simp only [List.mem_singleton] at hr; exact .inr (.inr hr))) (by decide)
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hcs .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr'), hmx.trans hc.mx,
    (keep 200 (by decide) (by decide)).trans hc.pPk, (keep 208 (by decide) (by decide)).trans hc.pCtx,
    (keep 216 (by decide) (by decide)).trans hc.pCtxLen, (keep 224 (by decide) (by decide)).trans hc.pMsg,
    (keep 232 (by decide) (by decide)).trans hc.pLen, (keep 240 (by decide) (by decide)).trans hc.pSig,
    (keep 248 (by decide) (by decide)).trans hc.pScr, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  rcases List.mem_append.mp hr with hr | hr
  · rcases hrs r hr with h | h
    · exact ⟨L.SCR, by simp, h.sub⟩
    · have hd : Region.Sub L.DAT L.STK := by
        have := Offset.sub_base L.B (d := 16) (n := 200) (k := 272) (by omega)
        simpa [Lay.DAT, Lay.SP] using this
      exact ⟨L.STK, by simp, fun a ha => hd a (h.sub a ha)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨L.STK, by simp, ?_⟩
    have := Offset.sub_base L.B (d := 0) (n := 16) (k := 272) (by omega)
    simpa using this

/-! ## Calls -/

/-- A call of verified code from the frame, which nests calls at most once
more, reading regions within the permissions and writing only within
`scratch` and `DAT`, keeps `Ctx`. -/
theorem call_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 1) {t : State} (hc : Ctx L g mx m₀ t)
    {rd wr : List Region} (hpre : k.pre (t.callEntry.withRegions rd wr))
    (hsub : ∀ r ∈ rd, ∃ R ∈ L.rd ++ L.FR :: L.wr, Within r R)
    (hwsub : ∀ r ∈ wr, Within r L.SCR ∨ Within r L.DAT) {Q : State → Prop}
    (hQ : ∀ s', Ctx L g mx m₀ s' → Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = t.gpr r) →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (t.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) t Q := by
  have hwX : ∀ r ∈ wr, ∃ R ∈ L.FR :: L.wr, Within r R := fun r hr => by
    rcases hwsub r hr with h | h
    · exact ⟨L.SCR, by simp [hL.wr], h⟩
    · exact ⟨L.FR, by simp, h.trans (within_base _ (by decide))⟩
  have hcov : Covers (rd ++ wr) (t.rd ++ t.wr) := by
    rw [hc.rd, hc.wr]
    refine covers_of_within fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact hsub r hr
    · obtain ⟨R, hR, hw⟩ := hwX r hr
      exact ⟨R, List.mem_append_right _ hR, hw⟩
  have hcovw : Covers wr t.wr := by
    rw [hc.wr]
    exact covers_of_within hwX
  refine WP.call_mx hv hsp (by omega) hpre hcov hcovw fun s' hrd hwr hcs hf hg hpost hmx => ?_
  have hf' : Frame (wr ++ [⟨L.B, 16⟩]) t.mem s'.mem := by
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [hc.rsp]
      exact below_call_sub _ (by omega)
  exact hQ s' (hc.of_frame hL hrd hwr hcs hmx hf' hwsub) hf' hg hpost

end VG.Proof.Ed448.X86_64.Verify
