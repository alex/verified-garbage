import VerifiedGarbage.Impl.MlDsa.Arm.Message
import VerifiedGarbage.Proof.MlKem.Arm.Keccak
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.Message.Common

/-!
# ML-DSA on ARMv7, `sign_message` and `verify_message`: where everything is

Untrusted: everything here is checked by Lean. The function's buffers, the
36 bytes of stack below the stack pointer on entry (`STK`, which the calls'
frames use), `scratch` (`SC`) and the 1 KiB `X` in it after the working
space of the function on `μ` (`Lay`): the Keccak state, the sponge
functions' working space and `μ` in its first 904 bytes (`W`), then the
saved registers and arguments and the two bytes of the formatted message.
`Ctx` is what holds from the entry's saves to the exit: the permissions,
the stack pointer, `r7` pointing at `X`, the callee-saved registers, the
saves, and that memory changed only in `scratch` and `STK`. `Ctx.keep`
carries it over code that writes only within `W` and `STK`.
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.Sha3 (bytesAt)

theorem covers_of_within {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, o, hb, hl⟩ := h r hr
    exact ⟨R, hR, o, hb, hl⟩

/-! ## The layout -/

/-- The stack pointer on entry, the arguments, the size of `scratch`, the
offset `E` of the 1 KiB `X` in it, and the permissions on entry. -/
structure Lay where
  SP : BitVec 32
  key : BitVec 32
  keyLen : Nat
  msg : BitVec 32
  len : BitVec 32
  ctx : BitVec 32
  ctxLen : BitVec 32
  rnd : BitVec 32
  sig : BitVec 32
  scr : BitVec 32
  scrLen : Nat
  E : Nat
  rd : List Region
  wr : List Region

namespace Lay

variable (L : Lay)

/-- The 36 bytes of stack the calls' frames use. -/
abbrev STK : Region := ⟨State.addr L.SP - BitVec.ofNat 64 36, 36⟩
/-- `scratch`. -/
abbrev SC : Region := ⟨State.addr L.scr, L.scrLen⟩
/-- The 1 KiB, as a register holds it and as an address. -/
abbrev X32 : BitVec 32 := L.scr + BitVec.ofNat 32 L.E
abbrev X : Addr := State.addr L.X32
abbrev XS : Region := ⟨L.X, 1024⟩
/-- What the calls write in it: the Keccak state, the sponge functions'
working space and `μ`. -/
abbrev W : Region := ⟨L.X, 904⟩
abbrev ST : Addr := L.X
abbrev KS : Addr := L.X + BitVec.ofNat 64 200
abbrev MU : Addr := L.X + BitVec.ofNat 64 840
abbrev KEY : Region := ⟨State.addr L.key, L.keyLen⟩
abbrev MSG : Region := ⟨State.addr L.msg, L.len.toNat⟩
abbrev CTX : Region := ⟨State.addr L.ctx, L.ctxLen.toNat⟩

/-- The saved arguments, at `X + 912 + 4j`. -/
def vals : List (BitVec 32) := [L.key, L.msg, L.len, L.ctx, L.ctxLen, L.rnd, L.sig, L.scr]

/-- What the contract says of where everything is. -/
structure Ok : Prop where
  ctxLt : L.ctxLen.toNat < 256
  hE : L.E + 1024 ≤ L.scrLen
  hKey : 128 ≤ L.keyLen ∧ L.keyLen < 2 ^ 16
  nSP : 36 ≤ L.SP.toNat
  nScr : L.scr.toNat + L.scrLen ≤ 2 ^ 32
  inSC : L.SC ∈ L.wr
  inKey : L.KEY ∈ L.rd
  inMsg : L.MSG ∈ L.rd
  inCtx : L.CTX ∈ L.rd
  xKey : L.SC.Disjoint L.KEY
  xMsg : L.SC.Disjoint L.MSG
  xCtx : L.SC.Disjoint L.CTX
  kX : L.STK.Disjoint L.SC
  kKey : L.STK.Disjoint L.KEY
  kMsg : L.STK.Disjoint L.MSG
  kCtx : L.STK.Disjoint L.CTX
  nKey : L.key.toNat + L.keyLen ≤ 2 ^ 32
  nMsg : L.msg.toNat + L.len.toNat ≤ 2 ^ 32
  nCtx : L.ctx.toNat + L.ctxLen.toNat ≤ 2 ^ 32

end Lay

namespace Lay.Ok

variable {L : Lay}

theorem x32_lt (h : L.Ok) : L.X32.toNat + 1024 ≤ 2 ^ 32 := by
  have := h.nScr; have := h.hE
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := L.E) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- `X` in `scratch`. -/
theorem x_eq (h : L.Ok) : L.X = State.addr L.scr + BitVec.ofNat 64 L.E :=
  addr_add (by have := h.nScr; have := h.hE; omega)

/-- An address in the 1 KiB, as an instruction computes it from `r7`. -/
theorem xo (h : L.Ok) {o : Nat} (ho : o < 1024) :
    State.addr (L.X32 + BitVec.ofNat 32 o) = L.X + BitVec.ofNat 64 o :=
  addr_add (by have := h.x32_lt; omega)

theorem x_toNat (h : L.Ok) : L.X.toNat + 1024 ≤ 2 ^ 32 := by
  rw [Proof.MlKem.Arm.addr_toNat]; exact h.x32_lt

theorem xs_sc (h : L.Ok) : Within L.XS L.SC := ⟨L.E, h.x_eq, h.hE⟩

theorem sub_sc (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) : Region.Sub ⟨L.X + BitVec.ofNat 64 e, k⟩ L.SC :=
  (Within.trans (within_off L.X h₂) h.xs_sc).sub

theorem stk_x (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    Region.Disjoint L.STK ⟨L.X + BitVec.ofNat 64 e, k⟩ :=
  h.kX.sub_right (h.sub_sc h₂)

theorem x_r (h : L.Ok) {r : Region} (hr : L.SC.Disjoint r) {e k : Nat} (h₂ : e + k ≤ 1024) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 e, k⟩ r :=
  hr.sub_left (h.sub_sc h₂)

/-- The 1 KiB is writable. -/
theorem covX (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) : ∃ R ∈ L.wr, Within ⟨L.X + BitVec.ofNat 64 e, k⟩ R :=
  ⟨L.SC, h.inSC, (within_off L.X h₂).trans h.xs_sc⟩

/-- Bytes of the 1 KiB are writable. -/
theorem inW (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) : InRegions L.wr (L.X + BitVec.ofNat 64 e) k := by
  refine ⟨L.SC, h.inSC, ?_⟩
  rw [h.x_eq, add_add]
  have := h.hE; have := h.nScr
  exact Offset.contains_base _ (by omega) (by omega)

/-- What lies within the first 904 bytes of `X`, or in `STK`, is apart from the saves. -/
theorem sv_disj (h : L.Ok) {r : Region} (hr : Within r L.W ∨ Region.Sub r L.STK) {d n : Nat} (hd : d + n ≤ 120) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 (904 + d), n⟩ r := by
  rcases hr with hr | hr
  · obtain ⟨o, hb, hl⟩ := hr
    obtain ⟨b, k⟩ := r
    simp only at hb hl
    subst hb
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact (h.kX.symm.sub_left (h.sub_sc (by omega))).sub_right hr

end Lay.Ok

/-! ## From the entry's saves to the exit -/

/-- The state from the entry's saves to the exit: `g` the registers on
entry, `m₀` the memory. -/
structure Ctx (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = L.wr
  sp : t.sp = L.SP
  r7 : t.gpr .r7 = L.X32
  cs : ∀ r ∈ preserved, r ≠ .r7 → r ≠ .lr → t.gpr r = g r
  s7 : t.mem.readW (L.X + BitVec.ofNat 64 (904 + 0)) 32 = g .r7
  sLR : t.mem.readW (L.X + BitVec.ofNat 64 (904 + 4)) 32 = g .lr
  slot : ∀ j < 8, t.mem.readW (L.X + BitVec.ofNat 64 (904 + (8 + 4 * j))) 32 = L.vals.getD j 0
  hdr : bytesAt t.mem (L.X + BitVec.ofNat 64 (904 + 40)) 2 = [0, BitVec.ofNat 8 L.ctxLen.toNat]
  frame : Frame [L.SC, L.STK] m₀ t.mem

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t t' : State}

/-- Code that writes only registers but `r7` and the callee-saved ones. -/
theorem regs (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hm : t'.mem = t.mem) (hg : ∀ r ∈ preserved, r ≠ .lr → t'.gpr r = t.gpr r) : Ctx L g m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg .r7 (by decide) (by decide)).trans hc.r7,
    fun r hr h7 hl => (hg r hr hl).trans (hc.cs r hr h7 hl),
    by rw [hm]; exact hc.s7, by rw [hm]; exact hc.sLR, fun j hj => by rw [hm]; exact hc.slot j hj,
    by rw [hm]; exact hc.hdr, by rw [hm]; exact hc.frame⟩

/-- Code that writes memory only within the first 904 bytes of `X` and in `STK`. -/
theorem keep (hc : Ctx L g m₀ t) (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hg : ∀ r ∈ preserved, r ≠ .lr → t'.gpr r = t.gpr r) {rs : List Region} (hf : Frame rs t.mem t'.mem)
    (hrs : ∀ r ∈ rs, Within r L.W ∨ Region.Sub r L.STK) : Ctx L g m₀ t' := by
  have keep : ∀ d, d + 4 ≤ 120 → t'.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 =
      t.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 :=
    fun d h => hf.readW (Region.contains_self _ _) (fun r hr => hL.sv_disj (hrs r hr) h) (by decide)
  have khdr : bytesAt t'.mem (L.X + BitVec.ofNat 64 (904 + 40)) 2 =
      bytesAt t.mem (L.X + BitVec.ofNat 64 (904 + 40)) 2 :=
    Proof.MlKem.bytesAt_congr fun i hi =>
      hf.bytes (R := ⟨_, 2⟩) (fun r hr => hL.sv_disj (hrs r hr) (by decide)) (by show 2 ≤ 2 ^ 64; decide) hi
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg .r7 (by decide) (by decide)).trans hc.r7,
    fun r hr h7 hl => (hg r hr hl).trans (hc.cs r hr h7 hl),
    (keep 0 (by decide)).trans hc.s7, (keep 4 (by decide)).trans hc.sLR,
    fun j hj => (keep _ (by omega)).trans (hc.slot j hj), khdr.trans hc.hdr,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  rcases hrs r hr with h | h
  · exact ⟨L.SC, by simp, (h.trans ((within_base L.X (by decide : 904 ≤ 1024)).trans hL.xs_sc)).sub⟩
  · exact ⟨L.STK, by simp, h⟩

/-- A byte of a region apart from `scratch` and `STK`, as on entry. -/
theorem bytesAt_eq (hc : Ctx L g m₀ t) {p : Addr} {n : Nat} (hx : L.SC.Disjoint ⟨p, n⟩)
    (hk : L.STK.Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt m₀ p n :=
  Proof.MlKem.bytesAt_congr fun _ hi => Frame.bytes (R := ⟨p, n⟩) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx.symm
    · exact hk.symm) hn hi

/-- Bytes of `X` are readable. -/
theorem inX (hc : Ctx L g m₀ t) (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    InRegions (t.rd ++ t.wr) (L.X + BitVec.ofNat 64 e) k := by
  obtain ⟨R, hR, hc'⟩ := hL.inW h₂
  exact ⟨R, by rw [hc.rd, hc.wr]; exact List.mem_append_right _ hR, hc'⟩

end Ctx

end VG.Proof.MlDsa.Arm.Message
