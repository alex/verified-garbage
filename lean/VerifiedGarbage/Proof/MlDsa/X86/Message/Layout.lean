import VerifiedGarbage.Impl.MlDsa.X86.Message
import VerifiedGarbage.Proof.MlKem.X86.Keccak
import VerifiedGarbage.Proof.MlKem.X86.Leaf
import VerifiedGarbage.Proof.MlKem.X86.CallRet
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.Message.Common

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: where everything is

Untrusted: everything here is checked by Lean. The stack pointer on entry,
the function's arguments, the `N` bytes of stack below it its contract gives
(the leaf's frame, then `STK`, which the calls use), `scratch` (`SC`) and the
1 KiB `X` in it after the working space of the function on `μ` (`Lay`): the
Keccak state, the sponge functions' working space and `μ` in its first 904
bytes (`W`), then the two bytes of the formatted message. `Ctx` is what
holds in the body of the leaf, from the entry's stores to the end: `esp`,
`esi` pointing at `X`, the permissions, the arguments, the two bytes, and
that memory changed only in `scratch` and `STK` since the frame's push.
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (E0 P0 frameR retR)
open VG.Spec.Sha3 (bytesAt)

theorem covers_of_within {rs rs' : List Region} (h : ∀ r ∈ rs, ∃ R ∈ rs', Within r R) : Covers rs rs' :=
  Covers.of_sub fun r hr => by
    obtain ⟨R, hR, o, hb, hl⟩ := h r hr
    exact ⟨R, hR, o, hb, hl⟩

/-! ## The layout -/

/-- The stack pointer on entry, the stack the contract gives, the number of
arguments, the arguments, the size of `scratch`, the offset `E` of the 1 KiB
`X` in it, and the permissions on entry. -/
structure Lay where
  SP : BitVec 32
  N : Nat
  nA : Nat
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
  argv : List (BitVec 32)
  rd : List Region
  wr : List Region

namespace Lay

variable (L : Lay)

/-- `esp` in the leaf's body. -/
abbrev E1 : BitVec 32 := L.SP - BitVec.ofNat 32 16
/-- The stack the calls use, below the leaf's frame. -/
abbrev STK : Region := below L.E1 (L.N - 16)
/-- The arguments. -/
abbrev ARGS : Region := ⟨(L.SP + BitVec.ofNat 32 4).setWidth 64, 4 * L.nA⟩
/-- `scratch`. -/
abbrev SC : Region := ⟨L.scr.setWidth 64, L.scrLen⟩
/-- The 1 KiB, as a register holds it and as an address. -/
abbrev X32 : BitVec 32 := L.scr + BitVec.ofNat 32 L.E
abbrev X : Addr := L.X32.setWidth 64
abbrev W : Region := ⟨L.X, 904⟩
abbrev ST : Addr := L.X
abbrev KS : Addr := L.X + BitVec.ofNat 64 200
abbrev MU : Addr := L.X + BitVec.ofNat 64 840
abbrev KEY : Region := ⟨L.key.setWidth 64, L.keyLen⟩
abbrev MSG : Region := ⟨L.msg.setWidth 64, L.len.toNat⟩
abbrev CTX : Region := ⟨L.ctx.setWidth 64, L.ctxLen.toNat⟩

/-- What the contract says of where everything is. -/
structure Ok : Prop where
  ctxLt : L.ctxLen.toNat < 256
  hE : L.E + 1024 ≤ L.scrLen
  hKey : 128 ≤ L.keyLen ∧ L.keyLen < 2 ^ 16
  hN : 56 ≤ L.N
  nSP : L.N ≤ L.SP.toNat
  fArgs : L.SP.toNat + 4 + 4 * L.nA ≤ 2 ^ 32
  nScr : L.scr.toNat + L.scrLen ≤ 2 ^ 32
  inSC : L.SC ∈ L.wr
  inKey : L.KEY ∈ L.rd
  inMsg : L.MSG ∈ L.rd
  inCtx : L.CTX ∈ L.rd
  xKey : L.SC.Disjoint L.KEY
  xMsg : L.SC.Disjoint L.MSG
  xCtx : L.SC.Disjoint L.CTX
  kAll : ∀ r ∈ [L.SC, L.KEY, L.MSG, L.CTX, L.ARGS], (below L.SP L.N).Disjoint r
  rAll : ∀ r ∈ [L.SC, L.ARGS], (⟨L.SP.setWidth 64, 4⟩ : Region).Disjoint r
  aSC : L.ARGS.Disjoint L.SC
  inArgs : L.ARGS ∈ L.wr
  argvLen : L.argv.length = L.nA
  nA8 : L.nA ≤ 8
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
theorem x_eq (h : L.Ok) : L.X = L.scr.setWidth 64 + BitVec.ofNat 64 L.E :=
  Proof.MlKem.X86.ea_off (by have := h.nScr; have := h.hE; omega)

/-- An address in the 1 KiB, as an instruction computes it from `esi`. -/
theorem xo (h : L.Ok) {o : Nat} (ho : o < 1024) : addr L.X32 o = L.X + BitVec.ofNat 64 o :=
  Proof.MlKem.X86.ea_off (by have := h.x32_lt; omega)

theorem x32_toNat (h : L.Ok) {o : Nat} (ho : o < 1024) : (L.X32 + BitVec.ofNat 32 o).toNat = L.X32.toNat + o := by
  have := h.x32_lt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem xs_sc (h : L.Ok) : Within ⟨L.X, 1024⟩ L.SC := ⟨L.E, h.x_eq, h.hE⟩

theorem sub_sc (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) : Region.Sub ⟨L.X + BitVec.ofNat 64 e, k⟩ L.SC :=
  (Within.trans (within_off L.X h₂) h.xs_sc).sub

/-- The calls' stack lies in the contract's. -/
theorem stk_sub (h : L.Ok) : Region.Sub L.STK (below L.SP L.N) := by
  have := h.nSP; have := h.hN
  rw [Lay.STK, Lay.E1]
  exact below_inner (by omega) (by omega)

/-- The leaf's frame lies in the contract's stack. -/
theorem fr_sub (h : L.Ok) : Region.Sub (below L.SP 16) (below L.SP L.N) := by
  have := h.nSP; have := h.hN
  exact below_sub (by omega) (by omega)

theorem kSC (h : L.Ok) : L.STK.Disjoint L.SC := (h.kAll _ (by simp)).sub_left h.stk_sub
theorem kKey (h : L.Ok) : L.STK.Disjoint L.KEY := (h.kAll _ (by simp)).sub_left h.stk_sub
theorem kMsg (h : L.Ok) : L.STK.Disjoint L.MSG := (h.kAll _ (by simp)).sub_left h.stk_sub
theorem kCtx (h : L.Ok) : L.STK.Disjoint L.CTX := (h.kAll _ (by simp)).sub_left h.stk_sub
theorem kArgs (h : L.Ok) : L.STK.Disjoint L.ARGS := (h.kAll _ (by simp)).sub_left h.stk_sub

theorem stk_x (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    Region.Disjoint L.STK ⟨L.X + BitVec.ofNat 64 e, k⟩ :=
  h.kSC.sub_right (h.sub_sc h₂)

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

/-- What lies within the first 904 bytes of `X`, or in `STK`, is apart from the two bytes. -/
theorem hdr_disj (h : L.Ok) {r : Region} (hr : Within r L.W ∨ Region.Sub r L.STK) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 944, 2⟩ r := by
  rcases hr with hr | hr
  · obtain ⟨o, hb, hl⟩ := hr
    obtain ⟨b, k⟩ := r
    simp only at hb hl
    subst hb
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact (h.kSC.symm.sub_left (h.sub_sc (by omega))).sub_right hr

/-- Argument `i`, as an instruction in the body addresses it. -/
theorem argAt_eq (L : Lay) (i : Nat) :
    addr L.E1 (20 + 4 * i) = (L.SP + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 := by
  simp only [addr, Lay.E1]
  congr 1
  rw [show (20 + 4 * i : Nat) = 16 + (4 + 4 * i) by omega, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
    BitVec.sub_add_cancel]

/-- Argument `i` lies in the arguments. -/
theorem argIn (h : L.Ok) {i : Nat} (hi : i < L.nA) :
    L.ARGS.Contains ((L.SP + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) 4 := by
  have := h.fArgs
  rw [Lay.ARGS, Proof.MlKem.X86.ea_off (x := L.SP) (d := 4) (by omega),
    Proof.MlKem.X86.ea_off (x := L.SP) (d := 4 + 4 * i) (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

end Lay.Ok

/-! ## In the leaf's body -/

/-- The state in the leaf's body, from the entry's stores to the end: `m₁`
is the memory after the frame's push. -/
structure Ctx (L : Lay) (m₁ : Mem) (t : State) : Prop where
  rd : t.rd = L.rd
  wr : t.wr = below L.SP 16 :: L.wr
  esp : t.gpr .esp = L.E1
  esi : t.gpr .esi = L.X32
  hdr : bytesAt t.mem (L.X + BitVec.ofNat 64 944) 2 = [0, BitVec.ofNat 8 L.ctxLen.toNat]
  args : ∀ i < L.nA, t.mem.readW ((L.SP + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) 32 = L.argv.getD i 0
  frame : Frame [L.SC, L.STK] m₁ t.mem

namespace Ctx

variable {L : Lay} {m₁ : Mem} {t t' : State}

/-- Code that writes only registers but `esp` and `esi`. -/
theorem regs (hc : Ctx L m₁ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hsp : t'.gpr .esp = t.gpr .esp) (hsi : t'.gpr .esi = t.gpr .esi) : Ctx L m₁ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.esp, hsi.trans hc.esi, by rw [hm]; exact hc.hdr,
    fun i hi => by rw [hm]; exact hc.args i hi, by rw [hm]; exact hc.frame⟩

/-- Code that writes memory only within the first 904 bytes of `X` and in `STK`. -/
theorem keep (hc : Ctx L m₁ t) (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .esp = t.gpr .esp) (hsi : t'.gpr .esi = t.gpr .esi) {rs : List Region}
    (hf : Frame rs t.mem t'.mem) (hrs : ∀ r ∈ rs, Within r L.W ∨ Region.Sub r L.STK) : Ctx L m₁ t' := by
  have khdr : bytesAt t'.mem (L.X + BitVec.ofNat 64 944) 2 = bytesAt t.mem (L.X + BitVec.ofNat 64 944) 2 :=
    Proof.MlKem.bytesAt_congr fun i hi =>
      hf.bytes (R := ⟨_, 2⟩) (fun r hr => hL.hdr_disj (hrs r hr)) (by show 2 ≤ 2 ^ 64; decide) hi
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.esp, hsi.trans hc.esi, khdr.trans hc.hdr,
    fun i hi => ?_, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · rw [hf.readW (hL.argIn hi) (fun r hr => ?_) (by decide)]
    · exact hc.args i hi
    · rcases hrs r hr with h | h
      · exact hL.aSC.sub_right ((h.trans ((within_base L.X (by decide : 904 ≤ 1024)).trans hL.xs_sc)).sub)
      · exact hL.kArgs.symm.sub_right h
  rcases hrs r hr with h | h
  · exact ⟨L.SC, by simp, (h.trans ((within_base L.X (by decide : 904 ≤ 1024)).trans hL.xs_sc)).sub⟩
  · exact ⟨L.STK, by simp, h⟩

/-- Bytes apart from `scratch` and `STK`, as after the push. -/
theorem bytesAt_eq (hc : Ctx L m₁ t) {p : Addr} {n : Nat} (hx : L.SC.Disjoint ⟨p, n⟩)
    (hk : L.STK.Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) : bytesAt t.mem p n = bytesAt m₁ p n :=
  Proof.MlKem.bytesAt_congr fun _ hi => Frame.bytes (R := ⟨p, n⟩) hc.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hx.symm
    · exact hk.symm) hn hi

/-- Bytes of `X` are readable. -/
theorem inX (hc : Ctx L m₁ t) (hL : L.Ok) {e k : Nat} (h₂ : e + k ≤ 1024) :
    InRegions (t.rd ++ t.wr) (L.X + BitVec.ofNat 64 e) k := by
  obtain ⟨R, hR, hc'⟩ := hL.inW h₂
  exact ⟨R, by rw [hc.rd, hc.wr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hR), hc'⟩

end Ctx

end VG.Proof.MlDsa.X86.Message
