import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# `vg_rsa_public` on x86-64: correctness

`code`, from a state its contract allows, writes `publicOp` of its inputs
(`code_correct`), against `pubContract`, which states the shared contract's
precondition on the registers and the stack.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-! ## Regions -/

theorem contains_scr {B a : Addr} {Z : Nat} (h : ofs B a < Z) : (⟨B, Z⟩ : Region).Contains a 1 := by
  simp only [Region.Contains, ofs] at *; omega

/-- A byte of a region disjoint from the working space is outside it. -/
theorem out_scr {B : Addr} {Z : Nat} {r : Region} (hd : r.Disjoint ⟨B, Z⟩) {a : Addr} (ha : r.Contains a 1) :
    Z ≤ ofs B a := by
  rcases Nat.lt_or_ge (ofs B a) Z with h | h
  · exact absurd (contains_scr h) (hd a ha)
  · exact h

theorem contains_byte (p : Addr) {i len : Nat} (hi : i < len) (hlen : len ≤ 2 ^ 64) :
    (⟨p, len⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 :=
  Offset.contains_base p (by omega) (by omega)

/-- A buffer disjoint from the working space, as a byte string. -/
theorem src_of_region {s : State} {B : Addr} {Z : Nat} {p : Addr} {len : Nat}
    (hr : (⟨p, len⟩ : Region) ∈ s.rd ++ s.wr) (hlen : len ≤ 2 ^ 64)
    (hd : (⟨p, len⟩ : Region).Disjoint ⟨B, Z⟩) : Src s B Z p (Spec.Rsa.bytesAt s.mem p len) := by
  have hl : (Spec.Rsa.bytesAt s.mem p len).length = len := by simp [Spec.Rsa.bytesAt]
  refine ⟨fun i hi => ⟨_, hr, contains_byte p (by omega) hlen⟩, fun i hi => ?_,
    fun i hi => out_scr hd (contains_byte p (by omega) hlen)⟩
  simp [Spec.Rsa.bytesAt]

/-! ## The contract on the registers and the stack -/

/-- `vg_rsa_public(out = rdi, out_len = rsi, n = rdx, n_len = rcx, e = r8,
e_len = r9, input = [rsp + 8], input_len = [rsp + 16], scratch = [rsp + 24],
scratch_len = [rsp + 32])`. -/
def pubContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let inp : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let scr : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 32⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64 ∧
      s.rd = [n, e, inp, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint inp ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .rcx).toNat ∧
      (stackArg s 1).toNat = (s.gpr .rcx).toNat ∧ 1 ≤ (s.gpr .r9).toNat ∧
      (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat ∧ Spec.Rsa.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 3).toNat
  post s s' :=
    Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.Rsa.publicOp (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      stackArg s₁ 3 = stackArg s₂ 3 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat

/-! ## Correctness -/

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem i2osp_zero' (k : Nat) : Spec.Rsa.i2osp 0 k = List.replicate k 0 := by
  rw [i2osp_zero]; simp

theorem setWidth_flag (c : Bool) : (BitVec.ofNat 64 c.toNat).setWidth 32 = if c then 1 else 0 := by
  cases c <;> rfl

/-- What `code` leaves: the result `r` and flag `c` of `fail` or `main`. -/
theorem written_of {m : Mem} {out : Addr} {k : Nat} {rax : BitVec 64} {nb eb xb : List Byte}
    (hnl : nb.length = k) {r : Nat} {c : Bool}
    (hb : Spec.Rsa.bytesAt m out k = Spec.Rsa.i2osp r k) (hr : rax = BitVec.ofNat 64 c.toNat)
    (hc : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true →
      c = decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb) ∧
      r = if Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb then
        Spec.Rsa.os2ip xb ^ Spec.Rsa.os2ip eb % Spec.Rsa.os2ip nb else 0)
    (hf : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = false → c = false ∧ r = 0) :
    Spec.Rsa.written m out k (rax.setWidth 32) (Spec.Rsa.publicOp nb eb xb) := by
  unfold Spec.Rsa.publicOp
  rw [hnl, hr, setWidth_flag]
  cases hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k
  · obtain ⟨rfl, rfl⟩ := hf hv
    simp only [hv, Bool.false_eq_true, ite_false, Spec.Rsa.written]
    exact ⟨trivial, by rw [hb, i2osp_zero']⟩
  · obtain ⟨rfl, rfl⟩ := hc hv
    by_cases hx : Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb
    · simp only [hv, hx, ite_true, decide_true, Spec.Rsa.encrypt, Option.map_some, Spec.Rsa.written]
      simp only [hx, ite_true] at hb
      exact ⟨trivial, by rw [hb, VG.Proof.Bignum.powMod_eq]⟩
    · simp only [hv, hx, ite_true, ite_false, decide_false, Spec.Rsa.encrypt, Option.map_none,
        Spec.Rsa.written, Bool.false_eq_true]
      simp only [hx, ite_false] at hb
      exact ⟨trivial, by rw [hb, i2osp_zero']⟩

theorem bytesAt_eq (m : Mem) (p : Addr) (k : Nat) :
    Spec.Rsa.bytesAt m p k = (List.range k).map fun i => m (p + BitVec.ofNat 64 i) := rfl

theorem stackArgAddr_two (s : State) : stackArgAddr s 2 = stackArgAddr s 0 + BitVec.ofNat 64 16 := by
  simp only [stackArgAddr]; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- What `code` uses of its contract's precondition, for the working space
`B` (the third stack argument) of `Z` bytes and `m`'s length `k`. -/
structure CodeCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .rcx).toNat
  hk2 : (s.gpr .rcx).toNat ≤ 1024
  hL1 : 1 ≤ (s.gpr .r9).toNat
  hL2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  hZ : 128 * (s.gpr .rcx).toNat ≤ (stackArg s 3).toNat * 8
  hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8)
  ha0 : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8
  ha2 : InRegions (s.rd ++ s.wr) (stackArgAddr s 2) 8
  hsep : ∀ m', Outside (stackArg s 2) 0 (8 * 22) s.mem m' → m'.readW (stackArgAddr s 0) 64 = stackArg s 0
  hnb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rdx)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  heb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .r8)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
  hxb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (stackArg s 0)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
  hout : ∀ j < (s.gpr .rcx).toNat, InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1
  houts : ∀ j < (s.gpr .rcx).toNat, (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) (s.gpr .rdi + BitVec.ofNat 64 j)
  hret : ∀ b < 8, (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    ∀ j < (s.gpr .rcx).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j

theorem codeCtx_of {s : State} (h : pubContract.pre s) : CodeCtx s := by
  simp only [pubContract] at h
  obtain ⟨hsp, hrd, hwr, dOn, dOe, dOi, dOs, dOa, dns, des, dis, dsa, dRo, dRn, dRe, dRi, dRs, dRa,
    wO, wN, wE, wI, wS, hk, hol, hil, hL1, hL2, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8) := ⟨by rw [hwr]; simp, wS⟩
  have hn := hs.nowrap
  refine ⟨hk1, hk2, hL1, hL2, by omega, hs,
    ⟨⟨stackArgAddr s 0, 32⟩, by rw [hrd]; simp, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩,
    ⟨⟨stackArgAddr s 0, 32⟩, by rw [hrd]; simp,
      by rw [stackArgAddr_two]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := b) (by omega) (by omega)); omega)),
    src_of_region (by rw [hrd]; simp) (by omega) dns, src_of_region (by rw [hrd]; simp) (by omega) des,
    src_of_region (by rw [hrd, ← hil]; simp) (by omega) (by rw [← hil]; exact dis),
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self .., contains_byte _ (by omega) (by omega)⟩,
    fun j hj => out_scr dOs (contains_byte _ (by omega) (by omega)), fun b hb => ?_⟩
  have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega)
  exact ⟨out_scr dRs hc, fun j hj he => dRo _ hc (by rw [he]; exact contains_byte _ (by omega) (by omega))⟩

/-- After `entry` and the reloads of `m` and `k`, from `s`. -/
structure HeadPost (s t : State) : Prop where
  scr : Scr t (stackArg s 2) ((stackArg s 3).toNat * 8)
  rdi : t.gpr .rdi = stackArg s 2
  rdx : t.gpr .rdx = s.gpr .rdx
  rcx : t.gpr .rcx = BitVec.ofNat 64 (s.gpr .rcx).toNat
  saved : ∀ i < 6, word t.mem (stackArg s 2) (8 * i) = s.gpr (saved.getD i .rax)
  hO : word t.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi
  hN : word t.mem (stackArg s 2) (8 * sN) = s.gpr .rdx
  hK : word t.mem (stackArg s 2) (8 * sK) = BitVec.ofNat 64 (s.gpr .rcx).toNat
  hE : word t.mem (stackArg s 2) (8 * sE) = s.gpr .r8
  hL : word t.mem (stackArg s 2) (8 * sElen) = BitVec.ofNat 64 (s.gpr .r9).toNat
  hIn : word t.mem (stackArg s 2) (8 * sIn) = stackArg s 0
  inScr : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t.mem
  keep : Keep [.r11, .rax, .rdi, .rdx, .rcx] s t

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `entry`, and `m` and `k` into `rdx` and `rcx`. -/
theorem head_ok {s : State} (c : CodeCtx s) :
    WP isa (.block (entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr))) s (HeadPost s) := by
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.hk1
  have hw : ∀ i < 22, InRegions s.wr (off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok rfl hw c.ha0 c.ha2 c.hsep) fun t₀ ⟨hdi, h0, h1, h2, h3, h4, h5, hO, hN, hK, hE, hL,
    hIn, ho₀, k₀⟩ => ?_
  have hs₀ := c.hs.congr k₀.2.2
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = s.gpr .rdx ∧
      t.gpr .rcx = s.gpr .rcx ∧ t.mem = t₀.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hs₀.ld (d := 8 * sN) (by unfold sN sFn; omega),
      hs₀.ld (d := 8 * sK) (by unfold sK sFn; omega), hN, hK]) rfl) fun t₁ ⟨⟨hdx, hcx, hm⟩, k₁⟩ => ?_
  refine ⟨hs₀.congr k₁.2.2, (k₁.gpr (by decide)).trans hdi, hdx, by rw [hcx, ofNat_toNat64], fun i hi => ?_,
    by rw [hm]; exact hO, by rw [hm]; exact hN, by rw [hm, hK, ofNat_toNat64], by rw [hm]; exact hE,
    by rw [hm, hL, ofNat_toNat64], by rw [hm]; exact hIn, by rw [hm]; exact InScr.of_outside ho₀ (by omega),
    (k₀.trans k₁).mono (by decide)⟩
  rw [hm]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-- `main`'s hypotheses after the head and the modulus' check. -/
theorem mainPre_of {s t₁ t : State} (c : CodeCtx s) (h : HeadPost s t₁) (hm : t.mem = t₁.mem)
    (k : Keep [.rax, .rbp, .rsi] t₁ t) :
    MainPre t (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rcx).toNat (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8)
      (stackArg s 0) (s.gpr .r9).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) := by
  have kk := h.keep.trans k
  have hi : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t.mem := by rw [hm]; exact h.inScr
  have hZ := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hdi : t.gpr .rdi = stackArg s 2 := (k.gpr (by decide)).trans h.rdi
  have hz : slot (((s.gpr .rcx).toNat + 7) / 8) 8 ≤ (stackArg s 3).toNat * 8 := by unfold slot hdrBytes; omega
  exact
    { scr := h.scr.congr k.2.2, rdi := hdi, z := hz, k1 := hk1, k2 := hk2, hO := (by rw [hm]; exact h.hO),
      hN := (by rw [hm]; exact h.hN), hK := (by rw [hm]; exact h.hK), hE := (by rw [hm]; exact h.hE),
      hL := (by rw [hm]; exact h.hL), hIn := (by rw [hm]; exact h.hIn), n := c.hnb.congrK hi kk,
      x := c.hxb.congrK hi kk, e := c.heb.congrK hi kk, nl := bytesAt_length _ _ _, xl := bytesAt_length _ _ _,
      el := bytesAt_length _ _ _, L1 := c.hL1, L2 := c.hL2,
      out := (fun j hj => by rw [kk.2.2]; exact c.hout j hj), outSep := c.houts }

/-- What `code` leaves, from what `fail` or `main` leaves. -/
theorem code_fin {s t₁ t₂ t : State} (c : CodeCtx s) (h : HeadPost s t₁) (hm : t₂.mem = t₁.mem)
    (k : Keep [.rax, .rbp, .rsi] t₁ t₂) {r : Nat} {cb : Bool}
    (hp : MainPost t₂ t (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rcx).toNat (s.gpr .rdi) r cb)
    (hc : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true →
      cb = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) <
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)) ∧
      r = if Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) <
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) then
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) ^
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) %
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) else 0)
    (hf : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false → cb = false ∧ r = 0) :
    gprPreserved s t ∧ pubContract.post s t := by
  refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩,
    written_of (bytesAt_length _ _ _) hp.bytes hp.rax hc hf⟩
  · have kk := h.keep.trans k
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.saved 0 (by decide)).trans (by rw [hm]; exact h.saved 0 (by decide))
    · exact (hp.saved 1 (by decide)).trans (by rw [hm]; exact h.saved 1 (by decide))
    · exact (hp.keep.gpr (by decide)).trans (kk.gpr (by decide))
    · exact (hp.saved 2 (by decide)).trans (by rw [hm]; exact h.saved 2 (by decide))
    · exact (hp.saved 3 (by decide)).trans (by rw [hm]; exact h.saved 3 (by decide))
    · exact (hp.saved 4 (by decide)).trans (by rw [hm]; exact h.saved 4 (by decide))
    · exact (hp.saved 5 (by decide)).trans (by rw [hm]; exact h.saved 5 (by decide))
  · obtain ⟨hZx, hne⟩ := c.hret b hb
    rw [hp.frame _ hZx hne, hm, h.inScr _ hZx]

theorem code_correct (s : State) (h : pubContract.pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ pubContract.post s s' := by
  have c := codeCtx_of h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  suffices hwp : WP isa code s fun s' => gprPreserved s s' ∧ pubContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hg, hp⟩
  unfold code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (head_ok c) fun t₁ h₁ => ?_
  have hnb₁ := c.hnb.congrK h₁.inScr h₁.keep
  refine WP.mono (invalid_ok h₁.rdx h₁.rcx hk1 hk2 (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by
    rw [bytesAt_length]; exact hi)) (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
    (s.gpr .rcx).toNat) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = false := by simpa using hb
    have hpre := mainPre_of c h₁ hm₂ k₂
    exact WP.mono (fail_ok hpre.scr hpre.rdi (by have := hpre.z; unfold slot hdrBytes at this; omega)
      (by omega) (by omega) hpre.hO hpre.hK hpre.out hpre.outSep)
      fun t hp => code_fin c h₁ hm₂ k₂ hp (fun h => absurd h (by rw [hv]; decide)) fun _ => ⟨rfl, rfl⟩
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
        (s.gpr .rcx).toNat = true := by simpa using hb
    exact WP.mono (main_ok (mainPre_of c h₁ hm₂ k₂) hv) fun t hp => code_fin c h₁ hm₂ k₂ hp
      (fun _ => ⟨rfl, rfl⟩) fun h => absurd h (by rw [hv]; decide)

end VG.Proof.Bignum.X86_64
