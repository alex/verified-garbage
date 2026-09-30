import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Blake2.X86_64.Contract
import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Impl.Blake2.X86_64.Stream
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Streaming BLAKE2 on x86-64: common lemmas

Untrusted: everything here is checked by Lean. The contracts the proofs of
`init`, `update` and `finalize` are written against, what they need of the
compression function they call (`CalleeOk`), the call (`compressWith_ok`),
and the loops copying bytes into the buffer and zeroing it.
-/

namespace VG.Proof.Blake2

open VG.X86_64 VG.Spec.Blake2

section
variable {w : Nat} (P : Params w)

/-- x86-64 contract for `init(state = rdi, outlen = rsi, key = rdx, keylen =
rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, bufOff w + blockBytes w⟩
    let key : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [state] ∧ key.Disjoint state ∧ ret.Disjoint state ∧
    1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ P.maxBytes ∧ (s.gpr .rcx).toNat ≤ P.maxBytes
  post s s' := Spec.Blake2.Repr P (Spec.Blake2.init P (s.gpr .rsi).toNat (s.gpr .rcx).toNat) s'.mem
    (s.gpr .rdi) (keyBlock w (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx

/-- x86-64 contract for `update(state = rdi, count = rsi, data = rdx, len =
rcx, scratch = r8)`. -/
def updateX86_64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, bufOff w + blockBytes w⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 576⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ h0 d, Spec.Blake2.Repr P h0 s.mem (s.gpr .rdi) d →
    s.gpr .rsi = BitVec.ofNat 64 d.length → d.length + (s.gpr .rcx).toNat < 2 ^ 64 →
    Spec.Blake2.Repr P h0 s'.mem (s.gpr .rdi) (d ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- x86-64 contract for `finalize(state = rdi, count = rsi, out = rdx, scratch =
rcx)`. -/
def finalizeX86_64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, bufOff w + blockBytes w⟩
    let out : Region := ⟨s.gpr .rdx, bufOff w⟩
    let scratch : Region := ⟨s.gpr .rcx, 576⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ h0 d, Spec.Blake2.Repr P h0 s.mem (s.gpr .rdi) d → d.length < 2 ^ 64 →
    s.gpr .rsi = BitVec.ofNat 64 d.length → bytesAt s'.mem (s.gpr .rdx) (bufOff w) = finalHash P h0 d
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end

namespace X86_64.Stream

open VG.Impl.Blake2.X86_64.Stream
open VG.Impl.Blake2.X86_64 (at_ compress)
open VG.Proof.MdStream.X86_64 (Upd ofInt_natCast toNat_ofNat_lt callEntry_byte wp_mov wp_movm wp_store
  wp_addi wp_subi wp_sub wp_add wp_cmp wp_test wp_movzx8 wp_store8 wp_mov32i wp_andi)

variable {w : Nat} {P : Params w}

/-- The word sizes. -/
structure Ok (P : Params w) : Prop where
  /-- A key fits in a block. -/
  max : P.maxBytes ≤ blockBytes w
  w : w = 64 ∨ w = 32

theorem Ok.bb (h : Ok P) : blockBytes w = 64 ∨ blockBytes w = 128 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.N (h : Ok P) : bufOff w = blockBytes w / 2 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.pos (h : Ok P) : 0 < blockBytes w := by rcases h.bb with h | h <;> omega

theorem N_eq : Impl.Blake2.X86_64.Stream.N w = bufOff w := rfl
theorem B_eq : Impl.Blake2.X86_64.Stream.B w = blockBytes w := rfl

/-- What the calls need of the compression function: its contract, and that it
does not touch `rsp` or the stack and keeps `rdi` and `r9`. -/
structure CalleeOk (P : Params w) (code : Prog isa) : Prop where
  verified : ∀ s, (compressX86_64 P).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressX86_64 P).post s s'
  nosp : NoSp code
  depth : code.depth = 0
  keeps_rdi : ∀ i ∈ instrs code, Taint.clobbers i .rdi = false
  keeps_r9 : ∀ i ∈ instrs code, Taint.clobbers i .r9 = false

/-- The facts about the instructions of `code`, from one kernel check. -/
theorem CalleeOk.of_verified {code : Prog isa}
    (hv : ∀ s, (compressX86_64 P).pre s →
      ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressX86_64 P).post s s')
    (hk : ((instrs code).all fun i => !Taint.clobbers i .rdi && !Taint.clobbers i .r9 &&
      !Taint.clobbers i .rsp) = true)
    (hd : code.depth = 0) : CalleeOk P code := by
  have h := fun i hi => List.all_eq_true.mp hk i hi
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨hv, fun i hi => (h i hi).2, hd, fun i hi => (h i hi).1.1, fun i hi => (h i hi).1.2⟩

/-- What the call of the compression function needs of the state `s` before
the argument set-up: the hash value `st` at `rbx`, the scratch space `scr` at
`r15` and the `len` bytes of blocks at `src` do not overlap each other or the
return address, and may be accessed. -/
structure CallOk (s : State) (st scr src : Addr) (len : Nat) : Prop where
  rbx : s.gpr .rbx = st
  r15 : s.gpr .r15 = scr
  d₁ : Region.Disjoint ⟨st, bufOff w⟩ ⟨scr, 512⟩
  d₂ : Region.Disjoint ⟨src, len⟩ ⟨st, bufOff w⟩
  d₃ : Region.Disjoint ⟨src, len⟩ ⟨scr, 512⟩
  d₄ : (below (s.gpr .rsp) 8).Disjoint ⟨st, bufOff w⟩
  d₅ : (below (s.gpr .rsp) 8).Disjoint ⟨scr, 512⟩
  d₆ : (below (s.gpr .rsp) 8).Disjoint ⟨src, len⟩
  hc : Covers [⟨src, len⟩, ⟨st, bufOff w⟩, ⟨scr, 512⟩] (s.rd ++ s.wr)
  hw : Covers [⟨st, bufOff w⟩, ⟨scr, 512⟩] s.wr
  hN : bufOff w ≤ 2 ^ 64
  hlen : len ≤ 2 ^ 64

/-- The arguments of the call, set up from `σ`. -/
structure Setup (σ s : State) (src n t : BitVec 64) (last : Bool) : Prop where
  rdi : s.gpr .rdi = σ.gpr .rbx
  rsi : s.gpr .rsi = src
  rdx : s.gpr .rdx = n
  rcx : s.gpr .rcx = t
  r8 : ((s.gpr .r8).setWidth 32 != 0) = last
  r9 : s.gpr .r9 = σ.gpr .r15
  cs : ∀ r ∈ calleeSaved, s.gpr r = σ.gpr r
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  mem : s.mem = σ.mem

/-- The call's precondition, narrowed to the regions it is given. -/
theorem call_hyps {σ s : State} {st scr src : Addr} {n t : BitVec 64} {last : Bool}
    (h : CallOk (w := w) σ st scr src (blockBytes w * n.toNat)) (hs : Setup σ s src n t last) :
    (compressX86_64 P).pre (s.callEntry.withRegions [⟨src, blockBytes w * n.toNat⟩]
      [⟨st, bufOff w⟩, ⟨scr, 512⟩]) ∧
    Covers ([⟨src, blockBytes w * n.toNat⟩] ++ [⟨st, bufOff w⟩, ⟨scr, 512⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨st, bufOff w⟩, ⟨scr, 512⟩] s.wr := by
  have hsp : s.gpr .rsp = σ.gpr .rsp := hs.cs _ (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  refine ⟨?_, ?_, ?_⟩
  · simp only [compressX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp),
      hne _ (by decide : Reg.r9 ≠ .rsp), hs.rdi, hs.rdx, hs.r9, hs.rsi, h.rbx, h.r15, hsp]
    exact ⟨trivial, trivial, h.d₁, by simpa using h.d₂, by simpa using h.d₃, h.d₄, h.d₅⟩
  · rw [hs.rd, hs.wr]; simpa using h.hc
  · rw [hs.wr]; exact h.hw

/-- Compressing the `n` blocks at `src` into the hash value at `rbx`, with
scratch space at `r15`, by calling the compression function, after `args`
set up its arguments. -/
theorem compressWith_ok {args : List Instr} (hf : CalleeOk P (compress P)) {s : State}
    {st scr src : Addr} {n t : BitVec 64} {last : Bool}
    (hs : WP isa (.block (([.mov .rdi (.reg .rbx)] : List Instr) ++ args ++ ([.mov .r9 (.reg .r15)] : List Instr))) s
      fun s' => Setup s s' src n t last)
    (h : CallOk (w := w) s st scr src (blockBytes w * n.toNat))
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, bufOff w⟩, ⟨scr, 512⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      stateAt w s'.mem st = compressBlocks P (stateAt w s.mem st) s.mem src n.toNat t.toNat last →
      Q s') :
    WP isa (compressWith P args) s Q := by
  unfold compressWith
  refine WP.seq (WP.mono hs fun s₁ hs => ?_)
  have e₁ : s₁.gpr .rdi = st := hs.rdi.trans h.rbx
  have e₃ : s₁.gpr .r9 = scr := hs.r9.trans h.r15
  have hsp : s₁.gpr .rsp = s.gpr .rsp := hs.cs _ (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  obtain ⟨hpre, hc, hw⟩ := call_hyps (P := P) h hs
  refine WP.seq (WP.call (k := compressX86_64 P) hf.verified hf.nosp (by rw [hf.depth]; decide)
    (rd := [⟨src, blockBytes w * n.toNat⟩]) (wr := [⟨st, bufOff w⟩, ⟨scr, 512⟩]) hpre hc hw ?_)
  intro s₂ hrd hwr hcs hfr hkeep ⟨s₃, hm₃, _, hpost⟩
  have k₁ := hkeep .rdi hf.keeps_rdi
  have k₃ := hkeep .r9 hf.keeps_r9
  simp only [compressX86_64, State.withRegions_gpr, State.withRegions_mem,
    hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
    hne _ (by decide : Reg.rdx ≠ .rsp), hne _ (by decide : Reg.rcx ≠ .rsp),
    hne _ (by decide : Reg.r8 ≠ .rsp), e₁, hs.rsi, hs.rdx, hs.rcx, hs.r8, hm₃] at hpost
  have hst : stateAt w s₁.callEntry.mem st = stateAt w s.mem st :=
    (stateAt_congr fun i hi => callEntry_byte s₁ (R := ⟨st, bufOff w⟩) (by rw [hsp]; exact h.d₄)
      h.hN hi).trans (by rw [hs.mem])
  have hblk : compressBlocks P (stateAt w s.mem st) s₁.callEntry.mem src n.toNat t.toNat last =
      compressBlocks P (stateAt w s.mem st) s.mem src n.toNat t.toNat last :=
    compressBlocks_congr P fun j hj => by
      rw [callEntry_byte s₁ (R := ⟨src, blockBytes w * n.toNat⟩) (by rw [hsp]; exact h.d₆) h.hlen hj,
        hs.mem]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, isa, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine hQ _ (hrd.trans hs.rd) (hwr.trans hs.wr) (fun r hr => ?_) (by
    rw [hf.depth, hsp, hs.mem] at hfr; simpa [State.setReg] using hfr)
    (by simp only [State.setReg]; rw [hpost, hst, hblk])
  have h₂ := hcs r hr
  simp only [State.setReg]
  by_cases h15 : r = .r15
  · subst h15; simp [k₃, e₃, h.r15]
  · by_cases hbx : r = .rbx
    · subst hbx; simp [k₁, e₁, h.rbx]
    · simp [h15, hbx, h₂, hs.cs r hr]

/-! ## Copying bytes into the buffer -/

open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_frame writeBytes_nil)
open VG.Proof.MdStream.X86_64 (sx1 ofNat_succ ofNat_pred ofNat_beq_zero)

theorem contains_prefix (q : Addr) {j k : Nat} (h : j ≤ k) : (⟨q, k⟩ : Region).Contains q j := by
  simp [Region.Contains, h]

/-- The copy loop's state after `j` of `k` bytes, from `s₀`. -/
structure CopyI (s₀ : State) (dst src : Addr) (r k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  rbp : s.gpr .rbp = src + BitVec.ofNat 64 j
  r13 : s.gpr .r13 = BitVec.ofNat 64 (r + j)
  rax : s.gpr .rax = BitVec.ofNat 64 (k - j)
  other : ∀ x, x ≠ .r9 → x ≠ .rax → x ≠ .rbp → x ≠ .r13 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)

/-- The loop copying `k ≥ 1` bytes from `src` (at `rbp`) to the buffer, from
byte `r` on (in `r13`). -/
theorem copyLoop_ok {s₀ : State} {st src : Addr} {r k : Nat} (hk : 1 ≤ k) (hk' : r + k < 2 ^ 32)
    (hrbx : s₀.gpr .rbx = st) (hrbp : s₀.gpr .rbp = src) (hr13 : s₀.gpr .r13 = BitVec.ofNat 64 r)
    (hrax : s₀.gpr .rax = BitVec.ofNat 64 k)
    (hsrc : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (src + BitVec.ofNat 64 i) 1)
    (hdst : ∀ i < k, InRegions s₀.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨src, k⟩ ⟨st + BitVec.ofNat 64 (bufOff w + r), k⟩)
    {Q : State → Prop}
    (hQ : ∀ s, CopyI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) src r k k s → Q s) :
    WP isa (copyLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      CopyI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) src r k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by simp [hrbp],
      by rw [hr13, Nat.add_zero], by rw [hrax, Nat.sub_zero], fun _ _ _ _ _ => rfl, rfl, rfl,
      by rw [List.take_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hxs : (bytesAt s₀.mem src k).length = k := by simp [bytesAt]
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr]; exact hsrc j hj
  have hbyte : s.mem (src + BitVec.ofNat 64 j) = s₀.mem (src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (writeBytes_frame s₀.mem _ _ (contains_prefix (k := k) _ (by simp; omega))).bytes (R := ⟨src, k⟩)
      (by simpa using hd) (by show k ≤ 2 ^ 64; omega) hj
  -- The byte written.
  have hout : InRegions s.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j) 1 := by
    rw [h.wr]; exact hdst j hj
  have hrbx' : s.gpr .rbx = st := by rw [h.other .rbx (by decide) (by decide) (by decide) (by decide), hrbx]
  refine wp_movzx8 (d := .r9) (a := src + BitVec.ofNat 64 j) (by simp [State.ea, h.rbp]) hin
    fun s₁ u₁ => ?_
  refine wp_store8 (r := .r9) (a := st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j) ?_
    (by rw [u₁.wr]; exact hout) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  · simp only [State.ea, bufByte, u₁.other .rbx (by decide), u₁.other .r13 (by decide), hrbx', h.r13,
      N_eq, BitVec.ofNat_add, BitVec.mul_one, ofInt_natCast]
    ac_rfl
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ hz₅ => WP.block_nil ?_
  have g : ∀ x, x ≠ .rax → x ≠ .r13 → x ≠ .rbp → x ≠ .r9 → s₅.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [u₅.other x h1, u₄.other x h2, u₃.other x h3, g₂, u₁.other x h4]
  have hrax' : s₅.gpr .rax = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [u₅.gpr, u₄.other .rax (by decide), u₃.other .rax (by decide), g₂, u₁.other .rax (by decide), h.rax,
      sx1, ofNat_pred (by omega), Nat.sub_sub]
  have hI : CopyI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) src r k (j + 1) s₅ := by
    refine ⟨by omega, ?_, ?_, hrax', fun x h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
    · rw [u₅.other .rbp (by decide), u₄.other .rbp (by decide), u₃.gpr, g₂, u₁.other .rbp (by decide), h.rbp,
        sx1, ofNat_succ, BitVec.add_assoc]
    · rw [u₅.other .r13 (by decide), u₄.gpr, u₃.other .r13 (by decide), g₂, u₁.other .r13 (by decide), h.r13,
        sx1, ← Nat.add_assoc, ofNat_succ]
    · rw [g x h2 h4 h3 h1, h.other x h1 h2 h3 h4]
    · rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, h.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, h.wr]
    · have hj' : j < (bytesAt s₀.mem src k).length := by omega
      have hlen : (List.take j (bytesAt s₀.mem src k)).length < 2 ^ 64 := by
        simp only [List.length_take]; omega
      rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem, u₁.gpr, hbyte, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some, writeBytes_snoc _ _ _ _ hlen]
      have hl : (List.take j (bytesAt s₀.mem src k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [hl, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
      congr 1
      simp [bytesAt]
  have hzf : s₅.zf = some (decide (k - (j + 1) = 0)) := by
    rw [hz₅, u₄.other .rax (by decide), u₃.other .rax (by decide), g₂, u₁.other .rax (by decide),
      h.rax, sx1, ofNat_pred (show 1 ≤ k - j by omega), ofNat_beq_zero (by omega),
      show k - j - 1 = k - (j + 1) by omega]
  by_cases hjk : j + 1 = k
  · refine .inl ⟨?_, hQ _ (hjk ▸ hI)⟩
    simp only [eval, hzf, show k - (j + 1) = 0 by omega, decide_true, Option.map_some,
      Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩
    simp only [eval, hzf, show k - (j + 1) ≠ 0 by omega, decide_false, Option.map_some,
      Bool.not_false]

end X86_64.Stream

end VG.Proof.Blake2
