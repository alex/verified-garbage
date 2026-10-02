import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# A Merkle–Damgård compression function on AArch64, called on one block

The contract of a compression function with blocks of any size `B` (`compK`,
which is that of the streaming proofs, `Proof/MdStream/AArch64/Common.lean`,
for any block size), what its callers need of an implementation (`CompOk`:
correct, constant time, without frames), and the call of it on one block
through the streaming code's `compressAt`, in one run (`compressAt_ok`) and in
two (`compressAt_rel`).
-/

namespace VG.Proof.Pbkdf2.AArch64

open VG VG.AArch64 VG.Proof.MdStream
open VG.Impl.MdStream.AArch64 (compressAt compressWith mov)
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_movz)

section
variable {B N L : Nat} (H : Md B N L) (so : Nat)

/-- The contract of the compression function: updates the `N`-byte hash
value at `x0` with the `x2` blocks of `B` bytes at `x1`, with scratch space
`x3` (`so` bytes). -/
def compK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, N⟩
    let blocks : Region := ⟨s.gpr .x1, B * (s.gpr .x2).toNat⟩
    let scratch : Region := ⟨s.gpr .x3, so⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    H.stateAt s'.mem (s.gpr .x0) =
      H.compressBlocks (H.stateAt s.mem (s.gpr .x0)) s.mem (s.gpr .x1) (s.gpr .x2).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- What a caller needs of an implementation of the compression function:
that it is correct and constant time, pushes no frames, and its checked
instructions do not write callee-saved SIMD registers. -/
structure CompOk (code : Prog isa) : Prop where
  verified : ∀ s, (compK H so).pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compK H so).post s s'
  ct : ConstantTime isa (compK H so).pre (compK H so).pub code
  noFrames : code.noFrames = true
  /-- Existing MD wrappers require untouched callee-saved SIMD registers. -/
  keepsV : code.allInstrs keepsV = true

end

section
variable {B N L : Nat} {H : Md B N L} {so : Nat}

/-- What the call of the compression function on the block at `x1`, into the
hash value at `x19`, with scratch space at `x20`, needs. -/
structure CallOk (s : State) (N B so : Nat) (st scr src : Addr) : Prop where
  x19 : s.gpr .x19 = st
  x20 : s.gpr .x20 = scr
  x1 : s.gpr .x1 = src
  st_scr : Region.Disjoint ⟨st, N⟩ ⟨scr, so⟩
  src_st : Region.Disjoint ⟨src, B⟩ ⟨st, N⟩
  src_scr : Region.Disjoint ⟨src, B⟩ ⟨scr, so⟩
  cov : Covers [⟨src, B⟩, ⟨st, N⟩, ⟨scr, so⟩] (s.rd ++ s.wr)
  covW : Covers [⟨st, N⟩, ⟨scr, so⟩] s.wr

theorem one_toNat : (BitVec.setWidth 64 (1 : BitVec 16)).toNat = 1 := rfl

/-- The state after the instructions that set up the call. -/
structure CSetup (s t : State) : Prop where
  x0 : t.gpr .x0 = s.gpr .x19
  x1 : t.gpr .x1 = s.gpr .x1
  x2 : t.gpr .x2 = BitVec.setWidth 64 (1 : BitVec 16)
  x3 : t.gpr .x3 = s.gpr .x20
  keep : ∀ r ∈ preserved, t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem csetup_ok (s : State) :
    WP isa (.block [mov .x0 .x19, .movz .x .x2 1 0, mov .x3 .x20]) s (CSetup s) := by
  refine wp_mov fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd],
    by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp]⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₃.other _ (by decide), u₂.gpr]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  · have : r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₃.other _ this.2.2, u₂.other _ this.2.1, u₁.other _ this.1]

theorem call_pre {s t : State} {st scr src : Addr} (h : CallOk s N B so st scr src) (hs : CSetup s t) :
    (compK H so).pre (t.callEntry.withRegions [⟨src, B * (t.callEntry.gpr .x2).toNat⟩] [⟨st, N⟩, ⟨scr, so⟩]) := by
  have c0 : t.callEntry.gpr .x0 = st := (State.callEntry_gpr _ (by decide)).trans (hs.x0.trans h.x19)
  have c1 : t.callEntry.gpr .x1 = src := (State.callEntry_gpr _ (by decide)).trans (hs.x1.trans h.x1)
  have c2 : t.callEntry.gpr .x2 = BitVec.setWidth 64 (1 : BitVec 16) :=
    (State.callEntry_gpr _ (by decide)).trans hs.x2
  have c3 : t.callEntry.gpr .x3 = scr := (State.callEntry_gpr _ (by decide)).trans (hs.x3.trans h.x20)
  simp only [compK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, c0, c1, c2, c3, one_toNat,
    Nat.mul_one]
  exact ⟨trivial, trivial, h.st_scr, h.src_st, h.src_scr⟩

theorem c2_eq (t : State) (hs : t.gpr .x2 = BitVec.setWidth 64 (1 : BitVec 16)) :
    B * (t.callEntry.gpr .x2).toNat = B := by
  rw [State.callEntry_gpr _ (by decide), hs, one_toNat, Nat.mul_one]

/-- Compressing the block at `x1` into the hash value at `x19`, with scratch
space at `x20`: the callee-saved registers other than `x30` are kept. -/
theorem compressAt_ok {name : String} {code : Prog isa} (hf : CompOk H so code) {s : State}
    {st scr src : Addr} (h : CallOk s N B so st scr src) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, N⟩, ⟨scr, so⟩] s.mem s'.mem →
      H.stateAt s'.mem st = H.compress (H.stateAt s.mem st) (H.blockAt s.mem src) → Q s') :
    WP isa (compressAt name code) s Q := by
  unfold compressAt compressWith
  refine WP.seq (WP.mono (csetup_ok s) fun t hs => ?_)
  have e := c2_eq (B := B) t hs.x2
  have hpre := call_pre (H := H) h hs
  rw [e] at hpre
  refine WP.call (k := compK H so) hf.verified hpre ?_ ?_ ?_ hf.noFrames
  · rw [hs.rd, hs.wr]; simpa using h.cov
  · rw [hs.wr]; exact h.covW
  · intro s' hrd hwr hsp hfr hcs _ hpost
    have c0 : t.callEntry.gpr .x0 = st := (State.callEntry_gpr _ (by decide)).trans (hs.x0.trans h.x19)
    have c1 : t.callEntry.gpr .x1 = src := (State.callEntry_gpr _ (by decide)).trans (hs.x1.trans h.x1)
    have c2 : (t.callEntry.gpr .x2).toNat = 1 := by
      rw [State.callEntry_gpr _ (by decide), hs.x2, one_toNat]
    simp only [compK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2,
      hs.mem] at hpost
    rw [hs.mem] at hfr
    refine hQ s' (hrd.trans hs.rd) (hwr.trans hs.wr) (fun r hr h30 => (hcs r hr h30).trans (hs.keep r hr))
      (hsp.trans hs.sp) hfr ?_
    rw [hpost, Md.compressBlocks_one]

/-- `compressAt` is constant time, in runs that call it on the same regions. -/
theorem compressAt_rel {name : String} {code : Prog isa} (hf : CompOk H so code) {st scr src : Addr}
    {P' : State → State → Prop}
    (hP : ∀ s₁ s₂, P' s₁ s₂ → CallOk s₁ N B so st scr src ∧ CallOk s₂ N B so st scr src ∧ s₁.sp = s₂.sp) :
    RelCT isa P' (compressAt name code) fun _ _ => True := by
  unfold compressAt compressWith
  have su := (RelCT.taint (A := taint) (P := P') (Taint.ofRegs [])
    (fun s₁ s₂ hp => ⟨(hP s₁ s₂ hp).2.2, fun r hr => by simp at hr⟩)
    (c := .block [mov .x0 .x19, .movz .x .x2 1 0, mov .x3 .x20]) (by taint_decide)).wpDep
      (F := CSetup) fun s₁ s₂ _ => ⟨csetup_ok s₁, csetup_ok s₂⟩
  refine su.seq (RelCT.call (k := compK H so) hf.verified hf.ct [⟨src, B⟩] [⟨st, N⟩, ⟨scr, so⟩]
    fun t₁ t₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => ?_)
  obtain ⟨c₁, c₂, hsp⟩ := hP σ₁ σ₂ hp
  have p₁ := call_pre (H := H) c₁ h₁
  have p₂ := call_pre (H := H) c₂ h₂
  rw [c2_eq t₁ h₁.x2] at p₁
  rw [c2_eq t₂ h₂.x2] at p₂
  refine ⟨p₁, p₂, ?_, by rw [h₁.rd, h₁.wr]; simpa using c₁.cov, by rw [h₁.wr]; exact c₁.covW,
    by rw [h₂.rd, h₂.wr]; simpa using c₂.cov, by rw [h₂.wr]; exact c₂.covW⟩
  simp only [compK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    h₁.x0, h₂.x0, h₁.x1, h₂.x1, h₁.x2, h₂.x2, h₁.x3, h₂.x3, c₁.x19, c₂.x19, c₁.x1, c₂.x1, c₁.x20, c₂.x20,
    h₁.sp, h₂.sp, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end

end VG.Proof.Pbkdf2.AArch64
