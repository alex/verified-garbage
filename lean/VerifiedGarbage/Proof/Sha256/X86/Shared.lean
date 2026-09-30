import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.Sha256.X86.Contract
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.MdStream.X86.Finalize
import VerifiedGarbage.Proof.MdStream.X86.Words
import VerifiedGarbage.Proof.Sha256.Md
import VerifiedGarbage.Impl.Sha256.X86.Stream
import VerifiedGarbage.Proof.Sha256.X86.Lit

/-!
# Streaming SHA-256 on x86 (32-bit): `init`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha256.X86.Stream

open VG VG.X86 VG.Impl.Sha256.X86.Stream
open VG.Impl.Sha256.X86 (at_)
open VG.Spec.Sha256 (stateAt H0)

/-- The two instructions storing the word `x` at `[eax + 4 * k]`. -/
def word (x : BitVec 32) (k : Nat) : List Instr := [.mov .ecx (.imm x), .store (at_ .eax (4 * k)) .ecx]

theorem init_eq : init = .seq (.block [.mov .eax (.mem (at_ .esp 4))])
    (.block (word H0[0] 0 ++ word H0[1] 1 ++ word H0[2] 2 ++ word H0[3] 3 ++ word H0[4] 4 ++
      word H0[5] 5 ++ word H0[6] 6 ++ word H0[7] 7)) := rfl

theorem word_ok {x : BitVec 32} {k : Nat} {rest : List Instr} {s : State} {Q : State → Prop}
    {st : BitVec 32} (heax : s.gpr .eax = st) (hout : InRegions s.wr (addr st (4 * k)) 4)
    (kk : ∀ s', s'.gpr .eax = st → (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → s'.mem = s.mem.writeW (addr st (4 * k)) x → WP isa (.block rest) s' Q) :
    WP isa (.block (word x k ++ rest)) s Q := by
  simp only [word, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ u₁ => wp_store (a := addr st (4 * k))
    (by rw [ea_at, u₁.other _ (by decide), heax]) (by rw [u₁.wr]; exact hout) fun s₂ u₂ => ?_
  refine kk s₂ (by rw [u₂.gpr, u₁.other _ (by decide), heax]) (fun r hr => by rw [u₂.gpr, u₁.other r hr])
    (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) ?_
  rw [u₂.mem, u₁.gpr, u₁.mem]

theorem init_correct {s₀ : State} (hp : Proof.Sha256.initX86.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha256.initX86.post s₀ s' := by
  obtain ⟨hrd, hwr, hargs, hret, hfit, hsp⟩ := hp
  set st := arg s₀ 0 with hst
  have o : ∀ k, k < 8 → InRegions s₀.wr (addr st (4 * k)) 4 :=
    fun k hk => ⟨⟨st.setWidth 64, 96⟩, by simp [hwr], contains_addr (by omega) (by omega) hfit⟩
  rw [init_eq]
  refine WP.seq (wp_movm (a := addr (s₀.gpr .esp) 4) (ea_at _ _ _)
    ⟨⟨argAddr s₀ 0, 4⟩, by simp [hrd], Region.contains_self _ _⟩ fun s₁ u₁ => WP.block_nil ?_)
  have e1 : s₁.gpr .eax = st := u₁.gpr
  have w1 : s₁.wr = s₀.wr := u₁.wr
  rw [← List.append_nil (_ ++ word H0[7] 7)]
  simp only [List.append_assoc]
  refine word_ok e1 (by rw [w1]; exact o 0 (by omega)) fun s2 a2 g2 _ wr2 m2 => ?_
  refine word_ok a2 (by rw [wr2, w1]; exact o 1 (by omega)) fun s3 a3 g3 _ wr3 m3 => ?_
  refine word_ok a3 (by rw [wr3, wr2, w1]; exact o 2 (by omega)) fun s4 a4 g4 _ wr4 m4 => ?_
  refine word_ok a4 (by rw [wr4, wr3, wr2, w1]; exact o 3 (by omega)) fun s5 a5 g5 _ wr5 m5 => ?_
  refine word_ok a5 (by rw [wr5, wr4, wr3, wr2, w1]; exact o 4 (by omega)) fun s6 a6 g6 _ wr6 m6 => ?_
  refine word_ok a6 (by rw [wr6, wr5, wr4, wr3, wr2, w1]; exact o 5 (by omega))
    fun s7 a7 g7 _ wr7 m7 => ?_
  refine word_ok a7 (by rw [wr7, wr6, wr5, wr4, wr3, wr2, w1]; exact o 6 (by omega))
    fun s8 a8 g8 _ wr8 m8 => ?_
  refine word_ok a8 (by rw [wr8, wr7, wr6, wr5, wr4, wr3, wr2, w1]; exact o 7 (by omega))
    fun s9 _ g9 _ _ m9 => WP.block_nil ?_
  have k9 : ∀ r, r ≠ .ecx → r ≠ .eax → s9.gpr r = s₀.gpr r := fun r h h' => by
    rw [g9 r h, g8 r h, g7 r h, g6 r h, g5 r h, g4 r h, g3 r h, g2 r h, u₁.other r h']
  have ha : ∀ k, k < 8 → addr st (4 * k) = st.setWidth 64 + BitVec.ofNat 64 (4 * k) :=
    fun k hk => addr_eq (by omega)
  have hm : s9.mem = Proof.Sha256.StateMem.writeState s₀.mem (st.setWidth 64) H0 := by
    rw [m9, m8, m7, m6, m5, m4, m3, m2, u₁.mem, ha 0 (by omega), ha 1 (by omega), ha 2 (by omega),
      ha 3 (by omega), ha 4 (by omega), ha 5 (by omega), ha 6 (by omega), ha 7 (by omega)]
    rfl
  have hf : Frame [⟨st.setWidth 64, 96⟩] s₀.mem s9.mem := by
    rw [m9, m8, m7, m6, m5, m4, m3, m2, u₁.mem]
    have c : ∀ k, k < 8 → (⟨st.setWidth 64, 96⟩ : Region).Contains (addr st (4 * k)) (32 / 8) :=
      fun k hk => contains_addr (by omega) (by omega) hfit
    exact ((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 1 (by omega))).writeW (List.mem_singleton_self _) _
      (c 2 (by omega))).writeW (List.mem_singleton_self _) _ (c 3 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 4 (by omega))).writeW (List.mem_singleton_self _) _
      (c 5 (by omega))).writeW (List.mem_singleton_self _) _ (c 6 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 7 (by omega))
  refine ⟨⟨fun r hr => k9 r ?_ ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · exact hf.readW (Region.contains_self _ _) (by simpa using hret) (by decide)
  · show Spec.Sha256.Repr s9.mem (st.setWidth 64) []
    rw [hm]
    exact Proof.Sha256.Stream.repr_nil (Proof.Sha256.StateMem.stateAt_writeState _ _ _)

/-- Memory holding the argument `0x1000` at `0x4004`. -/
def initSatMem : Mem := fun a => if a = 0x4005 then 0x10 else 0

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := initSatMem
  rd := [⟨0x4004, 4⟩]
  wr := [⟨0x1000, 96⟩]

theorem initSat_pre : Proof.Sha256.initX86.pre initSat := by
  have a0 : arg initSat 0 = 0x1000 := by decide
  have e : argAddr initSat 0 = 0x4004 := by decide
  simp only [Proof.Sha256.initX86, a0, e]
  exact ⟨rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide, by decide⟩

/-- The initial taint: the argument is public, and the word holding `state`
is the base address of the writable region. -/
def initτ₀ : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 8 }

theorem init_agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha256.initX86.pre s₁) (h₂ : Proof.Sha256.initX86.pre s₂)
    (hpub : Proof.Sha256.initX86.pub s₁ s₂) : VG.X86.Taint.Agree initτ₀ s₁ s₂ := by
  obtain ⟨hesp, a0⟩ := hpub
  have wf : ∀ s, Proof.Sha256.initX86.pre s → VG.X86.Taint.Wf initτ₀ s := by
    intro s hs
    obtain ⟨-, hw, hd, hr, -, hsp⟩ := hs
    refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
      fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hsp, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩
    simp only [hw, List.mem_singleton]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 4) (by omega) hr hd
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf _ h₁, wf _ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [initτ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · simp only [initτ₀] at hk
    rw [show VG.X86.Taint.depth initτ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq h₁.2.2.2.2.2 h4 hk, VG.X86.Taint.argByte_eq h₂.2.2.2.2.2 h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega)),
      show (k - 4) / 4 = 0 by omega]
    exact congrArg _ a0

theorem init_verified : Verified X86.target init Proof.Sha256.initX86 := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, initSat_pre⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct hs
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) initτ₀ (fun _ _ h₁ h₂ hp => init_agree₀ h₁ h₂ hp)
      (by taint_decide)

end VG.Proof.Sha256.X86.Stream

/-!
# Streaming SHA-256 on x86 (32-bit): `update` and `finalize`

Untrusted: everything here is checked by Lean. `update` and `finalize` are
the generic streaming code (`Impl/MdStream/X86.lean`) for SHA-256's sizes,
length field and digest (`params`), instruction for instruction
(`update_eq`, `finalize_eq`), so they are verified by the generic proofs
(`Proof/MdStream/X86/`) for SHA-256's instance (`Proof/Sha256/Md.lean`) with
160 bytes of scratch space, given what SHA-256's own pieces do: its length
field and digest (`shape`), that its compression function is verified
(`callee`), and that the taint analysis accepts its code (which it checks
together with the compression function's).
-/

namespace VG.Proof.Sha256.X86.Stream

open VG VG.X86 VG.Proof.MdStream VG.Proof.MdStream.X86
open VG.Impl.MdStream.X86 (Params len64 out32)

/-- SHA-256's sizes, length field and digest in the generic streaming code. -/
def params : Params where
  N := 32
  so := 112
  len := len64 112 88 true
  out := out32 8 true

theorem update_eq :
    Impl.Sha256.X86.Stream.update = Impl.MdStream.X86.update params "vg_sha256_compress" Impl.Sha256.X86.compress :=
  rfl

theorem finalize_eq :
    Impl.Sha256.X86.Stream.finalize =
      Impl.MdStream.X86.finalize params "vg_sha256_compress" Impl.Sha256.X86.compress :=
  rfl

theorem dims : Dims params 160 := ⟨by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  len _ hfit hlo hhi ho₁ ho₂ := len64_ok (so := params.so) (d := params.N + 56) (be := true) (by omega)
    hlo hhi ho₁ ho₂
  out _ hbx hax hin hout hd := by
    refine (out32_ok (n := 8) true (by decide) hbx hax hin hout hd).mono fun s' ⟨g, rd, wr, m⟩ =>
      ⟨g, rd, wr, ?_⟩
    rw [m, digest_eq]

theorem callee : CalleeOk (P := params) md Impl.Sha256.X86.compress :=
  ⟨compress_verified.1, NoSp.of_all (by lit_decide), by lit_decide⟩

namespace Update

theorem update_verified : Verified X86.target Impl.Sha256.X86.Stream.update Proof.Sha256.updateX86 := by
  have ct : ConstantTime isa (updK (P := params) md 160).pre (updK (P := params) md 160).pub
      Impl.Sha256.X86.Stream.update :=
    VG.Taint.constantTime (A := taint) (MdStream.X86.Update.τ₀ params 160)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Update.agree₀ dims h₁ h₂ hp) (by taint_decide)
  rw [update_eq] at ct ⊢
  have h := MdStream.X86.Update.verified (name := "vg_sha256_compress") dims callee ct
  exact Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86.Update.sat params 160

end Update

namespace Finalize

theorem finalize_verified : Verified X86.target Impl.Sha256.X86.Stream.finalize Proof.Sha256.finalizeX86 := by
  have ct : ConstantTime isa (finK (P := params) md 160).pre (finK (P := params) md 160).pub
      Impl.Sha256.X86.Stream.finalize :=
    VG.Taint.constantTime (A := taint) (MdStream.X86.Finalize.τ₀ params 160)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Finalize.agree₀ dims h₁ h₂ hp) (by taint_decide)
  rw [finalize_eq] at ct ⊢
  have h := MdStream.X86.Finalize.verified (name := "vg_sha256_compress") dims shape callee ct
  exact Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.X86.Finalize.sat params 160

end Finalize

end VG.Proof.Sha256.X86.Stream

/-!
# Sha256 on X86: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha256/X86/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha256/Contract.lean`, which the
artifacts are emitted with.

The shared contracts give the functions more scratch than these ones use (560
bytes for `compress`, 608 for `update` and `finalize`, sized for the x86-64
AVX2 compression function): the per-target contracts are first widened to
that scratch (`Verified.widen`, the same code running with the same trace and
result; `update`'s also to writable arguments, `Verified.narrowTo`), then
moved to the shared ones. `update` and `finalize` call the compression
function, using the 20 bytes of stack below the return address.
-/

namespace VG.Proof.Sha256.X86.Shared

open _root_.VG.X86

/-- `compressX86` with 560 bytes of scratch. -/
def compressWide : Contract X86.isa :=
  { Proof.Sha256.compressX86 with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, 32⟩
      let blocks : Region := ⟨(arg s 1).setWidth 64, 64 * (arg s 2).toNat⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 560⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 * (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 560 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 }

/-- `updateX86` with 608 bytes of scratch, and its arguments writable. -/
def updateWide : Contract X86.isa :=
  { Proof.Sha256.updateX86 with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, 96⟩
      let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
      let scratch : Region := ⟨(arg s 5).setWidth 64, 608⟩
      let args : Region := ⟨argAddr s 0, 24⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
      s.rd = [data] ∧ s.wr = [state, scratch, args] ∧
      state.Disjoint scratch ∧ args.Disjoint state ∧ args.Disjoint scratch ∧
      data.Disjoint state ∧ data.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
      stack.Disjoint data ∧
      (arg s 0).toNat + 96 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 608 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 }

/-- `finalizeX86` with 608 bytes of scratch. -/
def finalizeWide : Contract X86.isa :=
  { Proof.Sha256.finalizeX86 with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, 96⟩
      let out : Region := ⟨(arg s 3).setWidth 64, 32⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 608⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
      s.rd = [] ∧ s.wr = [state, out, scratch, args] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 96 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 608 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub112 (a : Addr) : Region.Sub ⟨a, 112⟩ ⟨a, 560⟩ := Region.sub_prefix (by decide)
theorem sub160 (a : Addr) : Region.Sub ⟨a, 160⟩ ⟨a, 608⟩ := Region.sub_prefix (by decide)
theorem le112 {x : Nat} (h : x + 560 ≤ 2 ^ 32) : x + 112 ≤ 2 ^ 32 := by omega
theorem le160 {x : Nat} (h : x + 608 ≤ 2 ^ 32) : x + 160 ≤ 2 ^ 32 := by omega

/-- Rewrites the per-target contracts at a narrowed state (`arg` does not
unfold cheaply). -/
macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Sha256.compressX86, Proof.Sha256.updateX86, Proof.Sha256.finalizeX86,
    compressWide, updateWide, finalizeWide, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions, State.withRegions_gpr,
    State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem compressWide_verified (hsat : ∃ s, compressWide.pre s) :
    Verified X86.target Impl.Sha256.X86.compress compressWide :=
  Verified.widen Proof.Sha256.X86.compress_verified
    (fun s => [⟨(arg s 0).setWidth 64, 32⟩, ⟨(arg s 3).setWidth 64, 112⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃.sub_right (sub112 _), h₄, h₅.sub_right (sub112 _), h₆, h₇.sub_right (sub112 _),
        h₈, h₉.sub_right (sub112 _), h₁₀, h₁₁, le112 h₁₂, h₁₃⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

/-- `update` only reads its arguments. -/
theorem updateWide_verified (hsat : ∃ s, updateWide.pre s) :
    Verified X86.target Impl.Sha256.X86.Stream.update updateWide :=
  Verified.narrowTo Proof.Sha256.X86.Stream.Update.update_verified
    (fun s => [⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩, ⟨argAddr s 0, 24⟩])
    (fun s => [⟨(arg s 0).setWidth 64, 96⟩, ⟨(arg s 5).setWidth 64, 160⟩])
    (fun _ h => by
      obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩ := h
      narrow
      exact ⟨trivial, trivial, h₃.sub_right (sub160 _), h₆, h₇.sub_right (sub160 _), h₄,
        h₅.sub_right (sub160 _), h₈, h₉.sub_right (sub160 _), h₁₀, h₁₁.sub_right (sub160 _), h₁₂, h₁₃, h₁₄,
        le160 h₁₅, h₁₆, h₁₇⟩)
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_singleton_self _))), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp,
          by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

theorem finalizeWide_verified (hsat : ∃ s, finalizeWide.pre s) :
    Verified X86.target Impl.Sha256.X86.Stream.finalize finalizeWide :=
  Verified.widen Proof.Sha256.X86.Stream.Finalize.finalize_verified
    (fun s => [⟨(arg s 0).setWidth 64, 96⟩, ⟨(arg s 3).setWidth 64, 32⟩,
      ⟨(arg s 4).setWidth 64, 160⟩, ⟨argAddr s 0, 20⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃, h₄.sub_right (sub160 _), h₅.sub_right (sub160 _), h₆, h₇,
        h₈.sub_right (sub160 _), h₉, h₁₀, h₁₁.sub_right (sub160 _), h₁₂, h₁₃, h₁₄.sub_right (sub160 _),
        h₁₅, h₁₆, le160 h₁₇, h₁₈, h₁₉⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) .nil))))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State := { Proof.Sha256.X86.satState with wr := [⟨0x1000, 32⟩, ⟨0x3000, 560⟩] }

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State :=
  { Proof.Sha256.X86.Stream.Update.sat with
    rd := [⟨0x2000, 0⟩], wr := [⟨0x1000, 96⟩, ⟨0x3000, 608⟩, ⟨0x5004, 24⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha256.X86.Stream.Finalize.sat with
    wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩, ⟨0x3000, 608⟩, ⟨0x5004, 20⟩] }

theorem compressWide_implies : compressWide.Implies (Spec.Sha256.compressContract X86.abi) := by
  contract_implies [Spec.Sha256.compressContract, Spec.Sha256.compressSig, compressWide,
    Proof.Sha256.compressX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [compressSat, Proof.Sha256.X86.satState, Proof.Sha256.X86.satMem, X86.arg, X86.argAddr,
      Mem.readW, Mem.read] using compressSat

theorem compress :
    Verified X86.target Impl.Sha256.X86.compress (Spec.Sha256.compressContract X86.abi) :=
  (compressWide_verified compressWide_implies.sat_left).of_implies compressWide_implies

theorem init :
    Verified X86.target Impl.Sha256.X86.Stream.init (Spec.Sha256.initContract X86.abi) :=
  Proof.Sha256.X86.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha256.initContract, Spec.Sha256.initSig, Proof.Sha256.initX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sha256.X86.Stream.initSat, Proof.Sha256.X86.Stream.initSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using Proof.Sha256.X86.Stream.initSat)

theorem updateWide_implies : updateWide.Implies (Spec.Sha256.updateContract X86.abi 20) := by
  contract_implies [Spec.Sha256.updateContract, Spec.Sha256.updateSig, updateWide,
    Proof.Sha256.updateX86, Proof.Sha256.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [updateSat, Proof.Sha256.X86.Stream.Update.sat, MdStream.X86.Update.sat, MdStream.X86.Update.sat₀,
      MdStream.X86.Update.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using updateSat

theorem update :
    Verified X86.target Impl.Sha256.X86.Stream.update (Spec.Sha256.updateContract X86.abi 20) :=
  (updateWide_verified updateWide_implies.sat_left).of_implies updateWide_implies

theorem finalizeWide_implies : finalizeWide.Implies (Spec.Sha256.finalizeContract X86.abi 20) := by
  contract_implies [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig, finalizeWide,
    Proof.Sha256.finalizeX86, Proof.Sha256.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finalizeSat, Proof.Sha256.X86.Stream.Finalize.sat, MdStream.X86.Finalize.sat, MdStream.X86.Finalize.sat₀,
      MdStream.X86.Finalize.satMem, Proof.Sha256.X86.Stream.params, X86.arg, X86.argAddr, Mem.readW,
      Mem.read] using finalizeSat

theorem finalize :
    Verified X86.target Impl.Sha256.X86.Stream.finalize (Spec.Sha256.finalizeContract X86.abi 20) :=
  (finalizeWide_verified finalizeWide_implies.sat_left).of_implies finalizeWide_implies

end VG.Proof.Sha256.X86.Shared
