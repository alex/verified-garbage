import VerifiedGarbage.Proof.Poly1305.X86_64.Common
import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.TCB.X86_64.Target

/-!
# Poly1305 on x86-64: saving registers, loading the key and the accumulator

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305

open Spec.Poly1305

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let key : Region := ⟨s.gpr .rsi, 32⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [state] ∧ state.Disjoint key ∧ ret.Disjoint state
  post s s' := Repr s'.mem (s.gpr .rdi) (bytesAt s.mem (s.gpr .rsi) 32) []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n: usize)`. -/
def blocksX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let blocks : Region := ⟨s.gpr .rsi, 16 * (s.gpr .rdx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧ ret.Disjoint state ∧
      (s.gpr .rsi).toNat + 16 * (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' := ∀ key msg, Repr s.mem (s.gpr .rdi) key msg →
    Repr s'.mem (s.gpr .rdi) key (msg ++ bytesAt s.mem (s.gpr .rsi) (16 * (s.gpr .rdx).toNat))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_update(state: *mut [u64; 16], count: u64, data: *const u8, len: usize, …)`:
only `count mod 16`, the number of bytes buffered, matters. The state must be
writable, and it may be permitted to write other regions (which it does
not). -/
def updateX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [data] ∧ state ∈ s.wr ∧ state.Disjoint data ∧ ret.Disjoint state
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .rdi) key msg →
    (s.gpr .rsi).toNat % 16 = msg.length % 16 →
    Buffered s'.mem (s.gpr .rdi) key (msg ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_finalize(state: *mut [u64; 16], count: u64, out: *mut [u8; 16], …)`:
only `count mod 16`, the number of bytes buffered, matters, and it returns
with `rcx = out`. The state and `out` must be writable, and it may be
permitted to write other regions (which it does not). -/
def finalizeX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let out : Region := ⟨s.gpr .rdx, 16⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    state ∈ s.wr ∧ out ∈ s.wr ∧ state.Disjoint out ∧ ret.Disjoint state ∧ ret.Disjoint out
  post s s' := s'.gpr .rcx = s.gpr .rdx ∧ ∀ key msg, Buffered s.mem (s.gpr .rdi) key msg →
    (s.gpr .rsi).toNat % 16 = msg.length % 16 → bytesAt s'.mem (s.gpr .rdx) 16 = mac key msg
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx

end VG.Proof.Poly1305

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

section
variable (s₀ : State)
/-- The state, and the return address, on entry. -/
abbrev st : Addr := s₀.gpr .rdi
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
end

/-- The callee-saved registers of `s` are saved in the state at `st`. -/
def Saved (st : Addr) (s : State) (m : Mem) : Prop :=
  m.readW (off st 72) 64 = s.gpr .rbx ∧ m.readW (off st 80) 64 = s.gpr .rbp ∧
  m.readW (off st 88) 64 = s.gpr .r12 ∧ m.readW (off st 96) 64 = s.gpr .r13 ∧
  m.readW (off st 104) 64 = s.gpr .r14 ∧ m.readW (off st 112) 64 = s.gpr .r15

theorem save_eq : save = [
    .store (at_ .rdi 72) .rbx, .store (at_ .rdi 80) .rbp, .store (at_ .rdi 88) .r12,
    .store (at_ .rdi 96) .r13, .store (at_ .rdi 104) .r14, .store (at_ .rdi 112) .r15] := rfl

theorem restore_eq : restore = [
    .mov .rbx (.mem (at_ .rdi 72)), .mov .rbp (.mem (at_ .rdi 80)), .mov .r12 (.mem (at_ .rdi 88)),
    .mov .r13 (.mem (at_ .rdi 96)), .mov .r14 (.mem (at_ .rdi 104)), .mov .r15 (.mem (at_ .rdi 112))] := rfl

set_option simprocs false in
theorem save_ok (s : State) (hw : sR (s.gpr .rdi) ∈ s.wr) :
    WP isa (.block save) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.cf = s.cf ∧ s'.zf = s.zf ∧
      Frame [svR (s.gpr .rdi)] s.mem s'.mem ∧ Saved (s.gpr .rdi) s s'.mem := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega)⟩
  have o0 := o 72 (by omega); have o1 := o 80 (by omega); have o2 := o 88 (by omega)
  have o3 := o 96 (by omega); have o4 := o 104 (by omega); have o5 := o 112 (by omega)
  apply WP.of_runBlock
  rw [save_eq]
  simp only [off] at o0 o1 o2 o3 o4 o5
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    State.store64, o0, o1, o2, o3, o4, o5, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
  · have c : ∀ d, 72 ≤ d → d + 8 ≤ 120 → (svR (s.gpr .rdi)).Contains (off (s.gpr .rdi) d) (64 / 8) :=
      fun d h₁ h₂ => svR_contains _ h₁ h₂
    refine (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 72 ?_ ?_)).writeW
      (List.mem_singleton_self _) _ (c 80 ?_ ?_)).writeW (List.mem_singleton_self _) _ (c 88 ?_ ?_)).writeW
      (List.mem_singleton_self _) _ (c 96 ?_ ?_)).writeW (List.mem_singleton_self _) _ (c 104 ?_ ?_)
      |>.writeW (List.mem_singleton_self _) _ (c 112 ?_ ?_) <;> omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := {decide := true}) only [off, Mem.readW_writeW_self64, readW_writeW_off]

theorem setup_eq : setup = [
    .movImm64 .rax M0, .mov .r8 (.mem (at_ .rdi 24)), .alu .and .r8 (.reg .rax),
    .movImm64 .rax M1, .mov .r9 (.mem (at_ .rdi 32)), .alu .and .r9 (.reg .rax),
    .mov .r10 (.reg .r9), .shift .shr .r10 2, .alu .add .r10 (.reg .r9),
    .mov .r11 (.mem (at_ .rdi 0)), .mov .rbx (.mem (at_ .rdi 8)), .mov .rbp (.mem (at_ .rdi 16))] := rfl

/-- `s1 = r1 + r1 / 4` is `5 q` for `r1 = 4 q`. -/
theorem s1_toNat (k : BitVec 64) :
    (((k &&& M1) >>> 2) + (k &&& M1)).toNat = 5 * ((k &&& M1).toNat / 4) := by
  have h1 := r1_lt k; have h2 := r1_mod k
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

set_option simprocs false in
theorem setup_ok (s : State) (hw : sR (s.gpr .rdi) ∈ s.rd ++ s.wr) :
    WP isa (.block setup) s fun s' =>
      s'.gpr .r8 = s.mem.readW (off (s.gpr .rdi) 24) 64 &&& M0 ∧
      s'.gpr .r9 = s.mem.readW (off (s.gpr .rdi) 32) 64 &&& M1 ∧
      (s'.gpr .r10).toNat = 5 * ((s'.gpr .r9).toNat / 4) ∧
      s'.gpr .r11 = s.mem.readW (off (s.gpr .rdi) 0) 64 ∧
      s'.gpr .rbx = s.mem.readW (off (s.gpr .rdi) 8) 64 ∧
      s'.gpr .rbp = s.mem.readW (off (s.gpr .rdi) 16) 64 ∧
      Keeps [.rax, .r8, .r9, .r10, .r11, .rbx, .rbp] s s' := by
  have i : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega)⟩
  have i0 := i 0 (by omega); have i8 := i 8 (by omega); have i16 := i 16 (by omega)
  have i24 := i 24 (by omega); have i32 := i 32 (by omega)
  simp only [off] at i0 i8 i16 i24 i32
  apply WP.of_runBlock
  rw [setup_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, execAlu, execShift, arithFlags, State.setReg, State.setFlags, State.load64, i0, i8, i16,
    i24, i32, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, s1_toNat _, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]

end VG.Proof.Poly1305.X86_64
