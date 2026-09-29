import VerifiedGarbage.Proof.MlKem.X86_64.FragBase
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
import VerifiedGarbage.Proof.MlKem.X86_64.Mul
import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
import VerifiedGarbage.Proof.MlKem.X86_64.Cbd
import VerifiedGarbage.Proof.MlKem.X86_64.Encode12
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT

/-!
# ML-KEM-768 on x86-64: the calls of the top-level functions

Untrusted: everything here is checked by Lean. A call, with the moves of
its arguments before it (`glueCall_ok`), leaves the permissions and the
callee-saved registers as they were, and changes memory only within the
buffers it writes and the 24 bytes of stack below `rsp` (`Post`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- What a piece leaves: the permissions and the callee-saved registers,
and memory changed only within `W` and the stack. -/
structure Post (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame (W ++ [below (s.gpr .rsp) 24]) s.mem s'.mem

theorem Post.rsp {s s' : State} {W : List Region} (h : Post s s' W) : s'.gpr .rsp = s.gpr .rsp :=
  h.cs .rsp (by decide)

/-- The registers the moves of arguments write. -/
abbrev argRegs : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9]

theorem argRegs_cs : ∀ r ∈ calleeSaved, r ∉ argRegs := by decide

/-- The moves of the arguments, then a call of verified code. -/
theorem glueCall_ok {glue : List Instr} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 2) {s : State} {V : State → Prop}
    (hg : WP isa (.block glue) s fun s1 => (V s1 ∧ s1.mem = s.mem) ∧ Keep argRegs s s1)
    {rd wr : List Region} (hpre : ∀ s1, V s1 → s1.mem = s.mem → Keep argRegs s s1 →
      k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.seq (.block glue) (.call n c)) s fun s' => Post s s' wr ∧
      ∃ s1, V s1 ∧ s1.mem = s.mem ∧ Keep argRegs s s1 ∧ ∃ s₂ : State, s₂.mem = s'.mem ∧
        (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧ k.post (s1.callEntry.withRegions rd wr) s₂ := by
  refine WP.seq (WP.mono hg fun s1 ⟨⟨hV, hm⟩, k1⟩ => ?_)
  refine WP.call hv hsp (by omega) (hpre s1 hV hm k1) (by rw [k1.2.1, k1.2.2]; exact hc)
    (by rw [k1.2.2]; exact hw) fun s' hrd hwr hcs hf _ hpost => ⟨⟨hrd.trans k1.2.1, hwr.trans k1.2.2,
      fun r hr => by rw [hcs r hr, k1.gpr (argRegs_cs r hr)], ?_⟩, s1, hV, hm, k1, hpost⟩
  have hsp1 : s1.gpr .rsp = s.gpr .rsp := k1.gpr (by decide)
  rw [hm, hsp1] at hf
  exact Frame.below_mono hf (by omega) (by omega)

/-- The trace of the moves then a call, from two runs where the moves are
the same and the callee's public data agree. -/
theorem glueCall_tr {glue : List Instr} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} {V : State → State → Prop}
    (hgt : RelCT isa P (.block glue) fun _ _ => True)
    (hg : ∀ x y, P x y → WP isa (.block glue) x (V x) ∧ WP isa (.block glue) y (V y))
    (hP : ∀ x y x1 y1, P x y → V x x1 → V y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x1.rd ++ x1.wr) ∧ Covers wr₁ x1.wr ∧
      Covers (rd₂ ++ wr₂) (y1.rd ++ y1.wr) ∧ Covers wr₂ y1.wr ∧ x1.gpr .rsp = y1.gpr .rsp) :
    RelCT isa P (.seq (.block glue) (.call n c)) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ V x x1 ∧ V y y1) hgt hg
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.callEx hv hct fun x1 y1 ⟨x, y, hp, h1, h2⟩ => hP x y x1 y1 hp h1 h2)

/-! ## Regions on entry to a callee -/

theorem ce_gpr' (s : State) {r : Reg} (h : r ≠ .rsp) : s.callEntry.gpr r = s.gpr r := State.callEntry_gpr _ h

/-- The return address of a call is apart from a region apart from the stack. -/
theorem ret_disj (s : State) {R : Region} (h : (below (s.gpr .rsp) 24).Disjoint R) :
    (retR s.callEntry).Disjoint R := by
  refine h.sub_left ?_
  simp only [retR, State.callEntry_rsp]
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (s.gpr .rsp - BitVec.ofNat 64 24) = (x - (s.gpr .rsp - 8)) + 16 by bv_omega, BitVec.toNat_add]
  have : (16 : BitVec 64).toNat = 16 := rfl
  omega

/-- The stack a callee's own calls use (16 bytes below its return address). -/
theorem stk_disj (s : State) {R : Region} (h : (below (s.gpr .rsp) 24).Disjoint R) :
    (below (s.callEntry.gpr .rsp) 16).Disjoint R := by
  refine h.sub_left ?_
  simp only [State.callEntry_rsp]
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (s.gpr .rsp - BitVec.ofNat 64 24) = x - (s.gpr .rsp - 8 - BitVec.ofNat 64 16) by bv_omega]
  omega

theorem k16 (s : State) {R : Region} (h : (below (s.gpr .rsp) 24).Disjoint R) : (below (s.gpr .rsp) 16).Disjoint R :=
  h.sub_left (below_sub (by omega) (by omega))

/-- A polynomial apart from the stack reads the same on entry to a callee. -/
theorem ce_polyAt (s : State) {p : Addr} (h : (below (s.gpr .rsp) 24).Disjoint (pR p)) :
    polyAt s.callEntry.mem p = polyAt s.mem p :=
  polyAt_congr fun _ hi => callEntry_bytes s (R := pR p) (k16 s h) (by simp) hi

theorem ce_reduced (s : State) {p : Addr} (h : (below (s.gpr .rsp) 24).Disjoint (pR p)) :
    Reduced s.callEntry.mem p ↔ Reduced s.mem p :=
  ⟨reduced_congr fun _ hi => (callEntry_bytes s (R := pR p) (k16 s h) (by simp) hi).symm,
    reduced_congr fun _ hi => callEntry_bytes s (R := pR p) (k16 s h) (by simp) hi⟩

theorem ce_bytesAt (s : State) {p : Addr} {n : Nat} (hn : n < 2 ^ 64) (h : (below (s.gpr .rsp) 24).Disjoint ⟨p, n⟩) :
    bytesAt s.callEntry.mem p n = bytesAt s.mem p n := callEntry_bytesAt s hn (k16 s h)

end VG.Proof.MlKem.X86_64
