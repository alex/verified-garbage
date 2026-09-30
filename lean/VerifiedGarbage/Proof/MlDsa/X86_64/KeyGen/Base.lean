import VerifiedGarbage.Proof.MlKem.X86_64.TopBase
import VerifiedGarbage.Impl.MlDsa.X86_64.KeyGen.KeyGen
import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# ML-DSA key generation on x86-64: the primitives, and calling them

Untrusted: everything here is checked by Lean. Key generation is proven for
any implementations of the primitives it calls (`Prims`) that are verified
against their contracts, with at most 16 bytes of stack, and that change the
stack pointer only by calls nested at most twice (`Callee`, `PrimsOk`): as
ML-KEM's top-level functions on x86-64 (`Proof/MlKem/X86_64/`), whose
framework (layouts of buffers, calls, the sponge) the proofs use.

A primitive may load MXCSR (as the MXCSR prologue of Intel's MCDT does), so
MXCSR's control bits (`MX`) are carried from its `abiPreserved`
(`WP.callMx`, `glueCallMx_ok`), and from code that never loads MXCSR
(`WP.mx`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.KeyGen (Prims)

/-! ## The primitives -/

/-- Code `c` verified against the contract `k stk` of some stack `stk ≤ 16`,
that never writes `rsp` but by calls nested at most twice. -/
structure Callee (c : Prog isa) (k : Nat → Contract isa) : Prop where
  verified : ∃ stk, stk ≤ 16 ∧ Verified X86_64.target c (k stk)
  nosp : NoSp c
  depth : c.depth ≤ 2

/-- Verified implementations of the primitives key generation calls. -/
structure PrimsOk (P : Prims) : Prop where
  ntt : Callee P.ntt (fun stk => Spec.MlDsa.nttContract X86_64.abi stk)
  invNtt : Callee P.invNtt (fun stk => Spec.MlDsa.nttInvContract X86_64.abi stk)
  mul : Callee P.mul (fun stk => Spec.MlDsa.mulContract X86_64.abi stk)
  mulAdd : Callee P.mulAdd (fun stk => Spec.MlDsa.mulAddContract X86_64.abi stk)
  add : Callee P.add (fun stk => Spec.MlDsa.addContract X86_64.abi stk)
  rejNtt : Callee P.rejNtt (fun stk => Spec.MlDsa.rejNTTContract X86_64.abi stk)
  rejBounded : Callee P.rejBounded (fun stk => Spec.MlDsa.rejBoundedContract X86_64.abi stk)
  power2Round : Callee P.power2Round (fun stk => Spec.MlDsa.power2RoundContract X86_64.abi stk)
  simpleBitPack : Callee P.simpleBitPack (fun stk => Spec.MlDsa.simpleBitPackContract X86_64.abi stk)
  bitPack : Callee P.bitPack (fun stk => Spec.MlDsa.bitPackContract X86_64.abi stk)

/-! ## MXCSR -/

/-- The control bits of MXCSR, which `abiPreserved` keeps. -/
abbrev MX (s : State) : BitVec 10 := s.mxcsr.extractLsb' 6 10

/-- Code that never loads MXCSR keeps it. -/
theorem WP.mx {c : Prog isa} (hc : ∀ i ∈ instrs c, loadsMxcsr i = false) {s : State} {Q : State → Prop}
    (h : WP isa c s Q) : WP isa c s fun s' => Q s' ∧ MX s' = MX s := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, by rw [MX, MX, Exec.mxcsr hc he]⟩

/-- Whether no instruction of `c` loads MXCSR. -/
def noLd (c : Prog isa) : Bool := c.allInstrs fun i => !loadsMxcsr i

theorem noLd_spec {c : Prog isa} (h : noLd c = true) : ∀ i ∈ instrs c, loadsMxcsr i = false := by
  unfold noLd at h
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  exact fun i hi => by simpa using h i hi

/-- `WP.call`, which also keeps MXCSR's control bits, from the callee's `abiPreserved`. -/
theorem WP.callMx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : 8 * c.depth + 16 < 2 ^ 64)
    {s : State} {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (8 * (c.depth + 1))]) s.mem s'.mem → MX s' = MX s →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        k.post (s.callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (.call n c) s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  have hf := Exec.frameSp he hsp (by omega)
  simp only [State.withRegions_wr, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_rsp] at hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions] at he'
  rw [show s.callEntry.withRegions s.rd s.wr = s.callEntry from rfl] at he'
  let s₂ := s₁.withRegions s.rd s.wr
  have hs₂ : s₂ = s₁.withRegions s.rd s.wr := rfl
  have hsp₂ : s₂.gpr .rsp = s.gpr .rsp - 8 := by
    rw [hs₂, State.withRegions_gpr, habi.1 .rsp (by simp [calleeSaved])]; simp
  have hret : isa.ret s.callEntry s₂ = some (s₂.setReg .rsp (s₂.gpr .rsp + 8)) := by
    simp only [isa, ret]
    refine ite_eq_left ⟨by rw [hsp₂, State.callEntry_rsp], ?_⟩
    have := habi.2.1
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp] at this
    rw [hsp₂, State.callEntry_rsp]; exact this
  have hrsp : (s₂.setReg .rsp (s₂.gpr .rsp + 8)).gpr .rsp = s.gpr .rsp := by
    simp only [State.setReg, ite_true, hsp₂]; exact BitVec.sub_add_cancel _ _
  have hkeep : ∀ r, r ≠ .rsp → (s₂.setReg .rsp (s₂.gpr .rsp + 8)).gpr r = s₂.gpr r :=
    fun r h => by simp [State.setReg, h]
  refine ⟨_, _, .call (call_callEntry s) he' hret, hQ _ rfl rfl (fun r hr' => ?_) ?_ habi.2.2
    ⟨s₁, rfl, fun r h => (hkeep r h).symm, hpost⟩⟩
  · by_cases h : r = .rsp
    · subst h; exact hrsp
    · rw [hkeep r h, hs₂, State.withRegions_gpr, habi.1 r hr', State.withRegions_gpr,
        State.callEntry_gpr _ h]
  · have f₀ : Frame (wr ++ [below (s.gpr .rsp) (8 * (c.depth + 1))]) s.mem s.callEntry.mem :=
      Frame.writeW (Frame.refl _ _) (List.mem_append_right _ (List.mem_singleton_self _)) _
        (below_call _ (by omega) (by omega))
    have f₁ : Frame (wr ++ [below (s.gpr .rsp) (8 * (c.depth + 1))]) s.callEntry.mem s₁.mem :=
      Frame.sub hf fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
        · simp only [List.mem_singleton] at hr; subst hr
          refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
          rw [show 8 * (c.depth + 1) = 8 * c.depth + 8 by omega]
          exact below_callee _ _
    exact Frame.trans f₀ f₁

/-- `glueCall_ok`, keeping MXCSR's control bits. -/
theorem glueCallMx_ok {glue : List Instr} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 2) (hgl : ∀ i ∈ glue, loadsMxcsr i = false) {s : State}
    {V : State → Prop}
    (hg : WP isa (.block glue) s fun s1 => (V s1 ∧ s1.mem = s.mem) ∧ Keep MlKem.X86_64.argRegs s s1)
    {rd wr : List Region} (hpre : ∀ s1, V s1 → s1.mem = s.mem → Keep MlKem.X86_64.argRegs s s1 →
      k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.seq (.block glue) (.call n c)) s fun s' => Post s s' wr ∧ MX s' = MX s ∧
      ∃ s1, V s1 ∧ s1.mem = s.mem ∧ Keep MlKem.X86_64.argRegs s s1 ∧ ∃ s₂ : State, s₂.mem = s'.mem ∧
        (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧ k.post (s1.callEntry.withRegions rd wr) s₂ := by
  refine WP.seq (WP.mono (WP.mx (c := .block glue) (by simpa [instrs] using hgl) hg)
    fun s1 ⟨⟨⟨hV, hm⟩, k1⟩, hx1⟩ => ?_)
  refine WP.callMx hv hsp (by omega) (hpre s1 hV hm k1) (by rw [k1.2.1, k1.2.2]; exact hc)
    (by rw [k1.2.2]; exact hw) fun s' hrd hwr hcs hf hx hpost => ⟨⟨hrd.trans k1.2.1, hwr.trans k1.2.2,
      fun r hr => by rw [hcs r hr, k1.gpr (argRegs_cs r hr)], ?_⟩, hx.trans hx1, s1, hV, hm, k1, hpost⟩
  have hsp1 : s1.gpr .rsp = s.gpr .rsp := k1.gpr (by decide)
  rw [hm, hsp1] at hf
  exact Frame.below_mono hf (by omega) (by omega)

end VG.Proof.MlDsa.X86_64.KeyGen
