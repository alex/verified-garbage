import VerifiedGarbage.Impl.MlKem.X86_64.Arith
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86-64: `vg_mlkem_add` and `vg_mlkem_sub`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## One coefficient -/

theorem csub32_add {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (csub32 (a + b)).toNat = condSub (a.toNat + b.toNat) := by
  have e : (a + b).toNat = a.toNat + b.toNat := by rw [BitVec.toNat_add]; rw [q_eq] at *; omega
  rw [csub32_toNat (by rw [e]; rw [q_eq] at *; omega), e]

theorem csub32_sub {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat < q) :
    (csub32 (a + qImm - b)).toNat = condSub (a.toNat + q - b.toNat) := by
  have e : (a + qImm - b).toNat = a.toNat + q - b.toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, qImm_toNat]; rw [q_eq] at *; omega
  rw [csub32_toNat (by rw [e]; rw [q_eq] at *; omega), e]

theorem addBody_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 4)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4) (h3 : InRegions s.wr (s.gpr .rdi) 4) :
    WP isa (.block addBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (csub32 (s.mem.readW (s.gpr .rdi) 32 + s.mem.readW (s.gpr .rsi) 32)) ∧
        s'.gpr .rdi = s.gpr .rdi + 4 ∧ s'.gpr .rsi = s.gpr .rsi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdx, .rdi, .rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold addBody csubQ step2
  xrun [h1, h2, h3, List.cons_append, List.nil_append, csub32]

theorem subBody_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 4)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4) (h3 : InRegions s.wr (s.gpr .rdi) 4) :
    WP isa (.block subBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi)
          (csub32 (s.mem.readW (s.gpr .rdi) 32 + qImm - s.mem.readW (s.gpr .rsi) 32)) ∧
        s'.gpr .rdi = s.gpr .rdi + 4 ∧ s'.gpr .rsi = s.gpr .rsi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdx, .rdi, .rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold subBody csubQ step2
  xrun [h1, h2, h3, List.cons_append, List.nil_append, csub32]

/-! ## The loop -/

namespace AddSub

/-- After `i` coefficients, each one `v k`. -/
structure Inv (s₀ : State) (v : Nat → BitVec 32) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (4 * i)
  rsi : s.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 (4 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [pR (s₀.gpr .rdi)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rdi) k = if k < i then v k else coeffAt s₀.mem (s₀.gpr .rdi) k

section
variable {t : Poly → Poly → Poly} {s₀ : State} (hp : (accK t).pre s₀)
include hp

theorem inF {i : Nat} (hi : i < 256) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    InRegions (s.rd ++ s.wr) (coeffAddr (s₀.gpr .rdi) i) 4 ∧ InRegions s.wr (coeffAddr (s₀.gpr .rdi) i) 4 := by
  rw [hrd, hwr, hp.1, hp.2.1]
  exact ⟨⟨_, by simp, coeff_contains _ hi⟩, ⟨_, by simp, coeff_contains _ hi⟩⟩

theorem inG {i : Nat} (hi : i < 256) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    InRegions (s.rd ++ s.wr) (coeffAddr (s₀.gpr .rsi) i) 4 := by
  rw [hrd, hwr, hp.1, hp.2.1]
  exact ⟨_, by simp, coeff_contains _ hi⟩

/-- `g` is not written. -/
theorem coeffG {m : Mem} (hf : Frame [pR (s₀.gpr .rdi)] s₀.mem m) {i : Nat} (hi : i < 256) :
    coeffAt m (s₀.gpr .rsi) i = coeffAt s₀.mem (s₀.gpr .rsi) i :=
  coeffAt_congr (bytes_frame hf (by simpa using hp.2.2.1.symm) (by decide)) hi

omit hp in
theorem inv_step {v : Nat → BitVec 32} {i : Nat} (hi : i < 256) {s s' : State} (hI : Inv s₀ v i s)
    (hm : s'.mem = s.mem.writeW (s.gpr .rdi) (v i)) (hdi : s'.gpr .rdi = s.gpr .rdi + 4)
    (hsi : s'.gpr .rsi = s.gpr .rsi + 4) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Inv s₀ v (i + 1) s' where
  rdi := by rw [hdi, hI.rdi]; exact ptr_step _ i 4
  rsi := by rw [hsi, hI.rsi]; exact ptr_step _ i 4
  rd := hrd.trans hI.rd
  wr := hwr.trans hI.wr
  frame := by
    rw [hm, hI.rdi]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hi)
  coeff k hk := by
    rw [hm, hI.rdi, ← coeffAddr, coeffAt_writeW _ _ hk hi, hI.coeff k hk]
    by_cases e : i = k
    · subst e; simp
    · have : (k < i + 1) = (k < i) := propext (by omega)
      simp only [e, this, ↓reduceIte]

omit hp in
/-- The loop, from the prologue, with a body that stores `v i` to coefficient `i`. -/
theorem loop_ok {body : List Instr} {v : Nat → BitVec 32}
    (hbody : ∀ i < 256, ∀ s, Inv s₀ v i s → WP isa (.block body) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (v i) ∧ s'.gpr .rdi = s.gpr .rdi + 4 ∧
        s'.gpr .rsi = s.gpr .rsi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdx, .rdi, .rsi, .rcx] s s') :
    WP isa (.seq (.block [.mov32 .rcx (.imm 256)]) (.loop (.block body) .ne)) s₀ (Inv s₀ v 256) := by
  refine WP.seq ?_
  xrun
  refine wp_countdown (cnt := .rcx) (N := 256) (by decide) (by decide) (Inv s₀ v) (fun i hi s hI _ => ?_)
    (fun _ h => h) ?_ (by simp [setReg_gpr])
  · refine WP.mono (hbody i hi s hI) fun s' ⟨⟨hm, hdi, hsi, hcx, hz⟩, hk⟩ => ⟨?_, hcx, hz⟩
    exact inv_step hi hI hm hdi hsi hk.2.1 hk.2.2
  · refine ⟨by simp [setReg_gpr], by simp [setReg_gpr], rfl, rfl, Frame.refl _ _, fun k _ => ?_⟩
    simp [setReg_mem]

/-- The coefficients the loop reads. -/
theorem reads {v : Nat → BitVec 32} {i : Nat} (hi : i < 256) {s : State} (hI : Inv s₀ v i s) :
    s.mem.readW (s.gpr .rdi) 32 = coeffAt s₀.mem (s₀.gpr .rdi) i ∧
      s.mem.readW (s.gpr .rsi) 32 = coeffAt s₀.mem (s₀.gpr .rsi) i ∧
      InRegions (s.rd ++ s.wr) (s.gpr .rdi) 4 ∧ InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4 ∧
      InRegions s.wr (s.gpr .rdi) 4 := by
  have hf := inF hp hi hI.rd hI.wr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hI.rdi, ← coeffAddr, ← coeffAt_eq, hI.coeff i hi]; simp only [Nat.lt_irrefl, ↓reduceIte]
  · rw [hI.rsi, ← coeffAddr, ← coeffAt_eq, coeffG hp hI.frame hi]
  · rw [hI.rdi]; exact hf.1
  · rw [hI.rsi]; exact inG hp hi hI.rd hI.wr
  · rw [hI.rdi]; exact hf.2

omit hp in
/-- The result, with the values of `add` or `sub`. -/
theorem result {v : Nat → BitVec 32} {r : Poly} {s : State} (hI : Inv s₀ v 256 s)
    (hv : ∀ i < 256, (v i).toNat = (r[i]!).val) : PolyIs s.mem (s₀.gpr .rdi) r :=
  polyIs_of_toNat fun i hi => by rw [hI.coeff i hi]; simp only [hi, ↓reduceIte]; exact hv i hi

/-- The whole function, from its precondition. -/
theorem fn_ok {body : List Instr} {v : Nat → BitVec 32}
    (hbody : ∀ i < 256, ∀ s, Inv s₀ v i s → WP isa (.block body) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (v i) ∧ s'.gpr .rdi = s.gpr .rdi + 4 ∧
        s'.gpr .rsi = s.gpr .rsi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdx, .rdi, .rsi, .rcx] s s')
    (hv : ∀ i < 256, (v i).toNat = ((t (polyAt s₀.mem (s₀.gpr .rdi)) (polyAt s₀.mem (s₀.gpr .rsi)))[i]!).val)
    (hc : writesOnly [.rax, .rdx, .rdi, .rsi, .rcx]
      (.seq (.block [.mov32 .rcx (.imm 256)]) (.loop (.block body) .ne)) = true)
    (hm : Code.allInstrs (fun i => !loadsMxcsr i)
      (.seq (.block [.mov32 .rcx (.imm 256)]) (.loop (.block body) .ne) : Prog isa) = true) :
    ∃ tr s', Exec isa (.seq (.block [.mov32 .rcx (.imm 256)]) (.loop (.block body) .ne)) s₀ tr s' ∧
      abiPreserved s₀ s' ∧ (accK t).post s₀ s' := by
  obtain ⟨tr, s', he, hI, hk⟩ := WP.keep _ (loop_ok hbody) hc
  refine ⟨tr, s', he, abiPreserved_of_exec hm he (gprPreserved_of hk (by decide) hI.frame ?_),
    result hI hv⟩
  simpa using hp.2.2.2.1

end

end AddSub

/-! ## The functions -/

theorem add_correct (s : State) (hs : (accK Spec.MlKem.add).pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.add s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlKem.add).post s s' :=
  AddSub.fn_ok hs (v := fun i => csub32 (coeffAt s.mem (s.gpr .rdi) i + coeffAt s.mem (s.gpr .rsi) i))
    (fun i hi s' hI => by
      obtain ⟨e1, e2, h1, h2, h3⟩ := AddSub.reads hs hi hI
      have := addBody_ok s' h1 h2 h3
      rwa [e1, e2] at this)
    (fun i hi => by
      rw [csub32_add (hs.2.2.2.2.2.1 i hi) (hs.2.2.2.2.2.2 i hi), add_get _ _ hi, val_add,
        polyAt_val hs.2.2.2.2.2.1 hi, polyAt_val hs.2.2.2.2.2.2 hi])
    (by decide) (by decide)

theorem sub_correct (s : State) (hs : (accK Spec.MlKem.sub).pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.sub s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlKem.sub).post s s' :=
  AddSub.fn_ok hs (v := fun i => csub32 (coeffAt s.mem (s.gpr .rdi) i + qImm - coeffAt s.mem (s.gpr .rsi) i))
    (fun i hi s' hI => by
      obtain ⟨e1, e2, h1, h2, h3⟩ := AddSub.reads hs hi hI
      have := subBody_ok s' h1 h2 h3
      rwa [e1, e2] at this)
    (fun i hi => by
      rw [csub32_sub (hs.2.2.2.2.2.1 i hi) (hs.2.2.2.2.2.2 i hi), sub_get _ _ hi, val_sub,
        polyAt_val hs.2.2.2.2.2.1 hi, polyAt_val hs.2.2.2.2.2.2 hi])
    (by decide) (by decide)

/-- The pointers and `rsp` are public. -/
def accτ : X86_64.Taint.T := X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]

theorem acc_agree {t : Poly → Poly → Poly} (s₁ s₂ : State) (_ : (accK t).pre s₁) (_ : (accK t).pre s₂)
    (hp : (accK t).pub s₁ s₂) : X86_64.Taint.Agree accτ s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2]

theorem add_ct : ConstantTime isa (accK Spec.MlKem.add).pre (accK Spec.MlKem.add).pub Impl.MlKem.X86_64.add :=
  VG.Taint.constantTime (A := taint) accτ acc_agree (by taint_decide)

theorem sub_ct : ConstantTime isa (accK Spec.MlKem.sub).pre (accK Spec.MlKem.sub).pub Impl.MlKem.X86_64.sub :=
  VG.Taint.constantTime (A := taint) accτ acc_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def accSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 1024⟩]
  wr := [⟨0x1000, 1024⟩]

theorem add_verified :
    Verified X86_64.target Impl.MlKem.X86_64.add (Spec.MlKem.addContract X86_64.abi) :=
  Verified.of_correct add_correct add_ct (by
    mlkem_implies [Spec.MlKem.addContract, Spec.MlKem.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using accSat)

theorem sub_verified :
    Verified X86_64.target Impl.MlKem.X86_64.sub (Spec.MlKem.subContract X86_64.abi) :=
  Verified.of_correct sub_correct sub_ct (by
    mlkem_implies [Spec.MlKem.subContract, Spec.MlKem.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using accSat)

end VG.Proof.MlKem.X86_64
