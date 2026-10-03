import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Memory
import VerifiedGarbage.Proof.Gcm.Spec

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86 (GPre hP yP dP nBlk)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- Every instruction before the final Y store retains memory, regions and
all cdecl callee-saved registers. -/
structure Env (s₀ s : State) : Prop where
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r

theorem Env.refl (s : State) : Env s s := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Env.sp {s₀ s : State} (h : Env s₀ s) : s.gpr .esp = s₀.gpr .esp :=
  h.saved .esp (by decide)

theorem Env.of_setup {s₀ s s' : State} {rs : List XReg} (h : Env s₀ s)
    (hf : SetupFrame rs s s') : Env s₀ s' :=
  ⟨hf.mem.trans h.mem, hf.rd.trans h.rd, hf.wr.trans h.wr, fun r hr => by
    have hn : r ≠ .eax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hf.gpr r hn).trans (h.saved r hr)⟩

theorem Env.of_only {s₀ s s' : State} {rs : List XReg} (h : Env s₀ s)
    (hf : Only rs s s') : Env s₀ s' :=
  ⟨hf.mem.trans h.mem, hf.rd.trans h.rd, hf.wr.trans h.wr,
    fun r hr => (congrFun hf.gpr r).trans (h.saved r hr)⟩

theorem Env.setReg {s₀ s : State} (h : Env s₀ s) (d : Reg) (v : BitVec 32)
    (hd : d ∉ calleeSaved) : Env s₀ (s.setReg d v) :=
  ⟨(mem_setReg s d v).trans h.mem, (rd_setReg s d v).trans h.rd,
    (wr_setReg s d v).trans h.wr, fun r hr => by
    rw [gpr_setReg_of_ne s v (show r ≠ d from fun heq => hd (heq ▸ hr))]
    exact h.saved r hr⟩

abbrev H (s₀ : State) : Block := blockAt s₀.mem ((hP s₀).setWidth 64)
abbrev Y (s₀ : State) (i : Nat) : Block :=
  ghashFrom (H s₀) (blockAt s₀.mem ((yP s₀).setWidth 64))
    (blocksAt s₀.mem ((dP s₀).setWidth 64) i)

/-- The accumulator after i blocks and public remaining count/data pointer. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  env : Env s₀ s
  le : i ≤ nBlk s₀
  count : s.gpr .eax = BitVec.ofNat 32 (nBlk s₀ - i)
  data : s.gpr .edx = dP s₀ + BitVec.ofNat 32 (16 * i)
  out : s.gpr .ecx = yP s₀
  rev : s.xmm .xmm0 = VG.Proof.Gcm.X86.revMask
  poly : s.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly
  hash : x * φ (s.xmm .xmm3) = φ (H s₀)
  acc : s.xmm .xmm2 = Y s₀ i

end VG.Proof.Gcm.X86.Pclmul
