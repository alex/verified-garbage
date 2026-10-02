import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Loop
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Arith
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Contracts
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# ML-DSA on x86-64: `vg_mldsa_power2round`
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep writesOnly gprPreserved_of)

/-- `a + 4095`, in 64 bits. -/
abbrev p2rX (x : BitVec 32) : BitVec 64 := BitVec.setWidth 64 x + BitVec.signExtend 64 (4095 : BitVec 32)

/-- The `t1` the body stores. -/
def t1V (x : BitVec 32) : BitVec 32 := BitVec.setWidth 32 (p2rX x >>> 13)

/-- The `t0` the body stores. -/
def t0V (x : BitVec 32) : BitVec 32 :=
  BitVec.setWidth 32 (condAddV (p2rX x &&& BitVec.signExtend 64 (8191 : BitVec 32))
    (BitVec.signExtend 64 (4095 : BitVec 32)) qImm)

theorem p2rBody_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 4)
    (h2 : InRegions s.wr (cfAddr (s.gpr .rsi) (s.gpr .rcx)) 4)
    (h3 : InRegions s.wr (cfAddr (s.gpr .rdx) (s.gpr .rcx)) 4) :
    WP isa (.block (p2rBody ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      (s'.mem = (s.mem.writeW (cfAddr (s.gpr .rsi) (s.gpr .rcx))
          (t1V (s.mem.readW (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 32))).writeW (cfAddr (s.gpr .rdx) (s.gpr .rcx))
          (t0V (s.mem.readW (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 32)) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .r8, .r9, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold p2rBody condAdd
  xrun [h1, h2, h3, ea_cf, List.cons_append, List.nil_append, t1V, t0V, condAddV]

theorem p2rX_toNat {x : BitVec 32} (hx : x.toNat < q) : (p2rX x).toNat = x.toNat + 4095 := by
  rw [q_eq] at hx
  rw [BitVec.toNat_add, setWidth64_toNat, sx_toNat (by decide)]
  have : (4095 : BitVec 32).toNat = 4095 := rfl
  omega

theorem t1V_toNat {x : BitVec 32} (hx : x.toNat < q) : (t1V x).toNat = (x.toNat + 4095) / 8192 := by
  have e : (p2rX x >>> 13).toNat = (x.toNat + 4095) / 8192 := by
    rw [BitVec.toNat_ushiftRight, p2rX_toNat hx, Nat.shiftRight_eq_div_pow]
  rw [q_eq] at hx
  rw [t1V, BitVec.toNat_setWidth, e]
  omega

theorem t0V_toNat {x : BitVec 32} (hx : x.toNat < q) :
    (t0V x).toNat = if (x.toNat + 4095) % 8192 < 4095 then (x.toNat + 4095) % 8192 + q - 4095
      else (x.toNat + 4095) % 8192 - 4095 := by
  have e : (p2rX x &&& BitVec.signExtend 64 (8191 : BitVec 32)).toNat = (x.toNat + 4095) % 8192 := by
    rw [BitVec.toNat_and, p2rX_toNat hx, sx_toNat (by decide),
      show (8191 : BitVec 32).toNat = 2 ^ 13 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hs : (BitVec.signExtend 64 (4095 : BitVec 32)).toNat = 4095 := by decide
  have hq : qImm.toNat = q := rfl
  rw [t0V, BitVec.toNat_setWidth, condAddV_toNat (by decide) (by rw [e, hs, hq, q_eq]; omega), e, hs, hq]
  have := Nat.mod_lt (x.toNat + 4095) (show 8192 > 0 by decide)
  rw [q_eq] at *
  split <;> omega

section
variable {s₀ : State} (hp : power2RoundK.pre s₀)
include hp

theorem p2r_layout : Layout s₀ [.rdi] [.rsi, .rdx] where
  rd p hp' := by
    simp only [List.mem_singleton] at hp'; subst hp'; rw [hp.1]; simp
  wr o ho := by
    rw [hp.2.1]; simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ⊢
    rcases ho with rfl | rfl <;> simp
  dis p hp' o ho := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp' ho
    subst hp'
    rcases ho with rfl | rfl
    exacts [hp.2.2.1, hp.2.2.2.1]
  pw := List.pairwise_cons.mpr ⟨fun b hb => by
    simp only [List.mem_singleton] at hb; subst hb; exact hp.2.2.2.2.1, List.pairwise_singleton _ _⟩

/-- The values the loop writes. -/
def p2rV (s₀ : State) (o : Reg) (k : Nat) : BitVec 32 :=
  if o = .rsi then t1V (coeffAt s₀.mem (s₀.gpr .rdi) k) else t0V (coeffAt s₀.mem (s₀.gpr .rdi) k)

theorem p2r_loop :
    WP isa (mapLoop p2rBody) s₀ (Inv s₀ [.rdi, .rsi, .rdx] [.rsi, .rdx] (p2rV s₀) (fun _ _ => True) 256) := by
  have hL := p2r_layout hp
  refine loop_ok (clob := [.rax, .r8, .r9, .rcx]) hL (by decide) (by decide) (fun _ _ _ _ => trivial)
    fun i hi s hI hc => ?_
  have ha : ∀ p ∈ [Reg.rdi, .rsi, .rdx], cfAddr (s.gpr p) (s.gpr .rcx) = coeffAddr (s₀.gpr p) (255 - i) :=
    fun p hp' => hI.addr hc hi hp'
  refine WP.mono (p2rBody_ok s (by rw [ha _ (by simp)]; exact hI.inR hL (by simp) (by omega))
    (by rw [ha _ (by simp)]; exact hI.inW hL (by simp) (by omega))
    (by rw [ha _ (by simp)]; exact hI.inW hL (by simp) (by omega))) fun s' ⟨⟨hm, hc', hz⟩, hk⟩ =>
      ⟨⟨?_, hc', hz, trivial⟩, hk⟩
  rw [hm, ha _ (by simp), ha _ (by simp), ha _ (by simp), hI.read hL (by simp) (by omega)]
  rfl

theorem p2r_correct :
    ∃ t s', Exec isa power2Round s₀ t s' ∧ abiPreserved s₀ s' ∧ power2RoundK.post s₀ s' := by
  obtain ⟨t, s', he, hI, hk⟩ := WP.keep [.rax, .rcx, .r8, .r9] (p2r_loop hp) (by decide)
  have hr : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2.2.2.2.2.2
  refine ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hI.frame ?_), ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq]
    exact ⟨hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1⟩
  · refine natPolyIs_of_toNat fun k hk => ?_
    rw [hI.done .rsi (by simp) k (by omega) hk, map_get _ _ hk, p2rV, ite_eq_left_of_eq_true _ _ (eq_true rfl), t1V_toNat (hr k hk),
      power2Round_eq, ← polyAt_val hr hk]
    exact (Int.toNat_natCast _).symm
  · refine polyIs_of_toNat fun k hk => ?_
    rw [hI.done .rdx (by simp) k (by omega) hk, map_get _ _ hk, p2rV, ite_eq_right_of_eq_false _ _ (eq_false (by decide)), t0V_toNat (hr k hk),
      power2Round_t0, polyAt_val hr hk]

end

theorem p2r_ct : ConstantTime isa power2RoundK.pre power2RoundK.pub power2Round :=
  VG.Taint.constantTime (A := X86_64.taint) (regsLo [.rdi, .rsi, .rdx, .rsp] [])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]) fun _ h => by cases h)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def p2rSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]

theorem power2Round_verified :
    Verified X86_64.target power2Round (power2RoundContract X86_64.abi) :=
  Verified.of_correct (fun _ hp => p2r_correct hp) p2r_ct (by
    round_implies [power2RoundContract, power2RoundSig, power2RoundK, X86_64.abi, X86_64.argRegs] [p2rSat]
      using p2rSat)

end VG.Proof.MlDsa.X86_64.Round
