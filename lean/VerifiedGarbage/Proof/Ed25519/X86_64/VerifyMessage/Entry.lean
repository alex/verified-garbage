import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.Args

/-! Entry contract and stack frame of complete Ed25519 verification. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage
open VG VG.X86_64

/-- The disjoint scratch allocation leaves room for the hash's 64-byte prefix. -/
theorem Lay.Ok.message_bound {L : Lay} (h : L.Ok) : 64 + L.len.toNat < 2 ^ 64 := by
  have hd := h.sc L.MSG (by simp [Lay.inputs])
  have nm := h.nm
  have nc := h.nc
  by_cases hz : L.len.toNat = 0
  · omega
  by_cases hp : L.msg ≤ L.scr
  · have hn : ¬ L.MSG.Contains L.scr 1 := fun hx => hd _ hx (by simp [Region.Contains])
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp] at hn
    have hp' : L.msg.toNat ≤ L.scr.toNat := hp
    omega
  · have hp' : L.scr ≤ L.msg := by
      change L.scr.toNat ≤ L.msg.toNat
      change ¬ L.msg.toNat ≤ L.scr.toNat at hp
      omega
    have hn : ¬ L.SCR.Contains L.msg 1 := fun hx => hd _ (by simp [Region.Contains]; omega) hx
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp'] at hn
    have hp'' : L.scr.toNat ≤ L.msg.toNat := hp'
    omega

def verifyMessageLocal : Contract isa where
  pre s := 184 ≤ (s.gpr .rsp).toNat ∧
    s.rd = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 64⟩] ∧
    s.wr = [⟨s.gpr .r8, 8192⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .r8, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩ ⟨s.gpr .r8, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, 64⟩ ⟨s.gpr .r8, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 64⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .r8, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 184, 184⟩ ⟨s.gpr .rdi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 184, 184⟩ ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 184, 184⟩ ⟨s.gpr .rcx, 64⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 184, 184⟩ ⟨s.gpr .r8, 8192⟩ ∧
    (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64
  post s t := t.gpr .rax = if Spec.Ed25519.verify
    (Spec.Ed25519.bytesAt s.mem (s.gpr .rdi) 32)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .rcx) 64) then 1 else 0
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx ∧
    s.gpr .r8 = t.gpr .r8 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .rdi) 32 = Spec.Ed25519.bytesAt t.mem (t.gpr .rdi) 32 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
      Spec.Ed25519.bytesAt t.mem (t.gpr .rsi) (t.gpr .rdx).toNat ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .rcx) 64 = Spec.Ed25519.bytesAt t.mem (t.gpr .rcx) 64

def lay (s : State) : Lay :=
  ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx, s.gpr .r8, s.gpr .rsp - BitVec.ofNat 64 184⟩

theorem lay_ret (s : State) : (lay s).B + BitVec.ofNat 64 184 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem lay_ok {s : State} (h : verifyMessageLocal.pre s) : (lay s).Ok := by
  obtain ⟨-, -, -, pc, mc, sc, rp, rm, rs, rc, kp, km, ks, kc, np, nm, ns, nc⟩ := h
  have e : (lay s).RET = ⟨s.gpr .rsp, 8⟩ := by simp only [Lay.RET, lay_ret]
  refine ⟨?_, ?_, ?_, kc, e ▸ rc, np, nm, ns, nc⟩
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact pc
    · exact mc
    · exact sc
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact kp
    · exact km
    · exact ks
  · intro r hr
    rw [e]
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact rp
    · exact rm
    · exact rs

def pushRs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8,
    .rax, .rax, .rax, .rax, .rax, .rax, .rax, .rax,
    .rax, .rax, .rax, .rax, .rax, .rax, .rax, .rax]

theorem push_base (sp : Addr) :
    sp - BitVec.ofNat 64 (8 * 21) = sp - BitVec.ofNat 64 184 + BitVec.ofNat 64 16 := by bv_omega

theorem push_slot (sp : Addr) (j : Nat) (hj : j < 5) :
    sp - BitVec.ofNat 64 (8 * (j + 1)) = sp - BitVec.ofNat 64 184 + BitVec.ofNat 64 (176 - 8 * j) := by
  have : 8 * (j + 1) < 2 ^ 64 := by omega
  bv_omega

theorem push_ctx {s : State} (h : verifyMessageLocal.pre s) :
    Ctx (lay s) s.gpr s.mxcsr s.mem (pushed pushRs s) := by
  have hn : 8 * pushRs.length ≤ (s.gpr .rsp).toNat := by show 8 * 21 ≤ _; have := h.1; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s pushRs (by decide) hn
  have hw' : ∀ j (hj : j < 5), (pushed pushRs s).mem.readW
      ((lay s).B + BitVec.ofNat 64 (176 - 8 * j)) 64 = s.gpr (pushRs[j]'(by show j < 21; omega)) := fun j hj => by
    rw [← hw j (by show j < 21; omega)]; simp only [lay]; rw [push_slot _ j hj]; rfl
  refine ⟨by rw [pushed_rd, h.2.1]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr, by rw [pushed_mxcsr],
    hw' 4 (by omega), hw' 3 (by omega), hw' 2 (by omega), hw' 1 (by omega), hw' 0 (by omega), ?_⟩
  · rw [pushed_wr, h.2.2.1]; simp only [show pushRs.length = 21 from rfl, lay]; rw [push_base]
  · rw [pushed_rsp]; simp only [show pushRs.length = 21 from rfl, lay]; rw [push_base]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨(lay s).STK, by simp, ?_⟩
    simp only [show pushRs.length = 21 from rfl]
    rw [push_base]
    exact Offset.sub_base _ (by omega)

end VG.Proof.Ed25519.X86_64.VerifyMessage
