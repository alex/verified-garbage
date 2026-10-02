import VerifiedGarbage.Proof.Pbkdf2.X86_64.Iterate
import VerifiedGarbage.Proof.Hmac.Generic.Implies

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on x86-64: constant time

This holds for any compression function (`CalleeOk`), so it is proven once
for every implementation. The taint analysis cannot prove it without
looking into the compression function: it saves and restores our registers
in memory it also writes secrets to, so across a call the analysis forgets
that our pointers are public. So we relate two runs (`RelCT`): at every
point, correctness determines our registers from the public arguments
alone, so they agree; between the calls, the taint analysis proves each
block constant time from that (`Checks`, evaluated for each hash function,
since the code depends on its sizes); and the calls are constant time by
the compression function's own proof (`compressAt_rel`).
-/

namespace VG.Proof.Pbkdf2.X86_64

open VG VG.X86_64
open VG.Impl.MdStream.X86_64 (Params restore compressAt)
open VG.Impl.Pbkdf2.X86_64 (loadKey xorW compressBlock body prologue iterate)
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.X86_64 (Shape CalleeOk compressAt_rel wp_mov)
open VG.Spec.Sha256 (bytesAt)
open VG.Spec.Hmac (StreamingHash)

/-- The registers the blocks between the calls use. -/
abbrev regsS : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp, .r14]

/-- The taint checks of the pieces of `iterate` between its calls, which
depend on the hash function's sizes, its length field and its digest. -/
structure Checks (P : Params) (D : Nat) : Prop where
  pro : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi, .rcx, .r8, .rsp]) (.block (prologue P D)) hc).isSome = true
  load : ∃ hc, (taint.check (Taint.ofRegs regsS) (.block (loadKey P 0)) hc).isSome = true
  arg : ∃ hc, (taint.check (Taint.ofRegs regsS) (.block [.mov .rsi (.reg .rbp)]) hc).isSome = true
  mid : ∃ hc, (taint.check (Taint.ofRegs regsS)
    (.block (Impl.Pbkdf2.X86_64.digest P D ++ loadKey P (P.N + P.B))) hc).isSome = true
  fin : ∃ hc, (taint.check (Taint.ofRegs regsS) (.block (Impl.Pbkdf2.X86_64.digest P D ++
    (List.range (D / 4)).flatMap xorW ++ [.alu .sub .r14 (.imm 1)])) hc).isSome = true
  epi : ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block (restore P)) hc).isSome = true
  ite : ∃ hc, (taint.check (Taint.ofRegs []) (.block []) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : (s₀.gpr .rdx).setWidth 32 = (s₀'.gpr .rdx).setWidth 32
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

theorem PubEq.nn {s₀ s₀' : State} (hq : PubEq s₀ s₀') : nn s₀ = nn s₀' :=
  congrArg BitVec.toNat hq.rdx

/-- The state during a step, with `v` in `r14`. -/
structure St (P : Params) (D W : Nat) (H : Md P.B P.N P.L) (s₀ : State) (v : Addr) (s : State) : Prop
    extends Regs P D W s₀ s where
  r14 : s.gpr .r14 = v
  pad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D

section
variable {P : Params} {D W : Nat} {H : Md P.B P.N P.L}

/-- The registers the blocks use agree in two runs. -/
theorem St.agree {s₀ s₀' : State} (hq : PubEq s₀ s₀') {v : Addr} {s s' : State} (h : St P D W H s₀ v s)
    (h' : St P D W H s₀' v s') : ∀ r ∈ regsS, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, hv, hv, scr, scr, hq.r8]
  · rw [h.rbp, h'.rbp, blk, blk, scr, scr, hq.r8]
  · rw [h.r12, h'.r12, key, key, hq.rdi]
  · rw [h.r13, h'.r13, tp, tp, hq.rcx]
  · rw [h.r15, h'.r15, scr, scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]
  · rw [h.r14, h'.r14]

theorem St.of_inv {s₀ : State} {r : Nat} {s : State} (h : Inv P D W H s₀ (r + 1) s) :
    St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s :=
  ⟨h.toRegs, h.r14, h.pad⟩

variable (hz : Sizes P D W) {s₀ : State} (hp : Pre P D W s₀) {v : Addr}
include hz hp

/-! ## What each piece of a step does, in one run -/

theorem load_st (hR : H.Reloc) {o : Nat} (ho : o + P.N ≤ 2 * (P.N + P.B)) {s : State} (h : St P D W H s₀ v s) :
    WP isa (.block (loadKey P o)) s (St P D W H s₀ v) := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL
  rw [← List.append_nil (loadKey P o)]
  exact load_ok hz hp hR h.toRegs ho fun s' g rd wr f _ => WP.block_nil
    ⟨h.toRegs.write (fun r hr _ _ _ _ _ => g r hr) rd wr (frame_scr (a := P.so + 48) (by omega) f),
      (g _ (by decide)).trans h.r14,
      (Memory.frame_bytesAt f (fun r hr => blk_disj hz hp (by omega) r (by simp at hr; simp [hr])) (by omega)).trans
        h.pad⟩

theorem cmp_st {name : String} {code : Prog isa} (hf : CalleeOk H code) {s : State} (h : St P D W H s₀ v s) :
    WP isa (compressBlock name code) s (St P D W H s₀ v) := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL
  exact cmp_ok hz hp hf h.toRegs fun s' h' r14 f _ =>
    ⟨h', r14.trans h.r14, (Memory.frame_bytesAt f (blk_disj hz hp (by omega)) (by omega)).trans h.pad⟩

theorem mid_st (hs : Shape H) (hR : H.Reloc) {s : State} (h : St P D W H s₀ v s) :
    WP isa (.block (Impl.Pbkdf2.X86_64.digest P D ++ loadKey P (P.N + P.B))) s (St P D W H s₀ v) := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.NL
  refine digest_ok hz hp hs h.toRegs h.pad fun s' g rd wr f _ p => ?_
  exact load_st hz hp hR (by omega)
    ⟨h.toRegs.write (fun r hr _ _ _ _ _ => g r hr) rd wr (frame_scr (a := P.so + 48 + P.N) (by omega) f),
      (g _ (by decide)).trans h.r14, p⟩

/-! ## Two runs -/

variable {s₀' : State} (hp' : Pre P D W s₀') (hq : PubEq s₀ s₀')
include hp' hq

theorem cmp_rel {name : String} {code : Prog isa} (hf : CalleeOk H code) (hc : Checks P D) :
    RelCT isa (fun s s' => St P D W H s₀ v s ∧ St P D W H s₀' v s') (compressBlock name code) fun s s' =>
      St P D W H s₀ v s ∧ St P D W H s₀' v s' := by
  obtain ⟨_, ha⟩ := hc.arg
  have su : RelCT isa (fun s s' => St P D W H s₀ v s ∧ St P D W H s₀' v s') (.block [.mov .rsi (.reg .rbp)])
      fun s s' => (St P D W H s₀ v s ∧ s.gpr .rsi = blk P s₀) ∧ (St P D W H s₀' v s' ∧ s'.gpr .rsi = blk P s₀') :=
    ((RelCT.taint (A := taint) (Taint.ofRegs regsS) (fun _ _ h => Taint.agree_ofRegs (St.agree hq h.1 h.2)) ha).wp
      fun _ _ h => ⟨wp_mov fun s₁ u₁ _ _ => WP.block_nil ⟨⟨h.1.toRegs.write
          (fun r _ _ _ hr _ _ => u₁.other r hr) u₁.rd u₁.wr (by rw [u₁.mem]; exact Frame.refl _ _),
          (u₁.other _ (by decide)).trans h.1.r14, by rw [u₁.mem]; exact h.1.pad⟩, by rw [u₁.gpr, h.1.rbp]⟩,
        wp_mov fun s₁ u₁ _ _ => WP.block_nil ⟨⟨h.2.toRegs.write
          (fun r _ _ _ hr _ _ => u₁.other r hr) u₁.rd u₁.wr (by rw [u₁.mem]; exact Frame.refl _ _),
          (u₁.other _ (by decide)).trans h.2.r14, by rw [u₁.mem]; exact h.2.pad⟩, by rw [u₁.gpr, h.2.rbp]⟩⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have call := compressAt_rel H hf (name := name)
    (P' := fun s s' => (St P D W H s₀ v s ∧ s.gpr .rsi = blk P s₀) ∧ (St P D W H s₀' v s' ∧ s'.gpr .rsi = blk P s₀'))
    fun s s' ⟨⟨h, hsi⟩, ⟨h', hsi'⟩⟩ => by
      have ag := St.agree hq h h'
      exact ⟨⟨_, _, _, callOk_of hz hp h.toRegs hsi⟩, ⟨_, _, _, callOk_of hz hp' h'.toRegs hsi'⟩,
        ag _ (by simp), ag _ (by simp), by rw [hsi, hsi', blk, blk, scr, scr, hq.r8], ag _ (by simp)⟩
  exact ((su.seq call).wp fun _ _ h => ⟨cmp_st hz hp hf h.1, cmp_st hz hp' hf h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem body_rel (hs : Shape H) (hR : H.Reloc) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hc : Checks P D) {r : Nat} :
    RelCT isa (fun s s' => Inv P D W H s₀ (r + 1) s ∧ Inv P D W H s₀' (r + 1) s') (body P D name code)
      fun s s' => (eval .ne s = some (r != 0) ∧ Inv P D W H s₀ r s) ∧
        (eval .ne s' = some (r != 0) ∧ Inv P D W H s₀' r s') := by
  have := so_le hz; have := N_le hz; have := B_le hz
  obtain ⟨_, hl⟩ := hc.load
  obtain ⟨_, hm⟩ := hc.mid
  obtain ⟨_, hfi⟩ := hc.fin
  have l0 : RelCT isa (fun s s' => Inv P D W H s₀ (r + 1) s ∧ Inv P D W H s₀' (r + 1) s') (.block (loadKey P 0))
      fun s s' => St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧ St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs regsS) (fun _ _ h =>
      Taint.agree_ofRegs (St.agree hq (St.of_inv h.1) (St.of_inv h.2))) hl).wp
      fun _ _ h => ⟨load_st hz hp hR (by omega) (St.of_inv h.1), load_st hz hp' hR (by omega) (St.of_inv h.2)⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have dl : RelCT isa (fun s s' => St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧
        St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s')
      (.block (Impl.Pbkdf2.X86_64.digest P D ++ loadKey P (P.N + P.B)))
      fun s s' => St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧ St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs regsS) (fun _ _ h => Taint.agree_ofRegs (St.agree hq h.1 h.2))
      hm).wp fun _ _ h => ⟨mid_st hz hp hs hR h.1, mid_st hz hp' hs hR h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have fin : RelCT isa (fun s s' => St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧
        St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s')
      (.block (Impl.Pbkdf2.X86_64.digest P D ++ (List.range (D / 4)).flatMap xorW ++ [.alu .sub .r14 (.imm 1)]))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs regsS) (fun _ _ h => Taint.agree_ofRegs (St.agree hq h.1 h.2)) hfi
  have c := cmp_rel hz hp hp' hq (v := BitVec.ofNat 64 (r + 1)) hf hc (name := name)
  exact ((l0.seq (c.seq (dl.seq (c.seq fin)))).wp fun _ _ h =>
    ⟨body_ok hz hp hs hR hf h.1, body_ok hz hp' hs hR hf h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem loop_rel (hs : Shape H) (hR : H.Reloc) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hc : Checks P D) {n : Nat} :
    RelCT isa (fun s s' => Inv P D W H s₀ (n + 1) s ∧ Inv P D W H s₀' (n + 1) s') (.loop (body P D name code) .ne)
      fun _ _ => True :=
  RelCT.loop (M := isa) (body := body P D name code) (c := .ne) (Q := fun _ _ => True)
    (fun m s s' => Inv P D W H s₀ (m + 1) s ∧ Inv P D W H s₀' (m + 1) s') (fun m => by
      intro s s' t t' u u' h e e'
      obtain ⟨ht, ⟨z, i⟩, ⟨z', i'⟩⟩ := body_rel hz hp hp' hq hs hR hf hc _ _ _ _ _ _ h e e'
      refine ⟨ht, z.trans z'.symm, fun _ => trivial, fun hc' => ?_⟩
      have hc'' : some (m != 0) = some true := z.symm.trans hc'
      cases m with
      | zero => cases hc''
      | succ m => exact ⟨m, by omega, i, i'⟩) n

theorem iterate_rel {S : StreamingHash} {iv : H.HV} (ho : HashOk P D W S H iv) {name : String}
    {code : Prog isa} (hf : CalleeOk H code) (hc : Checks P D) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (iterate P D name code) fun _ _ => True := by
  obtain ⟨_, hpr⟩ := hc.pro
  obtain ⟨_, hep⟩ := hc.epi
  obtain ⟨_, hit⟩ := hc.ite
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block (prologue P D)) fun s s' =>
      (Inv P D W H s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0))) ∧
      (Inv P D W H s₀' (nn s₀') s' ∧ s'.zf = some (decide (nn s₀' = 0))) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rcx, .r8, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hpr).wp
      fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hz hp ho.shape ho.lenOk, prologue_ok hz hp' ho.shape ho.lenOk⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have br : RelCT isa (fun s s' =>
        (Inv P D W H s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0))) ∧
        (Inv P D W H s₀' (nn s₀') s' ∧ s'.zf = some (decide (nn s₀' = 0))))
      (.ite .e (.block []) (.loop (body P D name code) .ne))
      fun s s' => Inv P D W H s₀ 0 s ∧ Inv P D W H s₀' 0 s' := by
    refine (RelCT.ite (fun s s' h => ?_) (RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by simp)) hit) ?_).wp
      (fun _ _ h => ⟨loop_ok hz hp ho.shape ho.reloc hf h.1.1 h.1.2,
        loop_ok hz hp' ho.shape ho.reloc hf h.2.1 h.2.2⟩) |>.mono (fun _ _ h => h) fun _ _ h => h.2
    · show s.zf = s'.zf
      rw [h.1.2, h.2.2, hq.nn]
    · intro s s' t t' u u' ⟨⟨⟨i, z⟩, ⟨i', _⟩⟩, hc'⟩ e e'
      have hc'' : some (decide (nn s₀ = 0)) = some false := z.symm.trans hc'
      have hne : nn s₀ ≠ 0 := fun h0 => by rw [h0] at hc''; cases hc''
      obtain ⟨m, hm⟩ : ∃ m, nn s₀ = m + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hne).symm⟩
      rw [hm] at i
      rw [← hq.nn, hm] at i'
      exact loop_rel hz hp hp' hq ho.shape ho.reloc hf hc _ _ _ _ _ _ ⟨i, i'⟩ e e'
  have epi : RelCT isa (fun s s' => Inv P D W H s₀ 0 s ∧ Inv P D W H s₀' 0 s') (.block (restore P))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r15]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.r15, h.2.r15, scr, scr, hq.r8]) hep
  exact pro.seq (br.seq epi)

end

/-! ## Verified -/

theorem pubEq_of {S : StreamingHash} {W : Nat} {s₁ s₂ : State} (h : (iterK S W).pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- `iterate` is verified against `iterK`, for any hash function the proof
supports (`HashOk`), whose pieces of code the taint analysis accepts
(`Checks`), and any compression function (`CalleeOk`), if it never loads
MXCSR. -/
theorem verified {P : Params} {D W : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : HashOk P D W S H iv) (hc : Checks P D) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hm : (iterate P D name code).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, (iterK S W).pre s) :
    Verified X86_64.target (iterate P D name code) (iterK S W) := by
  refine ⟨iterate_ok ho hf hm, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  exact (iterate_rel ho.sizes (pre_of ho.link.hS ho.link.hD h₁) (pre_of ho.link.hS ho.link.hD h₂)
    (pubEq_of hpub) ho hf hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- `iterK` implies the shared contract, for any hash function and scratch
space, given that the shared contract is satisfiable. -/
theorem iterImp (S : StreamingHash) (W : Nat) (h : ∃ s, (Spec.Pbkdf2.iterateContract S W X86_64.abi 8).pre s) :
    (iterK S W).Implies (Spec.Pbkdf2.iterateContract S W X86_64.abi 8) := by
  generic_implies [
    Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, iterK, X86_64.abi, X86_64.argRegs] using h

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes and `8 W` bytes of scratch space. -/
def iterSat (S D W : Nat) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rcx => 0x30000 | .r8 => 0x40000
    | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x10000, 2 * S⟩, ⟨0x20000, D⟩]
  wr := [⟨0x30000, D⟩, ⟨0x40000, 8 * W⟩]

end VG.Proof.Pbkdf2.X86_64
