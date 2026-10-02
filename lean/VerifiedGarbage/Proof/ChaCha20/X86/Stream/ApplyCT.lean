import VerifiedGarbage.Proof.ChaCha20.X86.Stream.Apply
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-!
# Streaming ChaCha20 on x86 (32-bit): `apply`, constant time

Untrusted: everything here is checked by Lean. As on the other targets, two
runs from states that agree on `esp`, the arguments and the number of bytes
of keystream left (which the contract lets `apply` leak) are related piece
by piece (`RelCT`): the taint analysis proves each piece without calls
constant time from the registers that hold public values (`taintRel`), which
correctness determines in each run (`Apply.lean`) from those public values;
the calls of the block function and of `vg_chacha20_xor`, each in a frame of
its arguments, are constant time by their own proofs (`RelCT.callWith`),
their arguments agreeing; and the branches are on public values
(`RelCT.ite`). The argument slots may be written, so the taint analysis does
not take the arguments from them: the state pointer is loaded in a piece of
its own, whose result correctness determines.
-/

namespace VG.Proof.ChaCha20.X86.Stream

open VG VG.X86 VG.Impl.ChaCha20.X86.Stream
open VG.Impl.ChaCha20.X86 (at_)
open VG.Spec.ChaCha20 (stateAt)

/-- Code the taint analysis proves constant time from the registers `rs`. -/
theorem taintRel {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint sseTaint.T}
    (h : (sseTaint.check (τr rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := sseTaint) (τr rs) (fun x y hp => agree_regs (hr x y hp)) h

/-- What each run satisfies by correctness holds of the final states. -/
theorem RelCT.post {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x F₁ ∧ WP isa c y F₂) :
    RelCT isa P c fun x y => F₁ x ∧ F₂ y :=
  RelCT.mono (RelCT.wp h hw) (fun _ _ h => h) fun _ _ h => h.2

/-- Two entry states that agree on what is public. -/
structure Two (a b : State) : Prop where
  pa : APre a
  pb : APre b
  hesp : E a = E b
  hst : ST a = ST b
  hdp : DP a = DP b
  hln : LN a = LN b
  hleft : N a = N b

theorem Two.eqL {a b : State} (h : Two a b) : L a = L b := by
  show (LN a).toNat = (LN b).toNat; rw [h.hln]
theorem Two.eqO {a b : State} (h : Two a b) : O a = O b := by
  show N a % 64 = N b % 64; rw [h.hleft]
theorem Two.eqH {a b : State} (h : Two a b) : H a = H b := by
  show min (N a % 64) (L a) = min (N b % 64) (L b); rw [h.hleft, h.eqL]
theorem Two.eqNB {a b : State} (h : Two a b) : NB a = NB b := by
  show (L a - H a) / 64 = (L b - H b) / 64; rw [h.eqH, h.eqL]
theorem Two.eqT {a b : State} (h : Two a b) : T a = T b := by
  show (L a - H a) % 64 = (L b - H b) % 64; rw [h.eqH, h.eqL]
theorem Two.st64 {a b : State} (h : Two a b) : st a = st b := by simp only [st, h.hst]

/-- The callee's public data: `esp` and the arguments, which are the
registers pushed. -/
theorem entry_pub {rs : List Reg} {x y : State} (rd wr : List Region) (hrs : Reg.esp ∉ rs)
    (hfit : 4 * rs.length + 4 ≤ (x.gpr .esp).toNat) (hsp : x.gpr .esp = y.gpr .esp)
    (hr : ∀ r ∈ rs, x.gpr r = y.gpr r) :
    ((pushed rs x).callEntry.withRegions rd wr).gpr .esp = ((pushed rs y).callEntry.withRegions rd wr).gpr .esp ∧
    ∀ i < rs.length, arg ((pushed rs x).callEntry.withRegions rd wr) i =
      arg ((pushed rs y).callEntry.withRegions rd wr) i :=
  ⟨by simp only [State.withRegions_gpr, callEntry_esp', hsp],
   fun i hi => by simp only [arg_withRegions]; exact callEntry_arg_eq hrs hfit hsp hr hi⟩

/-- The arguments of the call of the block function, and the registers the
rest uses. -/
structure TArgs (s₀ s : State) : Prop where
  eax : s.gpr .eax = ST s₀ + BitVec.ofNat 32 64
  ebx : s.gpr .ebx = ST s₀
  esi : s.gpr .esi = DP s₀ + BitVec.ofNat 32 (H s₀ + 64 * NB s₀)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (T s₀)
  at_ : At s₀ s

theorem tailArgs_ok {s₀ : State} {s : State} (h : Q2 s₀ s) : WP isa (.block (ptr .eax .ebx 64)) s (TArgs s₀) :=
  WP.mono (tailPtr_ok h) fun _ ⟨eax₁, k₁, _, rd₁, wr₁⟩ =>
    ⟨eax₁, by rw [k₁ _ (by decide), h.ebx], by rw [k₁ _ (by decide), h.esi], by rw [k₁ _ (by decide), h.ebp],
      ⟨by rw [k₁ _ (by decide), h.esp], by rw [rd₁, h.rd], by rw [wr₁, h.wr]⟩⟩

/-- After the block function: the registers the rest uses. -/
structure TAfter (s₀ s : State) : Prop where
  ebx : s.gpr .ebx = ST s₀
  esi : s.gpr .esi = DP s₀ + BitVec.ofNat 32 (H s₀ + 64 * NB s₀)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (T s₀)
  esp : s.gpr .esp = E s₀

theorem TArgs.call {s₀ s : State} (hp : APre s₀) (h : TArgs s₀ s) : WP isa callBlock s (TAfter s₀) :=
  block_call hp h.at_ h.ebx h.eax fun _ at' cs _ _ =>
    ⟨by rw [cs .ebx (by simp [calleeSaved]), h.ebx], by rw [cs .esi (by simp [calleeSaved]), h.esi],
      by rw [cs .ebp (by simp [calleeSaved]), h.ebp], at'.esp⟩

section
variable {a b : State} (h : Two a b)
include h

theorem load_rel : RelCT isa (fun x y => x = a ∧ y = b) (.block [.mov .eax (.mem (at_ .esp 4))])
    fun x y => x = a.setReg .eax (ST a) ∧ y = b.setReg .eax (ST b) :=
  RelCT.post (taintRel [.esp] (fun x y ⟨hx, hy⟩ r hr => by
      subst hx hy
      simp only [List.mem_singleton] at hr; subst hr; exact h.hesp) (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨by subst hx; exact load_ok h.pa, by subst hy; exact load_ok h.pb⟩

theorem check_rel : RelCT isa (fun x y => x = a.setReg .eax (ST a) ∧ y = b.setReg .eax (ST b)) (.block check)
    fun x y => Q0 a x ∧ Q0 b y :=
  RelCT.post (taintRel [.eax, .esp] (fun x y ⟨hx, hy⟩ r hr => by
      subst hx hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [RegUpd.gpr_setReg_self, h.hst]
      · simp only [RegUpd.gpr_setReg_of_ne _ _ (show Reg.esp ≠ .eax by decide)]; exact h.hesp)
      (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨by subst hx; exact check_ok h.pa, by subst hy; exact check_ok h.pb⟩

theorem part1_rel (hle : L a ≤ N a) :
    RelCT isa (fun x y => Q0 a x ∧ Q0 b y) part1 fun x y => Q1 a x ∧ Q1 b y := by
  have hle' : L b ≤ N b := by rw [← h.eqL, ← h.hleft]; exact hle
  rw [part1_eq]
  refine RelCT.seq (R := fun (x y : State) => (R1 a (L a) x ∧ x.cf = some (decide (O a < L a))) ∧
      (R1 b (L b) y ∧ y.cf = some (decide (O b < L b))))
    (RelCT.post (taintRel [.eax, .esp] (fun x y ⟨hx, hy⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hx.eax, hy.eax, h.hst]
        · rw [hx.keep _ (by decide) (by decide) (by decide), hy.keep _ (by decide) (by decide) (by decide)]
          exact h.hesp) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨start_ok h.pa hle hx, start_ok h.pb hle' hy⟩) ?_
  refine RelCT.seq (R := fun x y => R1 a (H a) x ∧ R1 b (H b) y)
    (RelCT.post (RelCT.ite (fun x y ⟨⟨_, cx⟩, ⟨_, cy⟩⟩ => by
        show eval .b x = eval .b y; simp only [eval, cx, cy, h.eqO, h.eqL])
      (taintRel [] (fun _ _ _ r hr => by simp at hr) (by taint_decide))
      (taintRel [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)))
      fun x y ⟨⟨hx, cx⟩, ⟨hy, cy⟩⟩ => ⟨sel_ok hx cx, sel_ok hy cy⟩) ?_
  exact RelCT.post (taintRel [.ebx, .eax, .ecx, .esi, .ebp, .esp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hx.ebx, hy.ebx, h.hst]
      · rw [hx.eax, hy.eax, h.eqO]
      · rw [hx.ecx, hy.ecx, h.eqH]
      · rw [hx.esi, hy.esi, h.hdp]
      · rw [hx.ebp, hy.ebp, h.hln]
      · rw [hx.esp, hy.esp, h.hesp]) (by taint_decide))
    fun x y ⟨hx, hy⟩ => ⟨rest1_ok h.pa hx, rest1_ok h.pb hy⟩

theorem xor_rel (hnb : 0 < NB a) : RelCT isa (fun x y => Args a x ∧ Args b y) callXor fun _ _ => True := by
  have ew : wrXor b = wrXor a := by
    simp only [wrXor, cpR, blR, wkR, st, dp, E, h.hst, h.hdp, h.eqH, h.eqNB, h.hesp]
  refine RelCT.callWith Proof.ChaCha20.X86.Xor.xor_correct Proof.ChaCha20.X86.Xor.xor_ct [] (wrXor a)
    fun x y ⟨hx, hy⟩ => ?_
  have px := xor_pre h.pa ⟨hx.esp, hx.rd, hx.wr⟩ hnb hx.edx hx.esi hx.ecx hx.eax
  have py := xor_pre h.pb ⟨hy.esp, hy.rd, hy.wr⟩ (by rw [← h.eqNB]; exact hnb) hy.edx hy.esi hy.ecx hy.eax
  rw [ew] at py
  have fit := (At.fit h.pa ⟨hx.esp, hx.rd, hx.wr⟩ (rs := [.eax, .ecx, .esi, .edx]) (by decide))
  have hsp : x.gpr .esp = y.gpr .esp := by rw [hx.esp, hy.esp, h.hesp]
  have p := entry_pub [] (wrXor a) (by decide) fit hsp (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [hx.eax, hy.eax, h.hst]
    · rw [hx.ecx, hy.ecx, h.eqNB]
    · rw [hx.esi, hy.esi, h.hdp, h.eqH]
    · rw [hx.edx, hy.edx, h.hst])
  exact ⟨px, py, hsp, p.1, fun i hi => p.2 i hi⟩

theorem part2_rel : RelCT isa (fun x y => Q1 a x ∧ Q1 b y) part2 fun x y => Q2 a x ∧ Q2 b y := by
  refine RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨part2_ok h.pa hx, part2_ok h.pb hy⟩
  rw [part2_eq]
  refine RelCT.ite (fun x y ⟨hx, hy⟩ => by show eval .e x = eval .e y; simp only [eval, hx.zf, hy.zf, h.eqNB])
    (taintRel [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_
  by_cases h0 : 64 * NB a = 0
  · exact RelCT.of_false fun x y ⟨⟨hx, _⟩, he⟩ => by
      simp only [show eval .e x = x.zf from rfl, hx.zf, h0, decide_true] at he
      exact absurd he (by decide)
  refine RelCT.seq (R := fun x y => Args a x ∧ Args b y) ?_
    (RelCT.seq (xor_rel h (by omega)) (taintRel [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)))
  exact RelCT.post (taintRel [.ebx, .ecx, .esp] (fun x y ⟨⟨hx, hy⟩, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hx.ebx, hy.ebx, h.hst]
      · rw [hx.ecx, hy.ecx, h.eqNB]
      · rw [hx.esp, hy.esp, h.hesp]) (by taint_decide))
    fun x y ⟨⟨hx, hy⟩, _⟩ => ⟨WP.mono (args_exec h.pa hx) fun _ h' => h'.2, WP.mono (args_exec h.pb hy) fun _ h' => h'.2⟩

theorem part3_rel : RelCT isa (fun x y => Q2 a x ∧ Q2 b y) part3 fun x y => Q3 a x ∧ Q3 b y := by
  refine RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨part3_ok h.pa hx, part3_ok h.pb hy⟩
  rw [part3_eq]
  refine RelCT.seq (R := fun (x y : State) => (Q2 a x ∧ x.zf = some (decide (T a = 0))) ∧
      (Q2 b y ∧ y.zf = some (decide (T b = 0))))
    (RelCT.post (taintRel [] (fun _ _ _ r hr => by simp at hr) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨test_ok hx, test_ok hy⟩) ?_
  refine RelCT.ite (fun x y ⟨hx, hy⟩ => by show eval .e x = eval .e y; simp only [eval, hx.2, hy.2, h.eqT])
    (taintRel [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_
  refine RelCT.seq (R := fun x y => TArgs a x ∧ TArgs b y)
    (RelCT.post (taintRel [.ebx] (fun x y ⟨⟨hx, hy⟩, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hx.1.ebx, hy.1.ebx, h.hst]) (by taint_decide))
      fun x y ⟨⟨hx, hy⟩, _⟩ => ⟨tailArgs_ok hx.1, tailArgs_ok hy.1⟩) ?_
  refine RelCT.seq (R := fun x y => TAfter a x ∧ TAfter b y) ?_
    (taintRel [.ebx, .esi, .ebp, .esp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hx.ebx, hy.ebx, h.hst]
      · rw [hx.esi, hy.esi, h.hdp, h.eqH, h.eqNB]
      · rw [hx.ebp, hy.ebp, h.eqT]
      · rw [hx.esp, hy.esp, h.hesp]) (by taint_decide))
  have er : rdBlk b = rdBlk a := by simp only [rdBlk, st, E, h.hst, h.hesp]
  have ew : wrBlk b = wrBlk a := by simp only [wrBlk, st, h.hst]
  refine RelCT.post (RelCT.callWith Proof.ChaCha20.X86.block_correct Proof.ChaCha20.X86.block_ct (rdBlk a) (wrBlk a)
    fun x y ⟨hx, hy⟩ => ?_) fun x y ⟨hx, hy⟩ => ⟨hx.call h.pa, hy.call h.pb⟩
  have py := block_pre h.pb hy.at_ hy.ebx hy.eax
  rw [er, ew] at py
  have fit := hx.at_.fit h.pa (rs := [.eax, .ebx]) (by decide)
  have hsp : x.gpr .esp = y.gpr .esp := by rw [hx.at_.esp, hy.at_.esp, h.hesp]
  have p := entry_pub (rdBlk a) (wrBlk a) (by decide) fit hsp (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx.eax, hy.eax, h.hst]
    · rw [hx.ebx, hy.ebx, h.hst])
  exact ⟨block_pre h.pa hx.at_ hx.ebx hx.eax, py, hsp, p.1, p.2 0 (by decide), p.2 1 (by decide)⟩

theorem apply_rel : RelCT isa (fun x y => x = a ∧ y = b) apply fun _ _ => True := by
  rw [apply_eq]
  refine RelCT.seq (load_rel h) (RelCT.seq (check_rel h) (RelCT.ite (fun x y ⟨hx, hy⟩ => by
      show eval .b x = eval .b y; simp only [eval, hx.cf, hy.cf, h.hleft, h.eqL])
    (taintRel [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)) ?_))
  by_cases hlt : N a < L a
  · exact RelCT.of_false fun x y ⟨⟨hx, _⟩, he⟩ => by
      simp only [show eval .b x = x.cf from rfl, hx.cf, hlt, decide_true] at he
      exact absurd he (by decide)
  have hle : L a ≤ N a := by omega
  refine RelCT.seq (RelCT.mono (part1_rel h hle) (fun _ _ hp => hp.1) fun _ _ hq => hq)
    (RelCT.seq (part2_rel h) (RelCT.seq (part3_rel h) ?_))
  exact taintRel [.ebx] (fun x y ⟨hx, hy⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [hx.ebx, hy.ebx, h.hst]) (by taint_decide)

end

theorem Two.of {a b : State} (ha : Proof.ChaCha20.applyX86.pre a) (hb : Proof.ChaCha20.applyX86.pre b)
    (hq : Proof.ChaCha20.applyX86.pub a b) : Two a b := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hq
  exact ⟨APre.of a ha, APre.of b hb, p1, p2, p3, p4, (List.cons.inj p5).1⟩

theorem apply_ct : ConstantTime isa Proof.ChaCha20.applyX86.pre Proof.ChaCha20.applyX86.pub apply :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (apply_rel (Two.of h₁ h₂ hq) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem apply_ok (s : State) (hs : Proof.ChaCha20.applyX86.pre s) :
    ∃ t s', Exec isa apply s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.applyX86.post s s' := by
  obtain ⟨t, s', he, hf⟩ := apply_correct (APre.of s hs)
  exact ⟨t, s', he, hf.1, hf.2⟩

/-- The 32-bit result, as the ABI returns it in `edx:eax`. -/
theorem ret_eq (x y : BitVec 32) : (x ++ y).setWidth 32 = y := by
  ext i hi
  rw [BitVec.getElem_setWidth, BitVec.getLsbD_append, ite_pos hi, BitVec.getLsbD_eq_getElem hi]

/-- Memory whose argument slots (at `0x4004`) hold `0x1000`, `0x2000` and 0. -/
def applySatMem : Mem := fun a => if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0

/-- A state satisfying the precondition of `apply` (with no data). -/
def applySat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := applySatMem
  rd := []
  wr := [⟨0x1000, 768⟩, ⟨0x2000, 0⟩, ⟨0x4004, 12⟩]

theorem apply_verified : Verified X86.target apply (Spec.ChaCha20.applyContract X86.abi 32) :=
  Verified.of_correct apply_ok apply_ct (by
    have a0 : arg applySat 0 = 0x1000 := by decide
    have a1 : arg applySat 1 = 0x2000 := by decide
    have a2 : arg applySat 2 = 0 := by decide
    have e : argAddr applySat 0 = 0x4004 := by decide
    have esp : applySat.gpr .esp = 0x4000 := rfl
    sig_implies [Spec.ChaCha20.applyContract, Spec.ChaCha20.applySig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, Proof.ChaCha20.applyX86, ret_eq] [a0, a1, a2, e, esp] using applySat)

end VG.Proof.ChaCha20.X86.Stream
