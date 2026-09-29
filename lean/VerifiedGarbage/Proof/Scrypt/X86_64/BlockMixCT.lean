import VerifiedGarbage.Proof.Scrypt.X86_64.BlockMixFun
import VerifiedGarbage.Proof.Scrypt.X86_64.SalsaCall
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import Mathlib.Tactic.DefEqTransformations
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# scryptBlockMix on x86-64: constant time

Untrusted: everything here is checked by Lean.

The taint analysis alone cannot prove this: across a call of
`vg_salsa20_8`, which saves and restores our registers in memory it also
writes secrets to through a pointer of unknown provenance, it forgets that
our pointers are public. So we relate two runs (`RelCT`): at every point,
correctness determines our registers from the public arguments alone, so
they agree; between the calls, the taint analysis proves each block
constant time from that; and the calls are constant time by Salsa20/8's own
proof.
-/

namespace VG.Proof.Scrypt.X86_64.BlockMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.MdStream.X86_64 (Upd wp_mov wp_addi)

/-! ## What each run knows -/

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

/-- The loop's registers during pair `k`, with `rbx = bx`. -/
structure KR (s₀ : State) (k : Nat) (bx : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bx
  rbp : s.gpr .rbp = yE s₀ k
  r12 : s.gpr .r12 = yO s₀ k
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (rr s₀ - k)
  r15 : s.gpr .r15 = xP s₀ k

theorem KR.of_inv {s₀ : State} {k : Nat} {s : State} (h : Inv s₀ k s) : KR s₀ k (bB s₀ k) s :=
  ⟨h.rd, h.wr, h.rsp, h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

theorem KR.keep {s₀ : State} {k : Nat} {bx : Addr} {s s' : State} (h : KR s₀ k bx s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hk : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) :
    KR s₀ k bx s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hk _ (by simp [calleeSaved])).trans h.rsp,
    (hk _ (by simp [calleeSaved])).trans h.rbx, (hk _ (by simp [calleeSaved])).trans h.rbp,
    (hk _ (by simp [calleeSaved])).trans h.r12, (hk _ (by simp [calleeSaved])).trans h.r13,
    (hk _ (by simp [calleeSaved])).trans h.r14, (hk _ (by simp [calleeSaved])).trans h.r15⟩

theorem PubEq.rr {s₀ s₀' : State} (hq : PubEq s₀ s₀') : rr s₀ = rr s₀' := by
  simp only [VG.Proof.Scrypt.X86_64.BlockMix.rr, hq.rsi]

theorem PubEq.xP {s₀ s₀' : State} (hq : PubEq s₀ s₀') (k : Nat) : xP s₀ k = xP s₀' k := by
  cases k <;> simp only [VG.Proof.Scrypt.X86_64.BlockMix.xP, bP, yO, yP, hq.rdi, hq.rdx, hq.rr]

/-- The registers the blocks use agree in two runs. -/
theorem KR.agree {s₀ s₀' : State} (hq : PubEq s₀ s₀') {k : Nat} {bx bx' : Addr} {s s' : State}
    (h : KR s₀ k bx s) (h' : KR s₀' k bx' s') (hbx : bx = bx') :
    ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, hbx]
  · rw [h.rbp, h'.rbp, yE, yE, yP, yP, hq.rdx]
  · rw [h.r12, h'.r12, yO, yO, yP, yP, hq.rdx, hq.rr]
  · rw [h.r13, h'.r13, sc, sc, hq.r8]
  · rw [h.r14, h'.r14, hq.rr]
  · rw [h.r15, h'.r15, hq.xP]
  · rw [h.rsp, h'.rsp, hq.rsp]

/-! ## What each piece of the loop body does to the registers -/

section
variable {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀)
include hp hk

theorem xor1_wp {s : State} (h : KR s₀ k (bB s₀ k) s) :
    WP isa (.block (xor64 .rbp .r15 .rbx)) s (KR s₀ k (bB s₀ k)) := by
  have lt := r_lt hp
  have hrd : s.rd = [bR s₀] := h.rd.trans hp.rd
  have hwr : s.wr = [yR s₀, scR s₀] := h.wr.trans hp.wr
  rw [← List.append_nil (xor64 .rbp .r15 .rbx)]
  refine xor64_full (d := yE s₀ k) (x := xP s₀ k) (y := bB s₀ k) (by decide) (by decide)
    (by decide) (xP_disj hp hk) (yb_disj hp (by omega) (by omega)) h.rbp h.r15 h.rbx
    (xP_in hp hk hrd hwr)
    (fun i hi => by
      rw [hrd, hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_b hp (by omega)))
    (fun i hi => by
      rw [hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    fun _ g₁ rd₁ wr₁ _ => WP.block_nil (h.keep rd₁ wr₁ fun r hr => g₁ r (calleeSaved_ne_rax hr))

theorem xor2_wp {s : State} (h : KR s₀ k (bB s₀ k) s) :
    WP isa (.block (.alu .add .rbx (.imm 64) :: xor64 .r12 .rbp .rbx)) s
      (KR s₀ k (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)))) := by
  have lt := r_lt hp
  refine wp_addi fun s₃ u₃ => ?_
  have hrd : s₃.rd = [bR s₀] := u₃.rd.trans (h.rd.trans hp.rd)
  have hwr : s₃.wr = [yR s₀, scR s₀] := u₃.wr.trans (h.wr.trans hp.wr)
  have e3bx : s₃.gpr .rbx = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)) := by
    rw [u₃.gpr, h.rbx, sx64, add_ofNat]; congr 2; omega
  have h₃ : KR s₀ k (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) s₃ :=
    ⟨u₃.rd.trans h.rd, u₃.wr.trans h.wr, (u₃.other _ (by decide)).trans h.rsp, e3bx,
      (u₃.other _ (by decide)).trans h.rbp, (u₃.other _ (by decide)).trans h.r12,
      (u₃.other _ (by decide)).trans h.r13, (u₃.other _ (by decide)).trans h.r14,
      (u₃.other _ (by decide)).trans h.r15⟩
  rw [← List.append_nil (xor64 .r12 .rbp .rbx)]
  refine xor64_full (d := yO s₀ k) (x := yE s₀ k) (y := bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)))
    (by decide) (by decide) (by decide) (y_disj hp (by omega) (by omega) (by omega) (by omega)
      (by omega))
    (yb_disj hp (by omega) (by omega)) h₃.r12 h₃.rbp e3bx
    (fun i hi => by rw [hrd, hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    (fun i hi => by rw [hrd, hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_b hp (by omega)))
    (fun i hi => by rw [hwr, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    fun _ g₁ rd₁ wr₁ _ => WP.block_nil (h₃.keep rd₁ wr₁ fun r hr => g₁ r (calleeSaved_ne_rax hr))

end

theorem salsa_wp {s₀ : State} (hp : Pre s₀) {k : Nat} {bx : Addr} {dR : Reg} {o : Nat}
    (ho : o + 64 ≤ 128 * rr s₀) {s : State} (h : KR s₀ k bx s)
    (hd : s.gpr dR = yP s₀ + BitVec.ofNat 64 o) :
    WP isa (salsaAt salsa dR) s (KR s₀ k bx) :=
  salsaAt_ok salsaSpec hp ho hd h.r13 h.rsp h.wr fun _ rd wr cs _ _ => h.keep rd wr cs

theorem movs_wp {s₀ : State} {k : Nat} {bx : Addr} {dR : Reg} {o : Addr}
    {s : State} (h : KR s₀ k bx s) (hd : s.gpr dR = o) :
    WP isa (.block [.mov .rdi (.reg dR), .mov .rsi (.reg .r13)]) s fun s' =>
      KR s₀ k bx s' ∧ s'.gpr .rdi = o ∧ s'.gpr .rsi = sc s₀ := by
  refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · refine h.keep (u₂.rd.trans u₁.rd) (u₂.wr.trans u₁.wr) fun r hr => ?_
    rw [u₂.other _ (calleeSaved_ne hr).2, u₁.other _ (calleeSaved_ne hr).1]
  · rw [u₂.other _ (by decide), u₁.gpr, hd]
  · rw [u₂.gpr, u₁.other _ (by decide), h.r13]

/-- What a call of `vg_salsa20_8` on block `o` of `y` needs. -/
theorem call_hyps {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {s : State}
    (hrdi : s.gpr .rdi = yP s₀ + BitVec.ofNat 64 o) (hrsi : s.gpr .rsi = sc s₀)
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) (hwr : s.wr = s₀.wr) :
    Proof.Scrypt.salsaX86_64.pre
      (s.callEntry.withRegions [] [⟨yP s₀ + BitVec.ofNat 64 o, 64⟩, ⟨sc s₀, 64⟩]) ∧
    Covers ([] ++ [⟨yP s₀ + BitVec.ofNat 64 o, 64⟩, ⟨sc s₀, 64⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨yP s₀ + BitVec.ofNat 64 o, 64⟩, ⟨sc s₀, 64⟩] s.wr := by
  have lt := r_lt hp
  have hsub : Region.Sub ⟨yP s₀ + BitVec.ofNat 64 o, 64⟩ (yR s₀) := y_sub hp ho
  have hsub' : Region.Sub ⟨sc s₀, 64⟩ (scR s₀) := Region.sub_prefix (by omega)
  have hsc : (scR s₀).Contains (sc s₀) 64 := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  have cw : Covers [⟨yP s₀ + BitVec.ofNat 64 o, 64⟩, ⟨sc s₀, 64⟩] s.wr := by
    rw [hwr, hp.wr]
    exact covers_pair (covers_of_in (InRegions.of_mem (by simp) (in_y hp ho)))
      (covers_of_in (InRegions.of_mem (R := scR s₀) (by simp) hsc))
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  refine ⟨?_, fun a n h => ?_, cw⟩
  · simp only [Proof.Scrypt.salsaX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hrdi, hrsi, hrsp]
    exact ⟨trivial, trivial, hp.y_s.sub_left hsub |>.sub_right hsub',
      hp.stk_y.sub_right hsub, hp.stk_s.sub_right hsub'⟩
  · obtain ⟨R, hR, hc⟩ := cw a n (by simpa using h)
    exact ⟨R, List.mem_append_right _ hR, hc⟩

/-! ## Two runs -/

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

omit hp hp' hq in
theorem movs_rel {k : Nat} {bx bx' : Addr} {dR : Reg} (hdR : dR = .rbp ∨ dR = .r12) {o : Nat} :
    RelCT isa (fun s s' => (KR s₀ k bx s ∧ s.gpr dR = yP s₀ + BitVec.ofNat 64 o) ∧
        (KR s₀' k bx' s' ∧ s'.gpr dR = yP s₀' + BitVec.ofNat 64 o))
      (.block [.mov .rdi (.reg dR), .mov .rsi (.reg .r13)]) fun s s' =>
      (KR s₀ k bx s ∧ s.gpr .rdi = yP s₀ + BitVec.ofNat 64 o ∧ s.gpr .rsi = sc s₀) ∧
      (KR s₀' k bx' s' ∧ s'.gpr .rdi = yP s₀' + BitVec.ofNat 64 o ∧ s'.gpr .rsi = sc s₀') := by
  have ct : RelCT isa (fun s s' => (KR s₀ k bx s ∧ s.gpr dR = yP s₀ + BitVec.ofNat 64 o) ∧
        (KR s₀' k bx' s' ∧ s'.gpr dR = yP s₀' + BitVec.ofNat 64 o))
      (.block [.mov .rdi (.reg dR), .mov .rsi (.reg .r13)]) fun _ _ => True := by
    rcases hdR with rfl | rfl
    · exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
        (by taint_decide)
    · exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
        (by taint_decide)
  exact (ct.wp fun s s' h => ⟨movs_wp h.1.1 h.1.2, movs_wp h.2.1 h.2.2⟩).mono (fun _ _ h => h)
    fun _ _ h => ⟨h.2.1, h.2.2⟩

theorem salsaAt_rel {k : Nat} {bx bx' : Addr} {dR : Reg} (hdR : dR = .rbp ∨ dR = .r12) {o : Nat}
    (ho : o + 64 ≤ 128 * rr s₀) :
    RelCT isa (fun s s' => (KR s₀ k bx s ∧ s.gpr dR = yP s₀ + BitVec.ofNat 64 o) ∧
        (KR s₀' k bx' s' ∧ s'.gpr dR = yP s₀' + BitVec.ofNat 64 o))
      (salsaAt salsa dR) fun s s' => KR s₀ k bx s ∧ KR s₀' k bx' s' := by
  have ho' : o + 64 ≤ 128 * rr s₀' := hq.rr ▸ ho
  have ey : yP s₀' = yP s₀ := hq.rdx.symm
  have es : sc s₀' = sc s₀ := hq.r8.symm
  have call := RelCT.call (n := "vg_salsa20_8") (P := fun s s' =>
      (KR s₀ k bx s ∧ s.gpr .rdi = yP s₀ + BitVec.ofNat 64 o ∧ s.gpr .rsi = sc s₀) ∧
      (KR s₀' k bx' s' ∧ s'.gpr .rdi = yP s₀' + BitVec.ofNat 64 o ∧ s'.gpr .rsi = sc s₀'))
    salsa_correct salsa_ct [] [⟨yP s₀ + BitVec.ofNat 64 o, 64⟩, ⟨sc s₀, 64⟩]
    fun s s' ⟨⟨h, hd, hs⟩, ⟨h', hd', hs'⟩⟩ => by
      obtain ⟨p₁, c₁, w₁⟩ := call_hyps hp ho hd hs h.rsp h.wr
      obtain ⟨p₂, c₂, w₂⟩ := call_hyps hp' ho' hd' hs' h'.rsp h'.wr
      rw [ey, es] at p₂ c₂ w₂
      refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [h.rsp, h'.rsp, hq.rsp]⟩
      simp only [Proof.Scrypt.salsaX86_64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), hd, hs, hd', hs', ey, es]
      exact ⟨trivial, trivial⟩
  exact ((RelCT.seq (movs_rel hdR) call).wp fun s s' h =>
    ⟨salsa_wp hp ho h.1.1 h.1.2, salsa_wp hp' ho' h.2.1 h.2.2⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2

end

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

/-- The registers the loop's blocks use. -/
abbrev τK : X86_64.Taint.T := Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]

theorem body_rel {k : Nat} (hk : k < rr s₀) :
    RelCT isa (fun s s' => Inv s₀ k s ∧ Inv s₀' k s') (bmBody salsa) fun s s' =>
      (Inv s₀ (k + 1) s ∧ s.zf = some (BitVec.ofNat 64 (rr s₀ - k) - 1 == 0)) ∧
      (Inv s₀' (k + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (rr s₀' - k) - 1 == 0)) := by
  have lt := r_lt hp
  have hk' : k < rr s₀' := hq.rr ▸ hk
  have hbB : bB s₀ k = bB s₀' k := by simp only [bB, bP, hq.rdi]
  have hb1 : bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)) =
      bP s₀' + BitVec.ofNat 64 (64 * (2 * k + 1)) := by simp only [bP, hq.rdi]
  have x1 : RelCT isa (fun s s' => Inv s₀ k s ∧ Inv s₀' k s') (.block (xor64 .rbp .r15 .rbx))
      fun s s' => KR s₀ k (bB s₀ k) s ∧ KR s₀' k (bB s₀' k) s' :=
    ((RelCT.taint (A := taint) τK (fun _ _ h => Taint.agree_ofRegs
      (KR.agree hq (KR.of_inv h.1) (KR.of_inv h.2) hbB)) (by taint_decide)).wp fun _ _ h =>
      ⟨xor1_wp hp hk (KR.of_inv h.1), xor1_wp hp' hk' (KR.of_inv h.2)⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have s1 := (salsaAt_rel hp hp' hq (k := k) (bx := bB s₀ k) (bx' := bB s₀' k) (.inl rfl)
    (o := 64 * k) (by omega)).mono (P' := fun s s' => KR s₀ k (bB s₀ k) s ∧ KR s₀' k (bB s₀' k) s')
      (fun _ _ h => ⟨⟨h.1, h.1.rbp⟩, ⟨h.2, h.2.rbp⟩⟩) fun _ _ h => h
  have x2 : RelCT isa (fun s s' => KR s₀ k (bB s₀ k) s ∧ KR s₀' k (bB s₀' k) s')
      (.block (.alu .add .rbx (.imm 64) :: xor64 .r12 .rbp .rbx)) fun s s' =>
        KR s₀ k (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) s ∧
        KR s₀' k (bP s₀' + BitVec.ofNat 64 (64 * (2 * k + 1))) s' :=
    ((RelCT.taint (A := taint) τK (fun _ _ h => Taint.agree_ofRegs (KR.agree hq h.1 h.2 hbB))
      (by taint_decide)).wp fun _ _ h => ⟨xor2_wp hp hk h.1, xor2_wp hp' hk' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have s2 := (salsaAt_rel hp hp' hq (k := k) (bx := bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1)))
    (bx' := bP s₀' + BitVec.ofNat 64 (64 * (2 * k + 1))) (.inr rfl) (o := 64 * (rr s₀ + k))
    (by omega)).mono (P' := fun s s' => KR s₀ k (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) s ∧
      KR s₀' k (bP s₀' + BitVec.ofNat 64 (64 * (2 * k + 1))) s')
      (fun _ _ h => ⟨⟨h.1, h.1.r12⟩, ⟨h.2, by rw [h.2.r12, hq.rr]⟩⟩) fun _ _ h => h
  have r : RelCT isa (fun s s' => KR s₀ k (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) s ∧
        KR s₀' k (bP s₀' + BitVec.ofNat 64 (64 * (2 * k + 1))) s')
      (.block [.mov .r15 (.reg .r12), .alu .add .rbx (.imm 64), .alu .add .rbp (.imm 64),
        .alu .add .r12 (.imm 64), .alu .sub .r14 (.imm 1)]) fun _ _ => True :=
    RelCT.taint (A := taint) τK (fun _ _ h => Taint.agree_ofRegs (KR.agree hq h.1 h.2 hb1))
      (by taint_decide)
  exact ((x1.seq (s1.seq (x2.seq (s2.seq r)))).wp fun _ _ h =>
    ⟨body_ok salsaSpec hp hk h.1, body_ok salsaSpec hp' hk' h.2⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2

theorem loop_rel :
    RelCT isa (fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s') (.loop (bmBody salsa) .ne) fun s s' =>
      Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := bmBody salsa) (c := .ne)
    (Q := fun s s' => Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s')
    (fun n s s' => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s ∧ Inv s₀' k s') (fun n => by
      intro s s' t t' u u' ⟨k, hn, hk, h, h'⟩ e e'
      have hk' : k < rr s₀' := hq.rr ▸ hk
      obtain ⟨ht, ⟨i, z⟩, ⟨i', z'⟩⟩ := body_rel hp hp' hq hk _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_ne hp hk z, eval_ne hp' hk' z', ← hq.rr]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : k + 1 = rr s₀ := by simpa using hf
        exact ⟨hl ▸ i, hl ▸ i'⟩
      · have hl : k + 1 ≠ rr s₀ := by simpa using ht'
        exact ⟨rr s₀ - (k + 1), by omega, k + 1, rfl, by omega, i, i'⟩) (rr s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, hp.pos, h.1, h.2⟩) fun _ _ h => h

theorem blockMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') blockMix fun _ _ => True := by
  show RelCT isa _ (blockMixWith salsa) _
  unfold blockMixWith
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block bmPrologue)
      fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .r8, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.r8
        · exact hq.rsp) (c := .block bmPrologue) (by taint_decide)).wp
      (F₁ := Inv s₀ 0) (F₂ := Inv s₀' 0) fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s') (.block bmEpilogue)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r13]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.r13, h.2.r13, sc, sc, hq.r8]) (by taint_decide)
  exact pro.seq ((loop_rel hp hp' hq).seq epi)

end

/-! ## Verified -/

theorem pubEq_of {s₁ s₂ : State} (h : Proof.Scrypt.blockMixX86_64.pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x2000 | .rcx => 1 | .r8 => 0x3000 | .rsp => 0x4000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 128⟩]

theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixX86_64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86_64.blockMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct salsaSpec (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixX86_64.pre
    Proof.Scrypt.blockMixX86_64.pub Impl.Scrypt.X86_64.blockMix := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (blockMix_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem blockMix_verified :
    Verified X86_64.target Impl.Scrypt.X86_64.blockMix (Spec.Scrypt.blockMixContract X86_64.abi 8) :=
  Verified.of_correct blockMix_correct blockMix_ct
    { pre := by
        sig_implies_pre [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        sig_implies_post [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs]
      pub := by
        sig_implies_pub [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        sig_implies_sat [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixX86_64, X86_64.abi, X86_64.argRegs,
          Proof.Scrypt.X86_64.BlockMix.satState]
          [Proof.Scrypt.X86_64.BlockMix.satState] using Proof.Scrypt.X86_64.BlockMix.satState }

end VG.Proof.Scrypt.X86_64.BlockMix
