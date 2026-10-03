import VerifiedGarbage.Proof.Ed448.X86_64.VerifyDecode
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyBits
import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
import VerifiedGarbage.Proof.Ed448.X86_64.BaseMain
import VerifiedGarbage.Proof.Ed448.VerifyEq
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# Ed448 verification's equation on x86-64: the whole function

The contract the proof is written against (the facts of
`Spec.Ed448.verifyEquationContract` it uses, stated for x86-64), and the
correctness of `vg_ed448_verify_equation` against it: `BAD` ends as the OR of
the checks of `S`, of decoding `A` and `R`, and of the comparison of `[4]Q`
with `[4]R`, for `Q` a representative of `[S]B + [k](-A)` when `A` decodes;
every write is in the working space, so the inputs are read unchanged, the
callee-saved registers are restored from it, and the return address is kept.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Proof.Ed448 VG.Proof.Ed448.Edwards
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk word off Outside Outside2 ofs Saved clob
  writeW_outside word_writeW_self contains_sc E_outside)
open VG.Impl.X448.X86_64 (W w sc at_ slot BITS)

/-- `vg_ed448_verify_equation(pk = rdi, signature = rsi, challenge = rdx, scratch = rcx) -> eax`. -/
def verifyEquationLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .rdi, 57⟩, ⟨s.gpr .rsi, 114⟩, ⟨s.gpr .rdx, 57⟩] ∧
    s.wr = [⟨s.gpr .rcx, 8192⟩] ∧
    (⟨s.gpr .rdi, 57⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rsi, 114⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rdx, 57⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64
  post s t := t.gpr .rax = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .rdi) 57)
    (Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57) then 1 else 0
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx

/-- One store of `r` at `[b + d]`, `b` the working space. -/
theorem store1_ok {s : State} {base : Addr} (b r : Reg) (hb : s.gpr b = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {d : Nat} (hd : d + 8 ≤ 8192) :
    WP isa (.block ([.store (at_ b d) r] : List Instr)) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : InRegions s.wr (base + BitVec.ofNat 64 d) 8 := ⟨_, hw, contains_sc hd⟩
  erun [hb, w]

/-- `rsi = [rdi + d]`. -/
theorem movRsi_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) :
    WP isa (.block ([.mov .rsi (.mem (sc d))] : List Instr)) s fun t =>
      t.gpr .rsi = word s.mem base d ∧ (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  have rb : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 d) 8 := hs.read hd
  erun [hs.rdi, rb]
  exact fun r hr => by simp only [hr, ite_false]

theorem evalOps_append (a b : List FOp) (e : Env) : evalOps (a ++ b) e = evalOps b (evalOps a e) :=
  List.foldl_append ..

/-- `[4]Q` and `[4]R`, doubling `Q` twice and then `R` twice. -/
def vcompare : List FOp := doubleAt 0 1 2 ++ doubleAt 0 1 2 ++ doubleAt 8 9 10 ++ doubleAt 8 9 10

/-- The slots after `vcompare` and the first products: `[4]Q` and `[4]R`, `X_Q Z_R` and `X_R Z_Q`. -/
theorem compare_eval (e : Env) :
    pt (evalOps (vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e) 0 1 2 =
      Proof.Ed448.double (Proof.Ed448.double (pt e 0 1 2)) ∧
    pt (evalOps (vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e) 8 9 10 =
      Proof.Ed448.double (Proof.Ed448.double (pt e 8 9 10)) ∧
    evalOps (vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 12 =
      evalOps (vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 0 *
        evalOps (vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 10 ∧
    evalOps (vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 13 =
      evalOps (vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 8 *
        evalOps (vcompare ++ ([.mul 12 0 10, .mul 13 8 2] : List FOp)) e 2 := by
  rw [evalOps_append]
  have h4 : ∀ (ec : Env) (i : Index), i.val < 3 ∨ (8 ≤ i.val ∧ i.val < 11) →
      evalOps [.mul 12 0 10, .mul 13 8 2] ec i = ec i := fun ec i hi =>
    evalOps_keep _ _ _ fun op hop => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl <;> simp only [fopDest] <;> omega
  have p12 : ∀ ec : Env, evalOps [.mul 12 0 10, .mul 13 8 2] ec 12 = ec 0 * ec 10 := fun _ => rfl
  have p13 : ∀ ec : Env, evalOps [.mul 12 0 10, .mul 13 8 2] ec 13 = ec 8 * ec 2 := fun _ => rfl
  simp only [vcompare, evalOps_append]
  generalize h1 : evalOps (doubleAt 0 1 2) e = e1
  generalize h2 : evalOps (doubleAt 0 1 2) e1 = e2
  generalize h3 : evalOps (doubleAt 8 9 10) e2 = e3
  generalize h4' : evalOps (doubleAt 8 9 10) e3 = e4
  have q4 : pt e4 0 1 2 = Proof.Ed448.double (Proof.Ed448.double (pt e 0 1 2)) := by
    rw [pt_congr (by rw [← h4', doubleAt_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h4', doubleAt_keep8 _ _ (Or.inl (by decide))]) (by rw [← h4', doubleAt_keep8 _ _ (Or.inl (by decide))]),
      pt_congr (by rw [← h3, doubleAt_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h3, doubleAt_keep8 _ _ (Or.inl (by decide))]) (by rw [← h3, doubleAt_keep8 _ _ (Or.inl (by decide))]),
      ← h2, doubleAt_eval0, ← h1, doubleAt_eval0]
  have r4 : pt e4 8 9 10 = Proof.Ed448.double (Proof.Ed448.double (pt e 8 9 10)) := by
    rw [← h4', doubleAt_eval8, ← h3, doubleAt_eval8,
      pt_congr (by rw [← h2, doubleAt_keep0 _ _ (Or.inl (by decide))])
      (by rw [← h2, doubleAt_keep0 _ _ (Or.inl (by decide))]) (by rw [← h2, doubleAt_keep0 _ _ (Or.inl (by decide))]),
      pt_congr (by rw [← h1, doubleAt_keep0 _ _ (Or.inl (by decide))])
      (by rw [← h1, doubleAt_keep0 _ _ (Or.inl (by decide))]) (by rw [← h1, doubleAt_keep0 _ _ (Or.inl (by decide))])]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pt_congr (h4 e4 0 (by decide)) (h4 e4 1 (by decide)) (h4 e4 2 (by decide)), q4]
  · rw [pt_congr (h4 e4 8 (by decide)) (h4 e4 9 (by decide)) (h4 e4 10 (by decide)), r4]
  · rw [p12, h4 e4 0 (by decide), h4 e4 10 (by decide)]
  · rw [p13, h4 e4 8 (by decide), h4 e4 2 (by decide)]

/-- `rdx = [rdi + BAD]`, then `rdx = (rdx == 0)` into `rax`. -/
theorem result_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (([.mov .rdx (.mem (sc BAD))] : List Instr) ++ (isZero ++
      ([.mov .rax (.reg .rdx)] : List Instr)))) s fun t =>
      t.gpr .rax = (if word s.mem base BAD = 0 then 1 else 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have rb : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 BAD) 8 := hs.read (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block ([.mov .rdx (.mem (sc BAD))] : List Instr)) s fun t =>
      t.gpr .rdx = word s.mem base BAD ∧ (∀ r, r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr by
    erun [hs.rdi, rb]
    exact fun r hr => by simp only [hr, ite_false]) fun s1 ⟨d1, g1, m1, rd1, wr1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (isZero_ok s1) fun s2 ⟨d2, m2, g2, rd2, wr2⟩ => ?_
  refine WP.mono (show WP isa (.block ([.mov .rax (.reg .rdx)] : List Instr)) s2 fun t =>
      t.gpr .rax = s2.gpr .rdx ∧ (∀ r, r ≠ .rax → t.gpr r = s2.gpr r) ∧ t.mem = s2.mem ∧
        t.rd = s2.rd ∧ t.wr = s2.wr by
    erun
    exact fun r hr => by simp only [hr, ite_false]) fun t ⟨at', gt, mt, rdt, wrt⟩ => ?_
  refine ⟨by rw [at', d2, d1], fun r h1 h2 => by rw [gt r h1, g2 r h2, g1 r h2], by rw [mt, m2, m1],
    by rw [rdt, rd2, rd1], by rw [wrt, wr2, wr1]⟩

theorem zero_or64 (x : BitVec 64) : 0 ||| x = x := BitVec.zero_or

/-- `rsi = r9 + 57`. -/
theorem movR957_ok (s : State) :
    WP isa (.block ([.mov .rsi (.reg .r9), .alu .add .rsi (.imm 57)] : List Instr)) s fun t =>
      t.gpr .rsi = s.gpr .r9 + BitVec.ofNat 64 57 ∧ (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧
        t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun
  exact ⟨rfl, fun r hr => by simp only [hr, ite_false]⟩

/-- `rax = 0`. -/
theorem movRax0_ok (s : State) :
    WP isa (.block ([.mov32 .rax (.imm 0)] : List Instr)) s fun t =>
      t.gpr .rax = 0 ∧ (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun
  exact fun r hr => by simp only [hr, ite_false]

/-- The moves of the entry. -/
theorem movArgs_ok (s : State) :
    WP isa (.block ([.mov .r8 (.reg .rdi), .mov .r9 (.reg .rsi), .mov .rdi (.reg .rcx),
      .mov .rsi (.reg .rdx)] : List Instr)) s fun t =>
      t.gpr .r8 = s.gpr .rdi ∧ t.gpr .r9 = s.gpr .rsi ∧ t.gpr .rdi = s.gpr .rcx ∧
      t.gpr .rsi = s.gpr .rdx ∧ (∀ r, r ∉ [Reg.r8, .r9, .rdi, .rsi] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- What the entry leaves: the callee-saved registers saved, the pointers to `A` and the
signature in `r8` and `r9`, and the challenge's in `rsi`. -/
theorem ventry_ok {s : State} {base : Addr} (hbase : s.gpr .rcx = base)
    (hws : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block ventry) s fun t =>
      Scr t base ∧ Saved base s.gpr t.mem ∧ t.gpr .r8 = s.gpr .rdi ∧ t.gpr .r9 = s.gpr .rsi ∧
      t.gpr .rsi = s.gpr .rdx ∧ (∀ r, r ∉ [Reg.r8, .r9, .rdi, .rsi] → t.gpr r = s.gpr r) ∧
      Outside base 0 48 s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [ventry, WP.block_append_iff]
  refine WP.mono (saveAt_ok .rcx hbase hws) fun s1 ⟨g1, rd1, wr1, o1, sv1⟩ => ?_
  refine WP.mono (movArgs_ok s1) fun t ⟨r8t, r9t, dit, sit, gt, mt, rdt, wrt⟩ => ?_
  refine ⟨⟨by rw [dit, g1, hbase], by rw [wrt, wr1]; exact hws, hn⟩, by rw [mt]; exact sv1,
    by rw [r8t, g1], by rw [r9t, g1], by rw [sit, g1], fun r hr => by rw [gt r hr, g1], by rw [mt]; exact o1,
    by rw [rdt, rd1], by rw [wrt, wr1]⟩

/-- The bits of `k` at `KBITS` and of `S` at `BITS`, and `rsi` the address of `S`. -/
theorem vbits_ok {s : State} {base sig ch : Addr} (hs : Scr s base) (hch : s.gpr .rsi = ch)
    (hsig : s.gpr .r9 = sig)
    (hrs : ∀ q < 57, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 q) 1)
    (hrc : ∀ q < 57, InRegions (s.rd ++ s.wr) (ch + BitVec.ofNat 64 q) 1)
    (hfs : ∀ q < 57, 8192 ≤ ofs base (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 q))
    (hfc : ∀ q < 57, 8192 ≤ ofs base (ch + BitVec.ofNat 64 q)) :
    WP isa vbits s fun t =>
      (∀ n < 456, t.mem (off base (BITS + n)) = BitVec.ofNat 8
        ((Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (sig + BitVec.ofNat 64 57) 57) >>> n) &&& 1)) ∧
      (∀ n < 456, t.mem (off base (KBITS + n)) = BitVec.ofNat 8
        ((Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem ch 57) >>> n) &&& 1)) ∧
      t.gpr .rsi = sig + BitVec.ofNat 64 57 ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rbx, .rsi] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base BITS 968 s.mem t.mem := by
  rw [vbits]
  apply WP.seq
  refine WP.mono (bitsAt_ok (o := KBITS) (by decide) hs hch hrc hfc) fun s1 ⟨g1, rd1, wr1, o1, b1⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  apply WP.seq
  refine WP.mono (movR957_ok s1) fun s2 ⟨si2, g2, m2, rd2, wr2⟩ => ?_
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide)).trans hs1.rdi, wr2 ▸ hs1.wr, hs1.nowrap⟩
  have hsig2 : s2.gpr .rsi = sig + BitVec.ofNat 64 57 := by rw [si2, g1 _ (by decide), hsig]
  refine WP.mono (bitsAt_ok (o := BITS) (by decide) hs2 hsig2
    (fun q hq => by rw [rd2, wr2, rd1, wr1]; exact hrs q hq) hfs) fun t ⟨gt, rdt, wrt, ot, bt⟩ => ?_
  have hm2 : ∀ x, 8192 ≤ ofs base x → s2.mem x = s.mem x := fun x hx => by
    rw [m2, o1 x (Or.inr (by simp only [KBITS]; omega))]
  have h3 : ∀ r, r ∉ [Reg.rax, .rdx, .rbx, .rsi] → r ∉ [Reg.rax, .rdx, .rbx] := fun r hr h =>
    hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      rcases h with h | h | h <;> simp only [h, true_or, or_true])
  refine ⟨fun n hn => ?_, fun n hn => ?_, by rw [gt _ (by decide), hsig2], fun r hr => ?_,
    by rw [rdt, rd2, rd1], by rw [wrt, wr2, wr1], fun x hx => ?_⟩
  · rw [bt n hn, hm2 _ (hfs _ (by omega)), scalar_bit s.mem _ hn]
  · have hlt : KBITS + n < 2 ^ 64 := by simp only [KBITS]; omega
    have hofs := VG.Proof.X448.X86_64.ofs_off' base hlt
    rw [ot _ (Or.inr (by rw [hofs]; simp only [BITS, KBITS]; omega)), m2, b1 n hn, scalar_bit s.mem _ hn]
  · have hsi : r ≠ .rsi := fun h => hr (by simp [h])
    rw [gt r (h3 r hr), g2 r hsi, g1 r (h3 r hr)]
  · simp only [BITS] at hx
    rw [ot x (by simp only [BITS]; omega), m2, o1 x (by simp only [KBITS]; omega)]

theorem vstart_eq : vstart = ([.store (sc PPK) .r8] : List Instr) ++ (([.store (sc PSIG) .r9] : List Instr) ++
    (([.mov32 .rax (.imm 0)] : List Instr) ++ (([.store (sc BAD) .rax] : List Instr) ++ sCheck))) := rfl

/-- The pointers to `A` and the signature saved, and `BAD` the check of `S < L`. -/
theorem vstart_ok {s : State} {base pk sig : Addr} (hs : Scr s base) (hpk : s.gpr .r8 = pk)
    (hsig : s.gpr .r9 = sig) (hp : s.gpr .rsi = sig + BitVec.ofNat 64 57)
    (hr8 : ∀ i < 7, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 (8 * i)) 8)
    (hr56 : InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 56) 1)
    (hfar : ∀ i < 57, 8192 ≤ ofs base (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 i)) :
    WP isa (.block vstart) s fun t =>
      word t.mem base PPK = pk ∧ word t.mem base PSIG = sig ∧
      (∃ c : BitVec 64, (c = 0 ↔ Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem
        (sig + BitVec.ofNat 64 57) 57) < Spec.Ed448.L) ∧ word t.mem base BAD = c) ∧
      (∀ r, r ∉ Reg.rax :: Reg.rdx :: W → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base KC 1568 s.mem t.mem := by
  have O3 : ∀ {m : Mem} {d : Nat} (v : BitVec 64), d + 8 < 2 ^ 64 → Outside base d 8 m (m.writeW (off base d) v) :=
    fun v h => writeW_outside _ base v h
  rw [vstart_eq, WP.block_append_iff]
  refine WP.mono (store1_ok .rdi .r8 hs.rdi hs.wr (d := PPK) (by decide)) fun s1 ⟨m1, g1, rd1, wr1⟩ => ?_
  have hs1 : Scr s1 base := ⟨by rw [g1]; exact hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (store1_ok .rdi .r9 hs1.rdi hs1.wr (d := PSIG) (by decide)) fun s2 ⟨m2, g2, rd2, wr2⟩ => ?_
  have hs2 : Scr s2 base := ⟨by rw [g2]; exact hs1.rdi, wr2 ▸ hs1.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (movRax0_ok s2) fun s3 ⟨ax3, g3, m3, rd3, wr3⟩ => ?_
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (store1_ok .rdi .rax hs3.rdi hs3.wr (d := BAD) (by decide)) fun s4 ⟨m4, g4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨by rw [g4]; exact hs3.rdi, wr4 ▸ hs3.wr, hs.nowrap⟩
  have hp4 : s4.gpr .rsi = sig + BitVec.ofNat 64 57 := by
    rw [g4, g3 _ (by decide), g2, g1, hp]
  have rr4 : s4.rd ++ s4.wr = s.rd ++ s.wr := by rw [rd4, wr4, rd3, wr3, rd2, wr2, rd1, wr1]
  have O4 : ∀ x, 8192 ≤ ofs base x → s4.mem x = s.mem x := fun x hx => by
    rw [m4, O3 _ (by decide) x (Or.inr (by simp only [BAD]; omega)), m3, m2,
      O3 _ (by decide) x (Or.inr (by simp only [PSIG]; omega)), m1,
      O3 _ (by decide) x (Or.inr (by simp only [PPK]; omega))]
  refine WP.mono (sCheck_ok hs4 hp4 (by rw [rr4]; exact hr8) (by rw [rr4]; exact hr56) hfar)
    fun t ⟨c, hc, bt, gt, rdt, wrt, ot⟩ => ?_
  have hbytes : Spec.Ed448.bytesAt s4.mem (sig + BitVec.ofNat 64 57) 57 =
      Spec.Ed448.bytesAt s.mem (sig + BitVec.ofNat 64 57) 57 := by
    simp only [Spec.Ed448.bytesAt]
    exact List.map_congr_left fun i hi => O4 _ (hfar i (List.mem_range.mp hi))
  have keepW : ∀ d, d + 8 ≤ BAD → KC + 56 ≤ d → word t.mem base d = word s4.mem base d := fun d h1 h2 =>
    ot.word (Or.inr h2) (Or.inl h1) (by simp only [BAD] at h1; omega)
  refine ⟨?_, ?_, ⟨c, by rw [hc, hbytes], ?_⟩, fun r hr => ?_, by rw [rdt, rd4, rd3, rd2, rd1],
    by rw [wrt, wr4, wr3, wr2, wr1], fun x hx => ?_⟩
  · rw [keepW PPK (by decide) (by decide), m4, (O3 _ (by decide)).word (Or.inl (by decide)) (by decide), m3,
      m2, (O3 _ (by decide)).word (Or.inl (by decide)) (by decide), m1, word_writeW_self, hpk]
  · rw [keepW PSIG (by decide) (by decide), m4, (O3 _ (by decide)).word (Or.inl (by decide)) (by decide), m3,
      m2, word_writeW_self, g1, hsig]
  · rw [bt, m4, word_writeW_self, ax3, zero_or64]
  · rw [gt r hr, g4, g3 r (fun h => hr (h ▸ List.mem_cons_self)), g2, g1]
  · simp only [KC] at hx
    rw [ot x (by simp only [KC]; omega) (by simp only [BAD]; omega), m4,
      O3 _ (by decide) x (by simp only [BAD]; omega), m3, m2,
      O3 _ (by decide) x (by simp only [PSIG]; omega), m1,
      O3 _ (by decide) x (by simp only [PPK]; omega)]

theorem bytesAt_take57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem bytesAt_drop57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57 = Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  refine List.ext_getElem (by simp [Spec.Ed448.bytesAt]) fun i _ _ => ?_
  simp only [Spec.Ed448.bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [Offset.add_add]

theorem bytesAt114_len (m : Mem) (p : Addr) : (Spec.Ed448.bytesAt m p 114).length = 57 + 57 := by
  simp [Spec.Ed448.bytesAt]

/-- Bytes far from the working space, after writes only to it. -/
theorem bytes_far {base p : Addr} {n : Nat} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hf : ∀ i < n, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    Spec.Ed448.bytesAt m' p n = Spec.Ed448.bytesAt m p n := by
  simp only [Spec.Ed448.bytesAt]
  exact List.map_congr_left fun i hi => h _ (Or.inr (by have := hf i (List.mem_range.mp hi); omega))

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
theorem vfinish_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 64}
    (hsv : Saved base g s.mem) :
    WP isa (vfinish fld) s fun t =>
      t.gpr .rax = (if word s.mem base BAD = 0 ∧ Spec.Ed448.pointEqual
        (Proof.Ed448.double (Proof.Ed448.double (pt (E s.mem base) 0 1 2)))
        (Proof.Ed448.double (Proof.Ed448.double (pt (E s.mem base) 8 9 10))) = true then 1 else 0) ∧
      (∀ rd ∈ Impl.X448.X86_64.saved, t.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ .rbx :: clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside2 base 64 1584 BAD 80 s.mem t.mem := by
  rw [vfinish]
  apply WP.seq
  refine WP.mono (fieldCode_ok hf _ doubleAt_valid0 hs) fun sa ⟨ka, ea⟩ => ?_
  have hsa := ka.scr hs
  apply WP.seq
  refine WP.mono (fieldCode_ok hf _ doubleAt_valid0 hsa) fun sb ⟨kb, eb⟩ => ?_
  have hsb := kb.scr hsa
  apply WP.seq
  refine WP.mono (fieldCode_ok hf _ doubleAt_valid8 hsb) fun sc' ⟨kc, ec⟩ => ?_
  have hsc := kc.scr hsb
  apply WP.seq
  refine WP.mono (fieldCode_ok hf _ doubleAt_valid8 hsc) fun sd ⟨kd, ed⟩ => ?_
  have hsd := kd.scr hsc
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf [.mul 12 0 10, .mul 13 8 2] (by decide) hsd) fun s1 ⟨k1', e1'⟩ => ?_
  have hs1 := k1'.scr hsd
  have k1 : Keep base s s1 := ((ka.trans kb).trans kc).trans (kd.trans k1')
  have e1 : E s1.mem base = evalOps (vcompare ++ [.mul 12 0 10, .mul 13 8 2]) (E s.mem base) := by
    rw [e1', ed, ec, eb, ea]; simp only [vcompare, evalOps_append]
  obtain ⟨q1, r1, x12, x13⟩ := compare_eval (E s.mem base)
  rw [← e1] at q1 r1 x12 x13
  rw [WP.block_append_iff]
  refine WP.mono (eqSlots_ok hs1 12 13) fun s2 ⟨c4, hc4, b2, k2, _⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf [.mul 12 1 10, .mul 13 9 2] (by decide) hs2) fun s3 ⟨k3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  rw [WP.block_append_iff]
  refine WP.mono (eqSlots_ok hs3 12 13) fun s4 ⟨c5, hc5, b4, k4, _⟩ => ?_
  have hs4 := k4.scr hs3
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff, List.append_assoc]
  refine WP.mono (result_ok hs4) fun s5 ⟨a5, g5, m5, rd5, wr5⟩ => ?_
  have hs5 : Scr s5 base := ⟨(g5 _ (by decide) (by decide)).trans hs4.rdi, wr5 ▸ hs4.wr, hs4.nowrap⟩
  have sv5 : Saved base g s5.mem := by
    rw [m5]
    exact ((((hsv.outside k1.mem (by decide)).outside k2.mem (by decide)).outside k3.mem (by decide)).outside
      k4.mem (by decide))
  refine WP.mono (Proof.X448.X86_64.restore_ok hs5 sv5) fun t ⟨rt, gt, mt, rdt, wrt⟩ => ?_
  -- the values
  have e2 : E s2.mem base = E s1.mem base := k2.E
  have y12 : E s3.mem base 12 = E s1.mem base 1 * E s1.mem base 10 := by rw [e3, e2]; rfl
  have y13 : E s3.mem base 13 = E s1.mem base 9 * E s1.mem base 2 := by rw [e3, e2]; rfl
  have hpe : Spec.Ed448.pointEqual (pt (E s1.mem base) 0 1 2) (pt (E s1.mem base) 8 9 10) = true ↔
      (E s1.mem base 0 * E s1.mem base 10 = E s1.mem base 8 * E s1.mem base 2 ∧
        E s1.mem base 1 * E s1.mem base 10 = E s1.mem base 9 * E s1.mem base 2) := by
    simp only [Spec.Ed448.pointEqual, pt, Bool.and_eq_true, beq_iff_eq]
  have hb : word s4.mem base BAD = word s.mem base BAD ||| c4 ||| c5 := by
    rw [b4, k3.mem.word (Or.inr (by decide)) (by decide), b2, k1.mem.word (Or.inr (by decide)) (by decide)]
  refine ⟨?_, rt, fun r hr => ?_, ?_, ?_, ?_⟩
  · have hcond : (word s.mem base BAD ||| c4 ||| c5 = 0) ↔ (word s.mem base BAD = 0 ∧
        Spec.Ed448.pointEqual (Proof.Ed448.double (Proof.Ed448.double (pt (E s.mem base) 0 1 2)))
          (Proof.Ed448.double (Proof.Ed448.double (pt (E s.mem base) 8 9 10))) = true) := by
      rw [or_eq_zero64, or_eq_zero64, hc5, hc4, y12, y13, x12, x13, ← q1, ← r1, hpe, and_assoc]
    rw [gt _ (by decide), a5, hb]
    exact if_congr hcond rfl rfl
  · have hr' : r ∉ clob := fun h => hr (List.mem_cons_of_mem _ h)
    have s1' : ∀ x ∈ Reg.rax :: Reg.rdx :: Reg.r15 :: W, x ∈ clob := by decide
    rw [gt r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨fun h => hr (h ▸ List.mem_cons_self), fun h => hr' (h ▸ by decide), fun h => hr' (h ▸ by decide),
        fun h => hr' (h ▸ by decide), fun h => hr' (h ▸ by decide), fun h => hr' (h ▸ by decide)⟩),
      g5 r (fun h => hr' (h ▸ by decide)) (fun h => hr' (h ▸ by decide)), k4.gpr r (fun h => hr' (s1' r h)),
      k3.gpr r hr', k2.gpr r (fun h => hr' (s1' r h)), k1.gpr r hr']
  · rw [rdt, rd5, k4.rd, k3.rd, k2.rd, k1.rd]
  · rw [wrt, wr5, k4.wr, k3.wr, k2.wr, k1.wr]
  · intro x h1 h2
    rw [mt, m5, k4.mem x h2, k3.mem x h1, k2.mem x h2, k1.mem x h1]

include hf in
/-- `A` decoded and negated into slots 6, 7 and 10, `Q` the neutral point, `B` and `d`. -/
theorem vdecodeA_ok {s : State} {base pk : Addr} (hs : Scr s base) (hpk : word s.mem base PPK = pk)
    (hr8 : ∀ i < 7, InRegions (s.rd ++ s.wr) (pk + BitVec.ofNat 64 (8 * i)) 8)
    (hr56 : InRegions (s.rd ++ s.wr) (pk + BitVec.ofNat 64 56) 1)
    (hfar : ∀ i < 57, 8192 ≤ ofs base (pk + BitVec.ofNat 64 i)) :
    WP isa (vdecodeA fld) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem pk 57)).isSome) ∧
        word t.mem base BAD = word s.mem base BAD ||| c) ∧
      (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem pk 57) = some a →
        pt (E t.mem base) 6 7 10 = negPoint a) ∧
      pt (E t.mem base) 0 1 2 = Spec.Ed448.identity ∧ pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      E t.mem base 11 = Spec.Ed448.d ∧
      (∀ r, r ∉ .rbx :: .rsi :: clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside2 base 64 1584 BAD 80 s.mem t.mem := by
  rw [vdecodeA]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok hs) fun s1 ⟨p1, q1, d1, o1, g1, rd1, wr1, _⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (movRsi_ok hs1 (d := PPK) (by decide)) fun s2 ⟨si2, g2, m2, rd2, wr2⟩ => ?_
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide)).trans hs1.rdi, wr2 ▸ hs1.wr, hs1.nowrap⟩
  have hp2 : s2.gpr .rsi = pk := by rw [si2, o1.word (Or.inr (by decide)) (by decide), hpk]
  have e2 : E s2.mem base = E s1.mem base := by rw [m2]
  have h10 : E s2.mem base 10 = 1 := by rw [e2]; exact congrArg Spec.Ed448.Point.Z q1
  have h11 : E s2.mem base 11 = Spec.Ed448.d := by rw [e2]; exact d1
  have rr2 : s2.rd = s.rd := by rw [rd2, rd1]
  have ww2 : s2.wr = s.wr := by rw [wr2, wr1]
  have hb2 : Spec.Ed448.bytesAt s2.mem pk 57 = Spec.Ed448.bytesAt s.mem pk 57 := by
    simp only [Spec.Ed448.bytesAt]
    exact List.map_congr_left fun i hi => by
      rw [m2, o1 _ (Or.inr (by have := hfar i (List.mem_range.mp hi); omega))]
  apply WP.seq
  refine WP.mono (decode_ok hf hs2 hp2 6 7 (Or.inl ⟨rfl, rfl⟩) h10 h11 (by rw [rr2, ww2]; exact hr8)
    (by rw [rr2, ww2]; exact hr56) hfar) fun s3 ⟨⟨c, hc, b3⟩, v3, k3, g3, rd3, wr3, o3⟩ => ?_
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hs2.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok hs3) fun s4 ⟨p4, q4, d4, o4, g4, rd4, wr4, k4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  refine WP.mono (fieldCode_ok hf [.sub 6 0 6] (by decide) hs4) fun t ⟨kt, et⟩ => ?_
  rw [hb2] at hc v3
  have keep : ∀ i : Index, i ≠ 6 → E t.mem base i = E s4.mem base i := fun i hi => by
    rw [et]; exact evalOps_keep _ _ _ fun op hop => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      subst hop; exact fun h => hi (Fin.ext (by simp only [fopDest] at h; omega))
  have t6 : E t.mem base 6 = E s4.mem base 0 - E s4.mem base 6 := by rw [et]; rfl
  refine ⟨⟨c, hc, ?_⟩, fun a ha => ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [kt.mem.word (Or.inr (by decide)) (by decide), o4.word (Or.inr (by decide)) (by decide), b3, m2,
      o1.word (Or.inr (by decide)) (by decide)]
  · obtain ⟨vx, vy, vz⟩ := v3 a ha
    have z0 : E s4.mem base 0 = 0 := congrArg Spec.Ed448.Point.X p4
    show (⟨E t.mem base 6, E t.mem base 7, E t.mem base 10⟩ : Spec.Ed448.Point) = ⟨0 - a.X, a.Y, a.Z⟩
    rw [t6, keep 7 (by decide), keep 10 (by decide), z0, k4 6 (by decide) (by decide),
      k4 7 (by decide) (by decide), vx, vy, vz, show E s4.mem base 10 = 1 from congrArg Spec.Ed448.Point.Z q4]
  · rw [pt_congr (keep 0 (by decide)) (keep 1 (by decide)) (keep 2 (by decide)), p4]
  · rw [pt_congr (keep 8 (by decide)) (keep 9 (by decide)) (keep 10 (by decide)), q4]
  · rw [keep 11 (by decide), d4]
  · have hr' : r ∉ clob := fun h => hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    have hW : r ∉ W := fun h => hr' (by
      have : ∀ x ∈ W, x ∈ clob := by decide
      exact this r h)
    rw [kt.gpr r hr', g4 r hW, g3 r (fun h => hr (by
      simp only [List.mem_cons] at h ⊢; rcases h with h | h <;> [exact Or.inl h; exact Or.inr (Or.inr h)])),
      g2 r (fun h => hr (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)), g1 r hW]
  · rw [kt.rd, rd4, rd3, rr2]
  · rw [kt.wr, wr4, wr3, ww2]
  · intro x h1 h2
    rw [kt.mem x h1, o4 x h1, o3 x h1 h2, m2, o1 x h1]

/-- Two stages' bound on what they write, as one range. -/
theorem wide {base : Addr} {m m' : Mem} (h : Outside2 base 64 1584 BAD 80 m m') :
    Outside base 64 1704 m m' :=
  h.outside (by decide) (by decide) (by decide) (by decide)

include hf in
theorem verifyEquation_correct {s : State} (hp : verifyEquationLocal.pre s) :
    WP isa (verifyEquationWith fld) s fun t => gprPreserved s t ∧ verifyEquationLocal.post s t := by
  obtain ⟨hr, hw, hdk, hds, hdc, hret, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .rcx = b := ⟨_, rfl⟩
  rw [hbase] at hdk hds hdc hret hn hw
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have rpk : ∀ i n, i + n ≤ 57 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .rdi, 57⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 57) h (by omega)⟩
  have rsg : ∀ i n, i + n ≤ 114 → InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .rsi, 114⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 114) h (by omega)⟩
  have rch : ∀ i n, i + n ≤ 57 → InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .rdx, 57⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 57) h (by omega)⟩
  have fpk : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rdi + BitVec.ofNat 64 i) := fun i hi => far hdk hi (by decide)
  have fsg : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 i) :=
    fun i hi => far hds (by omega) (by decide)
  have fs : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 57 + BitVec.ofNat 64 i) :=
    fun i hi => by rw [Offset.add_add]; exact far hds (by omega) (by decide)
  have fch : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rdx + BitVec.ofNat 64 i) := fun i hi => far hdc hi (by decide)
  obtain ⟨S, hS⟩ : ∃ S, Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .rsi + BitVec.ofNat 64 57) 57) = S :=
    ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57) = K := ⟨_, rfl⟩
  rw [verifyEquationWith]
  -- The entry: the callee-saved registers saved, and the pointers.
  apply WP.seq
  refine WP.mono (ventry_ok hbase hws hn) fun s1 ⟨hs1, sv1, r81, r91, si1, g1, o1, rd1, wr1⟩ => ?_
  have rr1 : s1.rd ++ s1.wr = s.rd ++ s.wr := by rw [rd1, wr1]
  have O1 : Outside base 0 8192 s.mem s1.mem := o1.mono (by decide) (by decide)
  -- The bits of `k` and `S`.
  apply WP.seq
  refine WP.mono (vbits_ok (sig := s.gpr .rsi) (ch := s.gpr .rdx) hs1 si1 r91
    (fun q hq => by rw [rr1, Offset.add_add]; exact rsg _ _ (by omega))
    (fun q hq => by rw [rr1]; exact rch _ _ (by omega)) fs fch)
    fun s2 ⟨bs2, bk2, si2, g2, rd2, wr2, o2⟩ => ?_
  rw [bytes_far O1 fs, hS] at bs2
  rw [bytes_far O1 fch, hK] at bk2
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide)).trans hs1.rdi, wr2 ▸ hs1.wr, hn⟩
  have rr2 : s2.rd ++ s2.wr = s.rd ++ s.wr := by rw [rd2, wr2, rd1, wr1]
  have O2 : Outside base 0 8192 s.mem s2.mem := O1.trans (o2.mono (by decide) (by decide))
  -- The pointers saved, and the check of `S`.
  apply WP.seq
  refine WP.mono (vstart_ok (pk := s.gpr .rdi) (sig := s.gpr .rsi) hs2 (by rw [g2 _ (by decide), r81]) (by rw [g2 _ (by decide), r91]) si2
    (fun i hi => by rw [rr2, Offset.add_add]; exact rsg _ _ (by omega))
    (by rw [rr2, Offset.add_add]; exact rsg _ _ (by omega)) fs)
    fun s3 ⟨pk3, sig3, ⟨c0, hc0, b3⟩, g3, rd3, wr3, o3⟩ => ?_
  rw [bytes_far O2 fs, hS] at hc0
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hn⟩
  have rr3 : s3.rd ++ s3.wr = s.rd ++ s.wr := by rw [rd3, wr3, rr2]
  have O3 : Outside base 0 8192 s.mem s3.mem := O2.trans (o3.mono (by decide) (by decide))
  -- `A`, decoded and negated, and the constants.
  apply WP.seq
  refine WP.mono (vdecodeA_ok hf hs3 pk3 (fun i hi => by rw [rr3]; exact rpk _ _ (by omega))
    (by rw [rr3]; exact rpk _ _ (by omega)) fpk)
    fun s4 ⟨⟨cA, hcA, b4⟩, na4, p4, q4, d4, g4, rd4, wr4, o4⟩ => ?_
  rw [bytes_far O3 fpk] at hcA na4
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hn⟩
  have O4 : Outside base 0 8192 s.mem s4.mem := O3.trans ((wide o4).mono (by decide) (by decide))
  -- The loop.
  apply WP.seq
  rw [vloop]
  apply WP.seq
  refine WP.mono (show WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 456))]) s4 _ from
    Proof.X448.X86_64.setRbx_ok s4 456 (by decide)) fun s5 ⟨rbx5, g5, m5, rd5, wr5⟩ => ?_
  have hs5 : Scr s5 base := ⟨(g5 _ (by decide)).trans hs4.rdi, wr5 ▸ hs4.wr, hn⟩
  have bits5 : ∀ o : Nat, o + 456 ≤ 8192 → 2048 ≤ o → ∀ t < 456,
      s5.mem (off base (o + t)) = s2.mem (off base (o + t)) := fun o ho1 ho2 t ht => by
    have hofs := VG.Proof.X448.X86_64.ofs_off' base (d := o + t) (by omega)
    rw [m5, o4 _ (Or.inr (by rw [hofs]; omega)) (Or.inr (by rw [hofs]; simp only [BAD]; omega)),
      o3 _ (Or.inr (by rw [hofs]; simp only [KC]; omega))]
  have I5 : VInv base S K (pt (E s5.mem base) 6 7 10) s5 456 s5 := by
    refine ⟨hs5, rbx5, fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _, ?_, rfl, ?_, fun _ => ?_⟩
    · rw [m5]; exact q4
    · rw [m5]; exact d4
    · rw [← hS, ← hK, scalar_shift, scalar_shift, zero_nsmul, zero_nsmul, add_zero, m5, p4]
      exact identity_rep
  refine WP.mono (vloop_ok hf (fun t ht => by rw [bits5 BITS (by decide) (by decide) t ht]; exact bs2 t ht)
    (fun t ht => by rw [bits5 KBITS (by decide) (by decide) t ht]; exact bk2 t ht)
    456 s5 (by decide) (by decide) I5) fun s6 I6 => ?_
  -- `R`, decoded.
  apply WP.seq
  refine WP.mono (movRsi_ok I6.scr (d := PSIG) (by decide)) fun s7 ⟨si7, g7, m7, rd7, wr7⟩ => ?_
  have hs7 : Scr s7 base := ⟨(g7 _ (by decide)).trans I6.scr.rdi, wr7 ▸ I6.scr.wr, hn⟩
  have hsig7 : s7.gpr .rsi = s.gpr .rsi := by
    rw [si7, I6.mem.word (by decide) (by decide), m5,
      o4.word (Or.inr (by decide)) (Or.inl (by decide)) (by decide), sig3]
  have O7 : Outside base 0 8192 s.mem s7.mem := by
    have h6 := I6.mem
    rw [m5] at h6
    rw [m7]
    exact O4.trans (h6.mono (by decide) (by decide))
  have rr7 : s7.rd ++ s7.wr = s.rd ++ s.wr := by
    rw [rd7, wr7, I6.rd, I6.wr, rd5, wr5, rd4, wr4, rr3]
  have h10 : E s7.mem base 10 = 1 := by
    rw [m7]; exact congrArg Spec.Ed448.Point.Z I6.q
  have h11 : E s7.mem base 11 = Spec.Ed448.d := by rw [m7]; exact I6.d
  apply WP.seq
  refine WP.mono (decode_ok hf hs7 hsig7 8 9 (Or.inr ⟨rfl, rfl⟩) h10 h11
    (fun i hi => by rw [rr7]; exact rsg _ _ (by omega)) (by rw [rr7]; exact rsg _ _ (by omega)) fsg)
    fun s8 ⟨⟨cR, hcR, b8⟩, v8, k8, g8, rd8, wr8, o8⟩ => ?_
  rw [bytes_far O7 fsg, ← bytesAt_take57] at hcR v8
  have hs8 : Scr s8 base := ⟨(g8 _ (by decide)).trans hs7.rdi, wr8 ▸ hs7.wr, hn⟩
  have sv8 : Saved base s.gpr s8.mem := by
    have sv4 := ((sv1.outside o2 (by decide)).outside o3 (by decide)).outside (wide o4) (by decide)
    have sv5 : Saved base s.gpr s5.mem := by rw [m5]; exact sv4
    have sv7 : Saved base s.gpr s7.mem := by rw [m7]; exact sv5.outside I6.mem (by decide)
    exact sv7.outside (wide o8) (by decide)
  -- `[4]Q` and `[4]R` compared, and the result.
  refine WP.mono (vfinish_ok hf hs8 sv8) fun t ⟨at', rt, gt, rdt, wrt, ot⟩ => ?_
  have hBAD : word s8.mem base BAD = c0 ||| cA ||| cR := by
    rw [b8, m7, I6.mem.word (by decide) (by decide), m5, b4, b3]
  have OT : Outside base 0 8192 s.mem t.mem :=
    (O7.trans ((wide o8).mono (by decide) (by decide))).trans ((wide ot).mono (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.rbx, 0) (by decide)
    · exact rt (.rbp, 8) (by decide)
    · rw [gt _ (by decide), g8 _ (by decide), g7 _ (by decide), I6.gpr _ (by decide), g5 _ (by decide),
        g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
    · exact rt (.r12, 16) (by decide)
    · exact rt (.r13, 24) (by decide)
    · exact rt (.r14, 32) (by decide)
    · exact rt (.r15, 40) (by decide)
  · exact (VG.Proof.Ed448.X86_64.Outside.frame OT).readW (r := ⟨s.gpr .rsp, 8⟩)
      (Region.contains_self _ _) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r rfl; exact hret) (by decide)
  · show t.gpr .rax = _
    rw [at']
    refine if_congr ?_ rfl rfl
    rw [hBAD, or_eq_zero64, or_eq_zero64]
    cases ha : Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .rdi) 57) with
    | none =>
      rw [verifyEquation_none (Or.inl ha)]
      refine ⟨fun h => absurd (hcA.mp h.1.1.2) (by rw [ha]; decide), fun h => absurd h (by decide)⟩
    | some a =>
      cases hR : Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 114).take 57) with
      | none =>
        rw [verifyEquation_none (Or.inr hR)]
        refine ⟨fun h => absurd (hcR.mp h.1.2) (by rw [hR]; decide), fun h => absurd h (by decide)⟩
      | some r =>
        have cA0 : cA = 0 := hcA.mpr (by rw [ha]; rfl)
        have cR0 : cR = 0 := hcR.mpr (by rw [hR]; rfl)
        have hva := decodePoint_valid ha
        have hA : pt (E s5.mem base) 6 7 10 = negPoint a := by rw [m5]; exact na4 a ha
        have k80 : ∀ i : Index, i = 0 ∨ i = 1 ∨ i = 2 → E s8.mem base i = E s6.mem base i := by
          rintro i (rfl | rfl | rfl) <;>
            rw [k8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), m7]
        have hQ : Rep (pt (E s8.mem base) 0 1 2) (Spec.Ed448.decodeLE
            ((Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 114).drop 57) • baseAff +
            Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57) • (-toAffine a)) := by
          have := I6.rep
          rw [Nat.shiftRight_zero, Nat.shiftRight_zero, hA, toAffine_negPoint hva] at this
          rw [bytesAt_drop57, hS, hK, pt_congr (k80 0 (Or.inl rfl)) (k80 1 (Or.inr (Or.inl rfl)))
            (k80 2 (Or.inr (Or.inr rfl)))]
          exact this (valid_negPoint hva)
        have hRR : Rep (pt (E s8.mem base) 8 9 10) (toAffine r) := by
          obtain ⟨vx, vy, vz⟩ := v8 r hR
          have : pt (E s8.mem base) 8 9 10 = r := by
            show (⟨E s8.mem base 8, E s8.mem base 9, E s8.mem base 10⟩ : Spec.Ed448.Point) = r
            rw [vx, vy, k8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h10, ← vz]
          rw [this]; exact rep_toAffine (decodePoint_valid hR)
        rw [verifyEquation_some (bytesAt57_len _ _) (bytesAt114_len _ _) (bytesAt57_len _ _) ha hR hQ hRR,
          Bool.and_eq_true, decide_eq_true_iff, bytesAt_drop57, hS, cA0, cR0, hc0]
        exact ⟨fun h => ⟨h.1.1.1, h.2⟩, fun h => ⟨⟨⟨h.1, rfl⟩, rfl⟩, h.2⟩⟩

end VG.Proof.Ed448.X86_64
