import VerifiedGarbage.Proof.Ed448.X86_64.VerifyDecode
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyBits
import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
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

/-- `rsi = [rdi + d] + 57`. -/
theorem movRsi57_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) :
    WP isa (.block ([.mov .rsi (.mem (sc d)), .alu .add .rsi (.imm 57)] : List Instr)) s fun t =>
      t.gpr .rsi = word s.mem base d + BitVec.ofNat 64 57 ∧ (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧
        t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have rb : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 d) 8 := hs.read hd
  erun [hs.rdi, rb]
  exact ⟨rfl, fun r hr => by simp only [hr, ite_false]⟩

/-- `rdi = rcx`, `rax = 0`. -/
theorem movBase_ok (s : State) :
    WP isa (.block ([.mov .rdi (.reg .rcx), .mov32 .rax (.imm 0)] : List Instr)) s fun t =>
      t.gpr .rdi = s.gpr .rcx ∧ t.gpr .rax = 0 ∧ (∀ r, r ≠ .rdi → r ≠ .rax → t.gpr r = s.gpr r) ∧
        t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun
  exact fun r h1 h2 => by simp only [h1, h2, ite_false]

theorem evalOps_append (a b : List FOp) (e : Env) : evalOps (a ++ b) e = evalOps b (evalOps a e) :=
  List.foldl_append ..

/-- The slots after `vcompare` and the first products: `[4]Q` and `[4]R`, `X_Q Z_R` and `X_R Z_Q`. -/
theorem compare_eval (e : Env) :
    pt (evalOps (vcompare ++ [.mul 12 0 10, .mul 13 8 2]) e) 0 1 2 =
      Proof.Ed448.double (Proof.Ed448.double (pt e 0 1 2)) ∧
    pt (evalOps (vcompare ++ [.mul 12 0 10, .mul 13 8 2]) e) 8 9 10 =
      Proof.Ed448.double (Proof.Ed448.double (pt e 8 9 10)) ∧
    evalOps (vcompare ++ [.mul 12 0 10, .mul 13 8 2]) e 12 =
      evalOps (vcompare ++ [.mul 12 0 10, .mul 13 8 2]) e 0 *
        evalOps (vcompare ++ [.mul 12 0 10, .mul 13 8 2]) e 10 ∧
    evalOps (vcompare ++ [.mul 12 0 10, .mul 13 8 2]) e 13 =
      evalOps (vcompare ++ [.mul 12 0 10, .mul 13 8 2]) e 8 *
        evalOps (vcompare ++ [.mul 12 0 10, .mul 13 8 2]) e 2 := by
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

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
theorem vfinish_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 64}
    (hsv : Saved base g s.mem) :
    WP isa (.block (vfinish fld)) s fun t =>
      t.gpr .rax = (if word s.mem base BAD = 0 ∧ Spec.Ed448.pointEqual
        (Proof.Ed448.double (Proof.Ed448.double (pt (E s.mem base) 0 1 2)))
        (Proof.Ed448.double (Proof.Ed448.double (pt (E s.mem base) 8 9 10))) = true then 1 else 0) ∧
      (∀ rd ∈ Impl.X448.X86_64.saved, t.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ .rbx :: clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside2 base 64 1584 BAD 80 s.mem t.mem := by
  rw [vfinish, WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf _ (by decide) hs) fun s1 ⟨k1, e1⟩ => ?_
  have hs1 := k1.scr hs
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

end VG.Proof.Ed448.X86_64
