import VerifiedGarbage.Proof.Rc2.X86.Stream.UpdateHead
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Correct
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-!
# Streaming RC2-CBC on x86 (32-bit): the call of the CBC function

Untrusted: everything here is checked by Lean. The call of the verified CBC
function on the blocks at `out` (`cbcCall_ok`), from the state before it
(`Mid`), in a frame of its arguments.
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

def cbcName : Spec.Rc2.Direction → String
  | .encrypt => "vg_rc2_cbc_encrypt"
  | .decrypt => "vg_rc2_cbc_decrypt"

/-- The registers pushed as the callee's arguments. -/
abbrev rs5 : List Reg := [.ebx, .esi, .edx, .ecx, .eax]

theorem cbcCall_eq (d : Spec.Rc2.Direction) :
    cbcCall d = .frame (.push rs5) (.call (cbcName d) (Impl.Rc2.X86.Cbc.cbc d)) (.pop .eax 5) := by
  cases d <;> rfl

theorem cbc_nosp (d : Spec.Rc2.Direction) : NoSp (Impl.Rc2.X86.Cbc.cbc d) := by
  apply NoSp.of_all
  cases d
  · change Impl.Rc2.X86.Cbc.encrypt.allInstrs _ = true
    lit_decide
  · change Impl.Rc2.X86.Cbc.decrypt.allInstrs _ = true
    lit_decide

theorem cbc_stack (d : Spec.Rc2.Direction) : stackUse (Impl.Rc2.X86.Cbc.cbc d) = 16 := by
  cases d <;> rfl

/-- The regions the CBC function reads (beyond those it writes), and writes. -/
def callRd (s₀ s : State) : List Region :=
  [⟨(ctx s₀).setWidth 64, 128⟩, ⟨argAddr (pushed rs5 s).callEntry 0, 20⟩]
def callWr (s₀ : State) : List Region :=
  [⟨(ctx s₀ + 128).setWidth 64, 8⟩, ⟨oA s₀, 8 * (O s₀ / 8)⟩, ⟨sA s₀, 512⟩]

theorem iv_eq {s₀ : State} (hp : Pre s₀) : (ctx s₀ + 128).setWidth 64 = cA s₀ + BitVec.ofNat 64 128 :=
  addr_eq (x := ctx s₀) (k := 128) (by have := hp.c_fit; omega)

section
variable {s₀ s : State} (hp : Pre s₀) (hm : Mid s₀ s)
include hp hm

theorem callEntry_args :
    arg (pushed rs5 s).callEntry 0 = ctx s₀ ∧ arg (pushed rs5 s).callEntry 1 = ctx s₀ + 128 ∧
      arg (pushed rs5 s).callEntry 2 = op s₀ ∧
      arg (pushed rs5 s).callEntry 3 = BitVec.ofNat 32 (O s₀ / 8) ∧
      arg (pushed rs5 s).callEntry 4 = scr s₀ := by
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hm.common.esp]; have := hp.sp_lo; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ rs5 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [callEntry_arg fit hrs (by simp)]
  · exact hm.eax
  · exact hm.ecx
  · exact hm.edx
  · exact hm.esi
  · exact hm.ebx

omit hp in
theorem callEntry_sp : (pushed rs5 s).callEntry.gpr .esp = E s₀ - BitVec.ofNat 32 24 := by
  rw [callEntry_esp', hm.common.esp]; rfl

omit hp in
theorem callEntry_argAddr : argAddr (pushed rs5 s).callEntry 0 = (E s₀ - BitVec.ofNat 32 20).setWidth 64 := by
  rw [callEntry_argAddr0, hm.common.esp]; rfl

theorem callPre_ok (d : Spec.Rc2.Direction) :
    VG.X86.CallPre (Cbc.contract d) rs5 (callRd s₀ s) (callWr s₀) s := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := callEntry_args hp hm
  have eSp := callEntry_sp hm
  have eA := callEntry_argAddr hm
  have hOe := hp.O_eq
  have hlo := hp.sp_lo
  have hcf := hp.c_fit
  have hof := hp.o_fit
  have hEf := hp.sp_fit
  have hOlt : O s₀ < 2 ^ 32 := (arg s₀ 5).isLt
  have e8 : 8 * (O s₀ / 8) = O s₀ := by omega
  have ivE := iv_eq hp
  have hesp : s.gpr .esp = E s₀ := hm.common.esp
  -- The stack the frame and the callee use.
  have kA : Region.Sub ⟨(E s₀ - BitVec.ofNat 32 20).setWidth 64, 20⟩ (stkR s₀) := below_sub (by decide) hlo
  have kR : Region.Sub ⟨(E s₀ - BitVec.ofNat 32 24).setWidth 64, 4⟩ (stkR s₀) := by
    have := below_inner (sp := E s₀) (a := 4) (b := 40) (k := 20) (by omega) hlo
    rw [show E s₀ - BitVec.ofNat 32 24 = E s₀ - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have kS : Region.Sub (below (E s₀ - BitVec.ofNat 32 24) 16) (stkR s₀) := below_inner (by omega) hlo
  have ivS : Region.Sub ⟨(ctx s₀ + 128).setWidth 64, 8⟩ (ctxR s₀) := by rw [ivE]; exact Pre.iv_sub
  have oS : Region.Sub ⟨oA s₀, 8 * (O s₀ / 8)⟩ (oR s₀) := by rw [e8]; exact fun _ h => h
  have bS : Region.Sub ⟨sA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Cbc.contract, callRd, callWr, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, addr32]
    refine ⟨trivial, by rw [toNat_ofNat_lt (by omega)], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [ivE]; exact Pre.sch_iv
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.c_o.sub_left Pre.sch_sub).sub_right oS
    · exact (hp.c_s.sub_left Pre.sch_sub).sub_right bS
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.c_o.sub_left ivS).sub_right oS
    · exact (hp.c_s.sub_left ivS).sub_right bS
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.o_s.sub_left oS).sub_right bS
    · exact (hp.k_c.sub_left kA).sub_right ivS
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.k_o.sub_left kA).sub_right oS
    · exact (hp.k_s.sub_left kA).sub_right bS
    · exact (hp.k_c.sub_left kR).sub_right ivS
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.k_o.sub_left kR).sub_right oS
    · exact (hp.k_s.sub_left kR).sub_right bS
    · exact (hp.k_c.sub_left kS).sub_right Pre.sch_sub
    · exact (hp.k_c.sub_left kS).sub_right ivS
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.k_o.sub_left kS).sub_right oS
    · exact (hp.k_s.sub_left kS).sub_right bS
    · omega
    · show (ctx s₀ + BitVec.ofNat 32 128).toNat + 8 ≤ _
      rw [toNat_add_ofNat (by omega)]; omega
    · have := hp.s_fit; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [toNat_ofNat_lt (by omega)]; omega
  · have wr : s.wr = [ctxR s₀, oR s₀, scR s₀] := hm.common.wr.trans hp.wr
    refine Covers.of_sub fun r hr => ?_
    simp only [callRd, callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨ctxR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
    · refine ⟨below (s.gpr .esp) (4 * rs5.length), by simp, 0, ?_, by simp⟩
      rw [BitVec.add_zero, callEntry_argAddr0]
    · exact ⟨ctxR s₀, by simp [wr], 128, ivE, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨oR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact ⟨scR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
  · have wr : s.wr = [ctxR s₀, oR s₀, scR s₀] := hm.common.wr.trans hp.wr
    refine Covers.of_sub fun r hr => ?_
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by simp [wr], 128, ivE, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨oR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact ⟨scR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩

/-- The call of the CBC function on the `O / 8` blocks at `out`: it writes only the
chaining value, `out`, its scratch space and the stack below `esp`. -/
theorem cbcCall_ok (d : Spec.Rc2.Direction) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [ivR s₀, oR s₀, ⟨sA s₀, 512⟩, stkR s₀] s.mem s'.mem →
      Spec.Rc2.blocksAt s'.mem (oA s₀) (O s₀ / 8) = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (cA s₀)) d
        (Spec.Rc2.blockAt s.mem (cA s₀ + BitVec.ofNat 64 128)) (Spec.Rc2.blocksAt s.mem (oA s₀) (O s₀ / 8))).1 →
      Spec.Rc2.blockAt s'.mem (cA s₀ + BitVec.ofNat 64 128) =
        (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (cA s₀)) d
          (Spec.Rc2.blockAt s.mem (cA s₀ + BitVec.ofNat 64 128)) (Spec.Rc2.blocksAt s.mem (oA s₀) (O s₀ / 8))).2 →
      Q s') :
    WP isa (cbcCall d) s Q := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := callEntry_args hp hm
  have hlo := hp.sp_lo
  have hOe := hp.O_eq
  have hOlt : O s₀ < 2 ^ 32 := (arg s₀ 5).isLt
  have e8 : 8 * (O s₀ / 8) = O s₀ := by omega
  have ivE := iv_eq hp
  have hesp : s.gpr .esp = E s₀ := hm.common.esp
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ rs5 := by decide
  have kE : Region.Sub (below (s.gpr .esp) (4 * rs5.length + 4)) (stkR s₀) := by
    rw [hesp]; exact below_sub (by decide) hlo
  have oS : Region.Sub ⟨oA s₀, 8 * (O s₀ / 8)⟩ (oR s₀) := by rw [e8]; exact fun _ h => h
  have sing {r r' : Region} (h : r.Disjoint r') : ∀ x ∈ [r'], r.Disjoint x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact h
  rw [cbcCall_eq]
  refine WP.callWith (k := Cbc.contract d) (fun s h => Cbc.cbc_body_correct d s h) (cbc_nosp d) (by simp)
    hrs (by rw [cbc_stack, hesp]; simp only [List.length_cons, List.length_nil]; omega)
    (callPre_ok hp hm d) fun s' rd wr cs f ⟨s₂, m₂, post⟩ => ?_
  have ce := callEntry_frame fit hrs
  simp only [Cbc.contract, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, m₂, addr32,
    toNat_ofNat_lt (show O s₀ / 8 < 2 ^ 32 by omega), ivE] at post
  have sch : Spec.Rc2.scheduleAt (pushed rs5 s).callEntry.mem (cA s₀) = Spec.Rc2.scheduleAt s.mem (cA s₀) :=
    Proof.Rc2.scheduleAt_frame ce _ (sing ((hp.k_c.sub_left kE).sub_right Pre.sch_sub).symm)
  have iv : Spec.Rc2.blockAt (pushed rs5 s).callEntry.mem (cA s₀ + BitVec.ofNat 64 128) =
      Spec.Rc2.blockAt s.mem (cA s₀ + BitVec.ofNat 64 128) :=
    Proof.Rc2.blockAt_frame ce _ (sing ((hp.k_c.sub_left kE).sub_right Pre.iv_sub).symm)
  have out : Spec.Rc2.blocksAt (pushed rs5 s).callEntry.mem (oA s₀) (O s₀ / 8) =
      Spec.Rc2.blocksAt s.mem (oA s₀) (O s₀ / 8) :=
    Proof.Rc2.blocksAt_frame ce _ _ (sing ((hp.k_o.sub_left kE).sub_right oS).symm)
  rw [sch, iv, out] at post
  refine hQ s' rd wr cs (f.sub fun r hr => ?_) post.1 post.2
  simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨ivR s₀, by simp, by rw [ivE]; exact fun _ h => h⟩
  · exact ⟨oR s₀, by simp, oS⟩
  · exact ⟨⟨sA s₀, 512⟩, by simp, fun _ h => h⟩
  · refine ⟨stkR s₀, by simp, ?_⟩
    rw [cbc_stack, hesp]; exact fun _ h => h

end

/-- Our caller's `esi` and `ebx`, from the scratch space at `ebx`. -/
theorem restore_ok {s₀ s : State} (hp : Pre s₀) (hebx : s.gpr .ebx = scr s₀)
    (hwr : s.wr = s₀.wr) (h₁ : s.mem.readW (addr (scr s₀) 512) 32 = s₀.gpr .ebx)
    (h₂ : s.mem.readW (addr (scr s₀) 516) 32 = s₀.gpr .esi) {Q : State → Prop}
    (hQ : ∀ t, t.mem = s.mem → t.gpr .ebx = s₀.gpr .ebx → t.gpr .esi = s₀.gpr .esi →
      (∀ r, r ≠ .ebx → r ≠ .esi → t.gpr r = s.gpr r) → Q t) :
    WP isa (.block restore) s Q := by
  have rin {d : Nat} (hd : d + 4 ≤ 576) : InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 := by
    obtain ⟨r, hr, hc⟩ := hp.sin hwr hd
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [restore]
  refine wp_ldm (o := 516) hebx (rin (d := 516) (by decide)) fun s₁ u₁ => ?_
  refine wp_ldm (o := 512) (B := scr s₀) (by rw [u₁.other _ (by decide)]; exact hebx)
    (by rw [u₁.rd, u₁.wr]; exact rin (d := 512) (by decide)) fun s₂ u₂ => WP.block_nil ?_
  refine hQ s₂ (by rw [u₂.mem, u₁.mem]) (by rw [u₂.gpr, u₁.mem]; exact h₁)
    (by rw [u₂.other _ (by decide), u₁.gpr]; exact h₂) fun r a b => ?_
  rw [u₂.other _ a, u₁.other _ b]

end VG.Proof.Rc2.X86.Stream.Update
