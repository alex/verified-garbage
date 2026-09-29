import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Sha512.X86.Compress
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Impl.Sha512.X86.Stream
import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Streaming SHA-512 on x86 (32-bit): common lemmas

Untrusted: everything here is checked by Lean. The call of the compression
function in the terms of the streaming proofs: its frame of arguments
(`WP.frame`) and the call (`WP.call`), whose effect the compression
function's own `Verified` proof gives.
-/

namespace VG.Proof.Sha512.X86.Stream

open VG VG.X86 VG.Impl.Sha512.X86.Stream
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha256.X86.Stream (contains_addr Upd Mupd wp_mov wp_addi wp_movi wp_movm)
open VG.Proof.Sha512.X86.Compress (compress_verified)
open VG.Spec.Sha512 (HashValue stateAt blockAt compress compressBlocks parseBlock)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-! ## The call of the compression function -/

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

/-- The two definitions of the instructions of structured code agree. -/
theorem x86_instrs_eq {I C : Type} (c : Code I C) : X86.instrs c = VG.instrs c := by
  induction c <;> simp_all [X86.instrs, VG.instrs]

theorem compress_nosp : NoSp Impl.Sha512.X86.compress := by
  have : ((VG.instrs Impl.Sha512.X86.compress).all fun i => !Taint.clobbers i .esp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  rw [x86_instrs_eq] at hi
  simpa using List.all_eq_true.mp this i hi

theorem compress_stackUse : stackUse Impl.Sha512.X86.compress = 0 := by lit_decide

/-- The frame's argument registers, pushed last to first. -/
abbrev args : List Reg := [.edx, .ecx, .eax, .ebx]

theorem popped_esp (r : Reg) (k : Nat) (s : State) :
    (popped r k s).gpr .esp = s.gpr .esp + BitVec.ofNat 32 (4 * k) := (popReg_eq s r k).2.2.1

theorem popped_gpr (r : Reg) (k : Nat) (s : State) {q : Reg} (h₁ : q ≠ .esp) (h₂ : q ≠ r) :
    (popped r k s).gpr q = s.gpr q := (popReg_eq s r k).2.2.2 q h₁ h₂

theorem popped_rd (r : Reg) (k : Nat) (s : State) : (popped r k s).rd = s.rd := (popReg_eq s r k).1

theorem popped_wr (r : Reg) (k : Nat) (s : State) : (popped r k s).wr = s.wr.tail := rfl

theorem popped_mem (r : Reg) (k : Nat) (s : State) : (popped r k s).mem = s.mem :=
  (popReg_rest s r k).1

/-- The address of byte `k` of the region at `x`, in 64 bits. -/
theorem setWidth_add {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 k := by
  have := addr_eq (x := x) (k := k) h
  simpa only [addr] using this

/-- Calling `vg_sha512_compress(ebx, eax, ecx, edx)` with `eax = ebx + 64`
(the buffer of the streaming state at `st`), `ecx = 1` and `edx` the scratch
space `scr`: it compresses the buffer into the hash value, and writes only
the hash value, the first 224 bytes of the scratch space and the 20 bytes
below `esp`. -/
theorem compressCall_ok {s : State} {st scr E : BitVec 32}
    (hesp : s.gpr .esp = E) (hebx : s.gpr .ebx = st) (heax : s.gpr .eax = st + 64)
    (hecx : s.gpr .ecx = 1) (hedx : s.gpr .edx = scr)
    (f₀ : st.toNat + 192 ≤ 2 ^ 32) (f₃ : scr.toNat + 272 ≤ 2 ^ 32) (hE : 20 ≤ E.toNat)
    (d : Region.Disjoint ⟨st.setWidth 64, 192⟩ ⟨scr.setWidth 64, 272⟩)
    (dS : Region.Disjoint (below E 20) ⟨st.setWidth 64, 192⟩)
    (dV : Region.Disjoint (below E 20) ⟨scr.setWidth 64, 272⟩)
    (hS : ⟨st.setWidth 64, 192⟩ ∈ s.wr) (hV : ⟨scr.setWidth 64, 272⟩ ∈ s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ [Reg.ebx, .esi, .edi, .ebp, .esp], s'.gpr r = s.gpr r) →
      Frame [⟨st.setWidth 64, 64⟩, ⟨scr.setWidth 64, 224⟩, below E 20] s.mem s'.mem →
      stateAt s'.mem (st.setWidth 64) =
        compress (stateAt s.mem (st.setWidth 64)) (blockAt s.mem (st.setWidth 64 + 64)) → Q s') :
    WP isa compressCall s Q := by
  have hn : 4 * args.length ≤ (s.gpr .esp).toNat := by rw [hesp]; simp only [args]; simp; omega_arith
  have hd : stackUse Impl.Sha512.X86.compress + 4 ≤ ((pushed args s).gpr .esp).toNat := by
    rw [compress_stackUse, pushed_esp, sub_toNat hn, hesp]; simp only [args]; simp; omega_arith
  have hE16 : ((pushed args s).gpr .esp) = E - BitVec.ofNat 32 16 := by rw [pushed_esp, hesp]; rfl
  -- The arguments, as the callee sees them.
  set sE := (pushed args s).callEntry with hsE
  have ha : ∀ j, j < 4 → arg sE j = s.gpr (args[3 - j]!) := by
    intro j hj
    rw [hsE, arg_callEntry (by rw [hE16, sub_toNat (by omega_arith)]; omega_arith)
      (by rw [hE16, sub_toNat (by omega_arith)]; have := E.isLt; omega_arith)]
    have := pushed_word (rs := args) (s := s) (by decide) hn (i := j) (by simp only [args]; simp; omega_arith)
    rw [this]
    simp only [args, List.length_cons, List.length_nil]
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
  have e0 : arg sE 0 = st := by rw [ha 0 (by omega_arith)]; exact hebx
  have e1 : arg sE 1 = st + 64 := by rw [ha 1 (by omega_arith)]; exact heax
  have e2 : arg sE 2 = 1 := by rw [ha 2 (by omega_arith)]; exact hecx
  have e3 : arg sE 3 = scr := by rw [ha 3 (by omega_arith)]; exact hedx
  have hbase : (st + 64).setWidth 64 = st.setWidth 64 + BitVec.ofNat 64 64 :=
    setWidth_add (k := 64) (by omega_arith)
  have hbt : (st + 64).toNat = st.toNat + 64 := by
    rw [BitVec.toNat_add, show (64 : BitVec 32).toNat = 64 from rfl, Nat.mod_eq_of_lt (by omega_arith)]
  have espE : (sE.gpr .esp) = E - BitVec.ofNat 32 20 := by
    rw [hsE, State.callEntry_esp, hE16]; bv_omega_arith
  have argA : argAddr sE 0 = (E - BitVec.ofNat 32 16).setWidth 64 := by
    rw [hsE, argAddr_callEntry, hE16]; simp
  -- The stack below `esp`.
  have below16 : Region.Sub (below E 16) (below E 20) := below_sub (by omega_arith) hE
  have ret_sub : Region.Sub ⟨(sE.gpr .esp).setWidth 64, 4⟩ (below E 20) := by
    have := below_inner (sp := E) (a := 4) (b := 20) (k := 16) (by omega_arith) hE
    rw [espE, show E - BitVec.ofNat 32 20 = E - BitVec.ofNat 32 16 - BitVec.ofNat 32 4 by bv_omega_arith]
    exact this
  have sS : Region.Sub ⟨st.setWidth 64, 64⟩ ⟨st.setWidth 64, 192⟩ := Region.sub_prefix (by omega_arith)
  have sB : Region.Sub ⟨(st + 64).setWidth 64, 128 * 1⟩ ⟨st.setWidth 64, 192⟩ := by
    rw [hbase]; exact Proof.Sha256.X86.Stream.sub_offset (by decide) (by decide)
  have sV : Region.Sub ⟨scr.setWidth 64, 224⟩ ⟨scr.setWidth 64, 272⟩ := Region.sub_prefix (by omega_arith)
  have dBS : Region.Disjoint ⟨(st + 64).setWidth 64, 128 * 1⟩ ⟨st.setWidth 64, 64⟩ := by
    intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    rw [hbase] at h₁
    generalize st.setWidth 64 = B at *
    bv_omega_arith
  have hA16 : Region.Sub ⟨argAddr sE 0, 16⟩ (below E 20) := by
    rw [argA]; exact fun a h => below16 a h
  let rdC : List Region := [⟨(st + 64).setWidth 64, 128 * 1⟩, ⟨argAddr sE 0, 16⟩]
  let wrC : List Region := [⟨st.setWidth 64, 64⟩, ⟨scr.setWidth 64, 224⟩]
  refine WP.frame (rs := args) (r := .eax) (by simp) (by decide) (by decide) hn compress_nosp ?_
  refine WP.call (k := Proof.Sha512.compressX86) compress_verified.1 compress_nosp hd (rd := rdC)
    (wr := wrC) ?_ ?_ ?_ fun s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩ => ?_
  · -- The callee's precondition.
    have wA : ∀ j, arg (sE.withRegions rdC wrC) j = arg sE j := fun _ => rfl
    have wAA : argAddr (sE.withRegions rdC wrC) 0 = argAddr sE 0 := rfl
    have wG : (sE.withRegions rdC wrC).gpr = sE.gpr := rfl
    rw [← hsE]
    simp only [Proof.Sha512.compressX86, wA, wAA, wG, State.withRegions_rd, State.withRegions_wr]
    rw [e0, e1, e2, e3]
    refine ⟨rfl, rfl, (d.sub_left sS).sub_right sV, dBS, (d.sub_left sB).sub_right sV,
      (dS.symm.sub_right hA16).sub_left sS |>.symm, (dV.symm.sub_right hA16).sub_left sV |>.symm,
      ((dS.symm.sub_right ret_sub).sub_left sS).symm, ((dV.symm.sub_right ret_sub).sub_left sV).symm,
      by omega_arith, by rw [hbt]; simp only [show (1 : BitVec 32).toNat = 1 from rfl]; omega_arith, by omega_arith, ?_⟩
    show (sE.gpr .esp).toNat + 20 ≤ 2 ^ 32
    rw [espE, sub_toNat hE]; have := E.isLt; omega_arith
  · rw [pushed_rd, pushed_wr]
    apply Covers.of_sub
    intro r hr
    simp only [rdC, wrC, List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ hS), 64, hbase, by simp⟩
    · refine ⟨below (s.gpr .esp) (4 * args.length), List.mem_append_right _ (List.mem_cons_self ..), 0, ?_,
        by simp [args]⟩
      rw [argA, hesp]; simp [args]
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ hS), 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ hV), 0, by simp, by simp⟩
  · rw [pushed_wr]
    apply Covers.of_sub
    intro r hr
    simp only [wrC, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ hS, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ hV, 0, by simp, by simp⟩
  · -- After the call and the frame's pop.
    have hsp : s'.gpr .esp = (pushed args s).gpr .esp := hcs .esp (by simp [calleeSaved])
    have hF : Frame [⟨st.setWidth 64, 64⟩, ⟨scr.setWidth 64, 224⟩, below E 20] s.mem s'.mem := by
      refine (Frame.sub (pushed_frame (by decide) hn) fun r hr => ?_).trans (Frame.sub hf fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨below E 20, by simp, by rw [hesp]; simpa [args] using below16⟩
      · simp only [wrC, compress_stackUse, List.cons_append, List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · refine ⟨below E 20, by simp, ?_⟩
          rw [hE16]
          exact below_inner (by omega_arith) hE
    -- The callee's memory on entry is ours outside the stack.
    have hFe : Frame [below E 20] s.mem sE.mem := by
      rw [hsE, State.callEntry_mem]
      have h20 : (pushed args s).gpr .esp - 4 = E - BitVec.ofNat 32 20 := by rw [hE16]; bv_omega_arith
      refine Frame.writeW (Frame.sub (pushed_frame (by decide) hn) fun r hr => ?_) (List.mem_singleton_self _) _
        ?_
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨below E 20, by simp, by rw [hesp]; simpa [args] using below16⟩
      · rw [h20]; exact below_top (k := 20) (Nat.le_refl _) hE (by omega_arith)
    have hst : stateAt sE.mem (st.setWidth 64) = stateAt s.mem (st.setWidth 64) :=
      Proof.Sha512.Stream.stateAt_congr fun i hi =>
        hFe.bytes (R := ⟨st.setWidth 64, 192⟩) (by simpa using dS.symm) (by simp) (show _ < 192 by omega_arith)
    have hblk : blockAt sE.mem (st.setWidth 64 + 64) = blockAt s.mem (st.setWidth 64 + 64) := by
      simp only [blockAt]
      refine Proof.Sha512.Stream.parseBlock_congr fun k hk => ?_
      rw [show st.setWidth 64 + 64 + BitVec.ofNat 64 k = st.setWidth 64 + BitVec.ofNat 64 (64 + k) by
        rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl]
      exact hFe.bytes (R := ⟨st.setWidth 64, 192⟩) (by simpa using dS.symm) (by simp) (show _ < 192 by omega_arith)
    have hpost' : stateAt s'.mem (st.setWidth 64) =
        compress (stateAt s.mem (st.setWidth 64)) (blockAt s.mem (st.setWidth 64 + 64)) := by
      have := (show stateAt s₂.mem ((arg (sE.withRegions rdC wrC) 0).setWidth 64) =
        compressBlocks (stateAt (sE.withRegions rdC wrC).mem ((arg (sE.withRegions rdC wrC) 0).setWidth 64))
          (sE.withRegions rdC wrC).mem ((arg (sE.withRegions rdC wrC) 1).setWidth 64)
          (arg (sE.withRegions rdC wrC) 2).toNat from hpost)
      rw [show arg (sE.withRegions rdC wrC) = arg sE from rfl, e0, e1, e2, hm₂, State.withRegions_mem,
        show (1 : BitVec 32).toNat = 1 from rfl, compressBlocks_one, hbase, hst] at this
      rw [this, ← hblk]; rfl
    refine hQ _ (by rw [popped_rd, hrd, pushed_rd]) (by rw [popped_wr, hwr, pushed_wr]; rfl)
      (fun r hr => ?_) (by rw [popped_mem]; exact hF) (by rw [popped_mem]; exact hpost')
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [popped_gpr _ _ _ (by decide) (by decide), hcs _ (by simp [calleeSaved]), pushed_gpr _ _ (by decide)]
    · rw [popped_gpr _ _ _ (by decide) (by decide), hcs _ (by simp [calleeSaved]), pushed_gpr _ _ (by decide)]
    · rw [popped_gpr _ _ _ (by decide) (by decide), hcs _ (by simp [calleeSaved]), pushed_gpr _ _ (by decide)]
    · rw [popped_gpr _ _ _ (by decide) (by decide), hcs _ (by simp [calleeSaved]), pushed_gpr _ _ (by decide)]
    · rw [popped_esp, hsp, hE16, hesp]; simp only [args, List.length_cons, List.length_nil]
      exact BitVec.sub_add_cancel _ _

/-- `compressAt d`: the call of the compression function on the buffer of the
state at `ebx`, with the scratch space whose address is at `[esp + d]`. -/
theorem compressAt_ok {s : State} {st scr E : BitVec 32} {d : Nat}
    (hesp : s.gpr .esp = E) (hebx : s.gpr .ebx = st)
    (hin : InRegions (s.rd ++ s.wr) (addr E d) 4) (hscr : s.mem.readW (addr E d) 32 = scr)
    (f₀ : st.toNat + 192 ≤ 2 ^ 32) (f₃ : scr.toNat + 272 ≤ 2 ^ 32) (hE : 20 ≤ E.toNat)
    (dd : Region.Disjoint ⟨st.setWidth 64, 192⟩ ⟨scr.setWidth 64, 272⟩)
    (dS : Region.Disjoint (below E 20) ⟨st.setWidth 64, 192⟩)
    (dV : Region.Disjoint (below E 20) ⟨scr.setWidth 64, 272⟩)
    (hS : ⟨st.setWidth 64, 192⟩ ∈ s.wr) (hV : ⟨scr.setWidth 64, 272⟩ ∈ s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ [Reg.ebx, .esi, .edi, .ebp, .esp], s'.gpr r = s.gpr r) →
      Frame [⟨st.setWidth 64, 64⟩, ⟨scr.setWidth 64, 224⟩, below E 20] s.mem s'.mem →
      stateAt s'.mem (st.setWidth 64) =
        compress (stateAt s.mem (st.setWidth 64)) (blockAt s.mem (st.setWidth 64 + 64)) → Q s') :
    WP isa (compressAt d) s Q := by
  refine WP.seq (wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_movi fun s₃ u₃ =>
    wp_movm (a := addr E d) (by rw [ea_of (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hesp])]) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin)
      fun s₄ u₄ => WP.block_nil ?_)
  have g : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₄.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₄.other r h3, u₃.other r h2, u₂.other r h1, u₁.other r h1]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine compressCall_ok (st := st) (scr := scr) (E := E)
    (by rw [g _ (by decide) (by decide) (by decide), hesp]) (by rw [g _ (by decide) (by decide) (by decide), hebx])
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, hebx])
    (by rw [u₄.other _ (by decide), u₃.gpr]) (by rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem, hscr])
    f₀ f₃ hE dd dS dV (by rw [wr₄]; exact hS) (by rw [wr₄]; exact hV) fun s' hrd hwr hg hf hst => ?_
  rw [m₄] at hf hst
  refine hQ s' (hrd.trans rd₄) (hwr.trans wr₄) (fun r hr => ?_) hf hst
  rw [hg r hr]
  refine g r ?_ ?_ ?_ <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## Lemmas shared by `update` and `finalize` -/

/-- The contract's stack region. -/
theorem stk_eq {E : BitVec 32} (h : 20 ≤ E.toNat) : below E 20 = ⟨E.setWidth 64 - 20, 20⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

/-- The count of bytes buffered, from the low word of the count. -/
theorem and127 (x : BitVec 32) : x &&& 127 = BitVec.ofNat 32 (x.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (127 : BitVec 32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

end VG.Proof.Sha512.X86.Stream
