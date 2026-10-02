import VerifiedGarbage.Proof.Pbkdf2.AArch64.Iterate
import VerifiedGarbage.Proof.Hmac.Generic.Implies

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on AArch64: constant time

As on x86-64 (`Proof/Pbkdf2/X86_64/IterateCT.lean`): this holds for any
compression function (`CompOk`), so it is proven once for every
implementation. The taint analysis cannot prove it without looking into the
compression function, so we relate two runs (`RelCT`): at every point,
correctness determines our registers from the public arguments alone, so they
agree; between the calls, the taint analysis proves each block constant time
from that (`Checks`, evaluated for each hash function, since the code depends
on its sizes); and the calls are constant time by the compression function's
own proof (`compressAt_rel`).
-/

namespace VG.Proof.Pbkdf2.AArch64

open VG VG.AArch64
open VG.Impl.Pbkdf2.AArch64 (Params loadKey xorW compressBlock body prologue epilogue main iterate)
open VG.Impl.MdStream.AArch64 (mov)
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.AArch64 (wp_mov eval_zero ofNat_beq_zero)
open VG.Spec.Sha256 (bytesAt)
open VG.Spec.Hmac (StreamingHash)

/-- The registers the blocks between the calls use. -/
abbrev regsS : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24]

/-- The taint checks of the pieces of `iterate` between its calls, which
depend on the hash function's sizes, its length field and its digest. -/
structure Checks (P : Params) (D : Nat) : Prop where
  ext : ∃ hc, (taint.check (Taint.ofRegs []) (.block [.addImm .w .x2 .x2 0]) hc).isSome = true
  pro : ∃ hc, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) (.block (prologue P D)) hc).isSome = true
  load : ∃ hc, (taint.check (Taint.ofRegs regsS) (.block (loadKey P 0)) hc).isSome = true
  arg : ∃ hc, (taint.check (Taint.ofRegs regsS) (.block [mov .x1 .x21]) hc).isSome = true
  mid : ∃ hc, (taint.check (Taint.ofRegs regsS)
    (.block (Impl.Pbkdf2.AArch64.digest P D ++ loadKey P (P.N + P.B))) hc).isSome = true
  fin : ∃ hc, (taint.check (Taint.ofRegs regsS) (.block (Impl.Pbkdf2.AArch64.digest P D ++
    (List.range (D / 4)).flatMap xorW ++ [.subImm .x .x24 .x24 1])) hc).isSome = true
  epi : ∃ hc, (taint.check (Taint.ofRegs [.x20]) (.block (epilogue P)) hc).isSome = true
  ite : ∃ hc, (taint.check (Taint.ofRegs []) (.block []) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  x0 : s₀.gpr .x0 = s₀'.gpr .x0
  x1 : s₀.gpr .x1 = s₀'.gpr .x1
  x2 : (s₀.gpr .x2).setWidth 32 = (s₀'.gpr .x2).setWidth 32
  x3 : s₀.gpr .x3 = s₀'.gpr .x3
  x4 : s₀.gpr .x4 = s₀'.gpr .x4
  sp : s₀.sp = s₀'.sp

theorem PubEq.nn {s₀ s₀' : State} (hq : PubEq s₀ s₀') : nn s₀ = nn s₀' :=
  congrArg BitVec.toNat hq.x2

/-- Agreement on `rs` and the stack pointer. -/
theorem agree_of {rs : List Reg} {s s' : State} (hsp : s.sp = s'.sp) (h : ∀ r ∈ rs, s.gpr r = s'.gpr r) :
    AArch64.Taint.Agree (AArch64.Taint.ofRegs rs) s s' :=
  ⟨hsp, fun r hr => h r (AArch64.Taint.mem_ofRegs.mp hr)⟩

/-- The state during a step, with `v` in `x24`. -/
structure St (P : Params) (D W : Nat) (H : Md P.B P.N P.L) (s₀ : State) (v : Addr) (s : State) : Prop
    extends Regs P D W s₀ s where
  x24 : s.gpr .x24 = v
  pad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D

section
variable {P : Params} {D W : Nat} {H : Md P.B P.N P.L}

/-- The registers the blocks use agree in two runs. -/
theorem St.agree {s₀ s₀' : State} (hq : PubEq s₀ s₀') {v : Addr} {s s' : State} (h : St P D W H s₀ v s)
    (h' : St P D W H s₀' v s') : AArch64.Taint.Agree (AArch64.Taint.ofRegs regsS) s s' := by
  refine agree_of (by rw [h.sp, h'.sp, hq.sp]) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, hv, hv, scr, scr, hq.x4]
  · rw [h.x20, h'.x20, scr, scr, hq.x4]
  · rw [h.x21, h'.x21, blk, blk, scr, scr, hq.x4]
  · rw [h.x22, h'.x22, key, key, hq.x0]
  · rw [h.x23, h'.x23, tp, tp, hq.x3]
  · rw [h.x24, h'.x24]

theorem St.of_inv {s₀ : State} {r : Nat} {s : State} (h : Inv P D W H s₀ (r + 1) s) :
    St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s :=
  ⟨h.toRegs, h.x24, h.pad⟩

variable (hz : Sizes P D W) {s₀ : State} (hp : Pre P D W s₀) {v : Addr}
include hz hp

/-! ## What each piece of a step does, in one run -/

theorem load_st (hR : H.Reloc) {o : Nat} (ho : o + P.N ≤ 2 * (P.N + P.B)) (ho4 : o % 4 = 0) {s : State}
    (h : St P D W H s₀ v s) :
    WP isa (.block (loadKey P o)) s (St P D W H s₀ v) := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL
  rw [← List.append_nil (loadKey P o)]
  exact load_ok hz hp hR h.toRegs ho ho4 fun s' g rd wr sp f _ => WP.block_nil
    ⟨h.toRegs.write (fun r hr => g r (ne9 r hr)) rd wr sp (frame_scr (a := P.so + 56) (by omega) f),
      (g _ (by decide)).trans h.x24,
      (Memory.frame_bytesAt f (fun r hr => blk_disj hz (by omega) r (by simp at hr; simp [hr])) (by omega)).trans
        h.pad⟩

theorem cmp_st {name : String} {code : Prog isa} (hf : CompOk H P.so code) {s : State} (h : St P D W H s₀ v s) :
    WP isa (compressBlock name code) s (St P D W H s₀ v) := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.DN; have := hz.pad
  have := hz.NL
  exact cmp_ok hz hp hf h.toRegs fun s' h' x24 f _ =>
    ⟨h', x24.trans h.x24, (Memory.frame_bytesAt f (blk_disj hz (by omega)) (by omega)).trans h.pad⟩

theorem mid_st (hs : Shape H) (hR : H.Reloc) {s : State} (h : St P D W H s₀ v s) :
    WP isa (.block (Impl.Pbkdf2.AArch64.digest P D ++ loadKey P (P.N + P.B))) s (St P D W H s₀ v) := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.fits; have := hz.NL; have := hz.N4
  refine digest_ok hz hp hs h.toRegs h.pad fun s' g rd wr sp f _ p => ?_
  exact load_st hz hp hR (by omega) (by rcases hz.B with h | h <;> omega)
    ⟨h.toRegs.write (fun r hr => g r (ne9 r hr)) rd wr sp (frame_scr (a := P.so + 56 + P.N) (by omega) f),
      (g _ (by decide)).trans h.x24, p⟩

/-! ## Two runs -/

variable {s₀' : State} (hp' : Pre P D W s₀') (hq : PubEq s₀ s₀')
include hp' hq

theorem cmp_rel {name : String} {code : Prog isa} (hf : CompOk H P.so code) (hc : Checks P D) :
    RelCT isa (fun s s' => St P D W H s₀ v s ∧ St P D W H s₀' v s') (compressBlock name code) fun s s' =>
      St P D W H s₀ v s ∧ St P D W H s₀' v s' := by
  obtain ⟨_, ha⟩ := hc.arg
  have mv : ∀ {s₀ : State}, Pre P D W s₀ → ∀ {s : State}, St P D W H s₀ v s →
      WP isa (.block [mov .x1 .x21]) s fun s => St P D W H s₀ v s ∧ s.gpr .x1 = blk P s₀ :=
    by intro _ _ _ h; exact wp_mov fun s₁ u₁ => WP.block_nil ⟨⟨h.toRegs.write (fun r hr => u₁.other r (ne1 r hr)) u₁.rd u₁.wr
      u₁.sp (by rw [u₁.mem]; exact Frame.refl _ _), (u₁.other _ (by decide)).trans h.x24,
      by rw [u₁.mem]; exact h.pad⟩, by rw [u₁.gpr, h.x21]⟩
  have su : RelCT isa (fun s s' => St P D W H s₀ v s ∧ St P D W H s₀' v s') (.block [mov .x1 .x21])
      fun s s' => (St P D W H s₀ v s ∧ s.gpr .x1 = blk P s₀) ∧ (St P D W H s₀' v s' ∧ s'.gpr .x1 = blk P s₀') :=
    ((RelCT.taint (A := taint) (Taint.ofRegs regsS) (fun _ _ h => St.agree hq h.1 h.2) ha).wp
      fun _ _ h => ⟨mv hp h.1, mv hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have call := compressAt_rel (H := H) hf (name := name) (st := hv P s₀) (scr := scr s₀) (src := blk P s₀)
    (P' := fun s s' => (St P D W H s₀ v s ∧ s.gpr .x1 = blk P s₀) ∧ (St P D W H s₀' v s' ∧ s'.gpr .x1 = blk P s₀'))
    fun s s' ⟨⟨h, hsi⟩, ⟨h', hsi'⟩⟩ => by
      have e : hv P s₀' = hv P s₀ ∧ scr s₀' = scr s₀ ∧ blk P s₀' = blk P s₀ := by
        refine ⟨?_, ?_, ?_⟩ <;> simp only [hv, blk, scr, hq.x4]
      have c' := callOk_of hz hp' h'.toRegs hsi'
      rw [e.1, e.2.1, e.2.2] at c'
      exact ⟨callOk_of hz hp h.toRegs hsi, c', by rw [h.sp, h'.sp, hq.sp]⟩
  exact ((su.seq call).wp fun _ _ h => ⟨cmp_st hz hp hf h.1, cmp_st hz hp' hf h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem body_rel (hs : Shape H) (hR : H.Reloc) {name : String} {code : Prog isa} (hf : CompOk H P.so code)
    (hc : Checks P D) {r : Nat} :
    RelCT isa (fun s s' => Inv P D W H s₀ (r + 1) s ∧ Inv P D W H s₀' (r + 1) s') (body P D name code)
      fun s s' => (eval (.nonzero .x .x24) s = some (r != 0) ∧ Inv P D W H s₀ r s) ∧
        (eval (.nonzero .x .x24) s' = some (r != 0) ∧ Inv P D W H s₀' r s') := by
  have := so_le hz; have := N_le hz; have := B_le hz
  obtain ⟨_, hl⟩ := hc.load
  obtain ⟨_, hm⟩ := hc.mid
  obtain ⟨_, hfi⟩ := hc.fin
  have l0 : RelCT isa (fun s s' => Inv P D W H s₀ (r + 1) s ∧ Inv P D W H s₀' (r + 1) s') (.block (loadKey P 0))
      fun s s' => St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧ St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs regsS) (fun _ _ h =>
      St.agree hq (St.of_inv h.1) (St.of_inv h.2)) hl).wp
      fun _ _ h => ⟨load_st hz hp hR (by omega) rfl (St.of_inv h.1),
        load_st hz hp' hR (by omega) rfl (St.of_inv h.2)⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have dl : RelCT isa (fun s s' => St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧
        St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s')
      (.block (Impl.Pbkdf2.AArch64.digest P D ++ loadKey P (P.N + P.B)))
      fun s s' => St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧ St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs regsS) (fun _ _ h => St.agree hq h.1 h.2)
      hm).wp fun _ _ h => ⟨mid_st hz hp hs hR h.1, mid_st hz hp' hs hR h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have fin : RelCT isa (fun s s' => St P D W H s₀ (BitVec.ofNat 64 (r + 1)) s ∧
        St P D W H s₀' (BitVec.ofNat 64 (r + 1)) s')
      (.block (Impl.Pbkdf2.AArch64.digest P D ++ (List.range (D / 4)).flatMap xorW ++ [.subImm .x .x24 .x24 1]))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs regsS) (fun _ _ h => St.agree hq h.1 h.2) hfi
  have c := cmp_rel hz hp hp' hq (v := BitVec.ofNat 64 (r + 1)) hf hc (name := name)
  exact ((l0.seq (c.seq (dl.seq (c.seq fin)))).wp fun _ _ h =>
    ⟨body_ok hz hp hs hR hf h.1, body_ok hz hp' hs hR hf h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem loop_rel (hs : Shape H) (hR : H.Reloc) {name : String} {code : Prog isa} (hf : CompOk H P.so code)
    (hc : Checks P D) {n : Nat} :
    RelCT isa (fun s s' => Inv P D W H s₀ (n + 1) s ∧ Inv P D W H s₀' (n + 1) s')
      (.loop (body P D name code) (.nonzero .x .x24)) fun _ _ => True :=
  RelCT.loop (M := isa) (body := body P D name code) (c := .nonzero .x .x24) (Q := fun _ _ => True)
    (fun m s s' => Inv P D W H s₀ (m + 1) s ∧ Inv P D W H s₀' (m + 1) s') (fun m => by
      intro s s' t t' u u' h e e'
      obtain ⟨ht, ⟨z, i⟩, ⟨z', i'⟩⟩ := body_rel hz hp hp' hq hs hR hf hc _ _ _ _ _ _ h e e'
      refine ⟨ht, z.trans z'.symm, fun _ => trivial, fun hc' => ?_⟩
      have hc'' : some (m != 0) = some true := z.symm.trans hc'
      cases m with
      | zero => cases hc''
      | succ m => exact ⟨m, by omega, i, i'⟩) n

theorem main_rel {S : StreamingHash} {iv : H.HV} (ho : HashOk P D W S H iv) {name : String}
    {code : Prog isa} (hf : CompOk H P.so code) (hc : Checks P D) :
    RelCT isa (fun s s' => s = zext s₀ ∧ s' = zext s₀') (main P D name code) fun _ _ => True := by
  obtain ⟨_, hpr⟩ := hc.pro
  obtain ⟨_, hep⟩ := hc.epi
  obtain ⟨_, hit⟩ := hc.ite
  have hlt : ∀ {s₀ : State}, nn s₀ < 2 ^ 64 := fun {s₀} => by
    have := ((s₀.gpr .x2).setWidth 32).isLt; simp only [nn]; omega
  have pro : RelCT isa (fun s s' => s = zext s₀ ∧ s' = zext s₀') (.block (prologue P D)) fun s s' =>
      Inv P D W H s₀ (nn s₀) s ∧ Inv P D W H s₀' (nn s₀') s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
      (P := fun s s' => s = zext s₀ ∧ s' = zext s₀') (fun _ _ ⟨e, e'⟩ => by
        subst e e'
        refine agree_of (by rw [(zext_upd _).sp, (zext_upd _).sp, hq.sp]) fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [(zext_upd _).other _ (by decide), (zext_upd _).other _ (by decide), hq.x0]
        · rw [(zext_upd _).other _ (by decide), (zext_upd _).other _ (by decide), hq.x1]
        · rw [zext_x2, zext_x2, hq.nn]
        · rw [(zext_upd _).other _ (by decide), (zext_upd _).other _ (by decide), hq.x3]
        · rw [(zext_upd _).other _ (by decide), (zext_upd _).other _ (by decide), hq.x4]) hpr).wp
      fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hz hp ho.shape ho.lenOk, prologue_ok hz hp' ho.shape ho.lenOk⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have br : RelCT isa (fun s s' => Inv P D W H s₀ (nn s₀) s ∧ Inv P D W H s₀' (nn s₀') s')
      (.ite (.zero .x .x24) (.block []) (.loop (body P D name code) (.nonzero .x .x24)))
      fun s s' => Inv P D W H s₀ 0 s ∧ Inv P D W H s₀' 0 s' := by
    refine (RelCT.ite (fun s s' h => ?_) (RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ h => agree_of (by rw [h.1.1.sp, h.1.2.sp, hq.sp]) (by simp)) hit) ?_).wp
      (fun _ _ h => ⟨loop_ok hz hp ho.shape ho.reloc hf h.1, loop_ok hz hp' ho.shape ho.reloc hf h.2⟩)
      |>.mono (fun _ _ h => h) fun _ _ h => h.2
    · show eval (.zero .x .x24) s = eval (.zero .x .x24) s'
      rw [eval_zero, eval_zero, h.1.x24, h.2.x24, hq.nn]
    · intro s s' t t' u u' ⟨⟨i, i'⟩, hc'⟩ e e'
      have z : eval (.zero .x .x24) s = some (decide (nn s₀ = 0)) := by
        rw [eval_zero, i.x24, ofNat_beq_zero hlt]
      have hc'' : some (decide (nn s₀ = 0)) = some false := z.symm.trans hc'
      have hne : nn s₀ ≠ 0 := fun h0 => by rw [h0] at hc''; cases hc''
      obtain ⟨m, hm⟩ : ∃ m, nn s₀ = m + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hne).symm⟩
      rw [hm] at i
      rw [← hq.nn, hm] at i'
      exact loop_rel hz hp hp' hq ho.shape ho.reloc hf hc _ _ _ _ _ _ ⟨i, i'⟩ e e'
  have epi : RelCT isa (fun s s' => Inv P D W H s₀ 0 s ∧ Inv P D W H s₀' 0 s') (.block (epilogue P))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.x20]) (fun _ _ h => agree_of (by rw [h.1.sp, h.2.sp, hq.sp])
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.1.x20, h.2.x20, scr, scr, hq.x4]) hep
  exact pro.seq (br.seq epi)

theorem iterate_rel {S : StreamingHash} {iv : H.HV} (ho : HashOk P D W S H iv) {name : String}
    {code : Prog isa} (hf : CompOk H P.so code) (hc : Checks P D) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (iterate P D name code) fun _ _ => True := by
  obtain ⟨_, hex⟩ := hc.ext
  have ext : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block [.addImm .w .x2 .x2 0])
      fun s s' => s = zext s₀ ∧ s' = zext s₀' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ ⟨e, e'⟩ => agree_of (by rw [e, e', hq.sp])
      (by simp)) hex).wp (F₁ := fun s => s = zext s₀) (F₂ := fun s => s = zext s₀')
      fun _ _ ⟨e, e'⟩ => by
        subst e e'
        exact ⟨MdStream.AArch64.WP.cons (zext_exec _) (WP.block_nil rfl),
          MdStream.AArch64.WP.cons (zext_exec _) (WP.block_nil rfl)⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  exact ext.seq (main_rel hz hp hp' hq ho hf hc)

end

/-! ## Verified -/

theorem pubEq_of {S : StreamingHash} {W : Nat} {s₁ s₂ : State} (h : (iterK S W).pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- `iterate` is verified against `iterK`, for any hash function the proof
supports (`HashOk`), whose pieces of code the taint analysis accepts
(`Checks`), and any compression function (`CompOk`). -/
theorem verified {P : Params} {D W : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : HashOk P D W S H iv) (hc : Checks P D) {name : String} {code : Prog isa} (hf : CompOk H P.so code)
    (hsat : ∃ s, (iterK S W).pre s) :
    Verified AArch64.target (iterate P D name code) (iterK S W) := by
  refine ⟨iterate_ok ho hf, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  exact (iterate_rel ho.sizes (pre_of ho.link.hS ho.link.hD h₁) (pre_of ho.link.hS ho.link.hD h₂)
    (pubEq_of hpub) ho hf hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- `iterK` implies the shared contract, for any hash function and scratch
space, given that the shared contract is satisfiable. -/
theorem iterImp (S : StreamingHash) (W : Nat) (h : ∃ s, (Spec.Pbkdf2.iterateContract S W AArch64.abi).pre s) :
    (iterK S W).Implies (Spec.Pbkdf2.iterateContract S W AArch64.abi) := by
  generic_implies [
    Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, iterK, AArch64.abi, AArch64.argRegs] using h

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes and `8 W` bytes of scratch space. -/
def iterSat (S D W : Nat) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x1 => 0x20000 | .x3 => 0x30000 | .x4 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x10000, 2 * S⟩, ⟨0x20000, D⟩]
  wr := [⟨0x30000, D⟩, ⟨0x40000, 8 * W⟩]

end VG.Proof.Pbkdf2.AArch64
