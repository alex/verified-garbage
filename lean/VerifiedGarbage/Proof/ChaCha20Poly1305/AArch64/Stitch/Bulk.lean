import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Body
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Xor

/-!
# ChaCha20 and Poly1305 together (AArch64): the whole chunks

`Stitch.bulk`, from a state with the stream's arguments (`Mixed8.XPre`, with
its working space 64 bytes after the state: `BPre`), at least 512 bytes of
data, and the accumulator in `x21`–`x23`: the chunks that fit encrypted (or
decrypted), as `Mixed8.bulk_ok`, and the bytes they absorbed: when
decrypting, every chunk's data as it was on entry; when encrypting, the
output of every chunk but the last.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64.Stitch

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Stitch VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64 (Words not_words_x1 not_words_x0 not_words_preserved)
open VG.Proof.ChaCha20.AArch64.Mixed8 (CP Chunked source sr scalarBuf dr LInv GPInv BulkInv
  cp_of_inv enter_ok leave_ok zero_batches)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {sve : Bool}

theorem WP.both {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁)
    (h₂ : WP isa c s Q₂) : WP isa c s fun u => Q₁ u ∧ Q₂ u := by
  obtain ⟨t₁, u₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, u₂, e₂, q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, u₁, e₁, q₁, q₂⟩

/-- The kernel's loop invariant on entry. -/
theorem linv0 (s₀ : State) : LInv s₀ 0 s₀ := by
  refine ⟨rfl, ?_, ?_, rfl, by omega, fun _ _ _ _ _ => rfl, rfl, rfl, rfl, ?_, ?_, Frame.refl _ _⟩
  · simp only [Nat.mul_zero, BitVec.add_zero]
  · simp only [Nat.mul_zero, Nat.sub_zero]
    simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat 64 (s₀.gpr .x2)).symm
  · exact (VG.Proof.ChaCha20.ctr_zero _).symm
  · intro k _; simp only [Nat.mul_zero, Nat.not_lt_zero, ite_false]

/-- The key is apart from what `enter` stores. -/
theorem key_enter {s₀ : State} (hp : BPre s₀) : ∀ r ∈ enterR s₀, (keyR s₀).Disjoint r := by
  have e (d : Nat) : s₀.gpr .x3 + BitVec.ofNat 64 d = st s₀ + BitVec.ofNat 64 (64 + d) := by
    rw [show s₀.gpr .x3 = bp s₀ from rfl, hp.bp, BitVec.add_assoc, ← BitVec.ofNat_add]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [keyR, e] <;>
    exact Offset.disjoint (st s₀) (by decide) (by decide) (by decide)

/-- The key is apart from the regions a chunk writes. -/
theorem key_chunk {s₀ s : State} (hp : BPre s₀) {t : Nat} (h : LInv s₀ t s)
    (hge : 512 * t + 512 ≤ L s₀) :
    ∀ r ∈ [sr s, scalarBuf s, dr s], (keyR s₀).Disjoint r := by
  have hkey : (keyR s₀).Sub (bR s₀) := hp.key_sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa only [sr, h.x0] using hp.st_b.symm.sub_left hkey
  · simp only [keyR, scalarBuf, h.x3, hp.bp]
    exact Offset.disjoint (st s₀) (d := 224) (n := 16) (e := 64) (k := 128) (by decide)
      (by decide) (by decide)
  · simp only [dr, h.x1]
    exact (hp.d_b.symm.sub_left hkey).sub_right
      (VG.Proof.ChaCha20.AArch64.Mixed8.win_sub hge)

/-- The key's words in a state with the entry state's `x0`, whose memory
differs from the entry state's only away from the key. -/
theorem rword_eq {s₀ s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hx0 : s.gpr .x0 = s₀.gpr .x0) (hd : ∀ r ∈ rs, (keyR s₀).Disjoint r) :
    ∀ d, (d = Poly.r0Off ∨ d = Poly.r1Off) → Poly.rword s d = Poly.rword s₀ d :=
  rword_of hf hx0 hd

/-- Data the loop has not reached is as on entry. -/
theorem window_orig {s₀ x : State} {t : Nat} (h : LInv s₀ t x) (hge : 512 * t + 512 ≤ L s₀) :
    bytesAt x.mem (dp s₀ + BitVec.ofNat 64 (512 * t)) 512 =
      bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 (512 * t)) 512 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.data _ (by omega), ite_eq_right (by omega)]

/-- Data the loop has passed is the output. -/
theorem prefix_ct {s₀ x : State} {t n : Nat} (h : LInv s₀ t x) (hn : n ≤ 512 * t) :
    bytesAt x.mem (dp s₀) n = (List.range n).map fun k => D0 s₀ k ^^^ (KS s₀).getD k 0 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  rw [h.data _ (by have := h.le; omega), ite_eq_left (by omega)]

theorem bytesAt_join (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p n ++ bytesAt m (p + BitVec.ofNat 64 n) 512 = bytesAt m p (n + 512) :=
  (Poly1305.bytesAt_add m p n 512).symm

theorem absorb_join {R a : Nat} {X Y : List Byte} (hx : X.length % 16 = 0) :
    absorbAll R (absorbAll R a X) Y = absorbAll R a (X ++ Y) :=
  (Poly1305.absorbAll_append hx).symm

theorem eval_zero5 {s : State} {n : Nat}
    (h : s.gpr .x5 = BitVec.ofNat 64 (if n < 512 then 1 else 0)) :
    isa.eval (.zero .x .x5) s = some (decide (512 ≤ n)) := zero_batches h

/-- The loop of chunks that decrypt. -/
theorem chunks_open {s₀ : State} (hp : BPre s₀) {R a : Nat} {s : State} {t : Nat}
    (hge : 512 * t + 512 ≤ L s₀) (h : BulkInv (rebase s₀ s) t s)
    (ha : Acc R (absorbAll R a (bytesAt s₀.mem (dp s₀) (512 * t))) s) :
    WP isa (chunks sve false) s fun u => ∃ T, L s₀ - 512 * T < 512 ∧ t < T ∧
      BulkInv (rebase s₀ u) T u ∧ Acc R (absorbAll R a (bytesAt s₀.mem (dp s₀) (512 * T))) u := by
  let Inv : Nat → State → Prop := fun n x => ∃ i, n = L s₀ - 512 * i ∧ 512 ≤ n ∧ t ≤ i ∧
    BulkInv (rebase s₀ x) i x ∧ Acc R (absorbAll R a (bytesAt s₀.mem (dp s₀) (512 * i))) x
  refine WP.loop (M := isa) Inv ?_ (L s₀ - 512 * t) s ⟨t, rfl, by omega, Nat.le_refl _, h, ha⟩
  rintro n x ⟨i, rfl, hge', hti, hx, hax⟩
  have hb : dp (rebase s₀ x) + BitVec.ofNat 64 (512 * i) =
      dataOf false (dp (rebase s₀ x) + BitVec.ofNat 64 (512 * i)) := by
    simp only [dataOf, Bool.false_eq_true, ite_false, BitVec.add_zero]
  refine (body_ok false (hp.rebase x) (t := i) (by simp; omega) hx (w := 512 * i)
    (by simp; omega) hb hax).mono fun v ⟨⟨hv, h5⟩, hav⟩ => ?_
  rw [rebase_rebase] at hv
  have hwin := window_orig hx.toLInv (by simp; omega)
  simp only [dp_rebase, rebase_mem] at hwin hav
  rw [hwin, absorb_join (by rw [Poly1305.length_bytesAt]; omega), bytesAt_join,
    show 512 * i + 512 = 512 * (i + 1) by omega] at hav
  rw [L_rebase] at h5
  have hc := eval_zero5 h5
  by_cases he : L s₀ - 512 * (i + 1) < 512
  · left
    rw [decide_eq_false (show ¬ 512 ≤ L s₀ - 512 * (i + 1) by omega)] at hc
    exact ⟨hc, i + 1, he, by omega, hv, hav⟩
  · right
    rw [decide_eq_true (show 512 ≤ L s₀ - 512 * (i + 1) by omega)] at hc
    exact ⟨hc, L s₀ - 512 * (i + 1), by omega, i + 1, rfl, by omega, by omega, hv, hav⟩

/-- The loop of chunks that encrypt, each absorbing the output of the one before. -/
theorem chunks_seal {s₀ : State} (hp : BPre s₀) {R a : Nat} {s : State} {t : Nat} (ht : 1 ≤ t)
    (hge : 512 * t + 512 ≤ L s₀) (h : BulkInv (rebase s₀ s) t s)
    (ha : Acc R (absorbAll R a (bytesAt s.mem (dp s₀) (512 * (t - 1)))) s) :
    WP isa (chunks sve true) s fun u => ∃ T, L s₀ - 512 * T < 512 ∧ t < T ∧
      BulkInv (rebase s₀ u) T u ∧
      Acc R (absorbAll R a (bytesAt u.mem (dp s₀) (512 * (T - 1)))) u := by
  let Inv : Nat → State → Prop := fun n x => ∃ i, n = L s₀ - 512 * i ∧ 512 ≤ n ∧ t ≤ i ∧
    BulkInv (rebase s₀ x) i x ∧ Acc R (absorbAll R a (bytesAt x.mem (dp s₀) (512 * (i - 1)))) x
  refine WP.loop (M := isa) Inv ?_ (L s₀ - 512 * t) s ⟨t, rfl, by omega, Nat.le_refl _, h, ha⟩
  rintro n x ⟨i, rfl, hge', hti, hx, hax⟩
  have hb : dp (rebase s₀ x) + BitVec.ofNat 64 (512 * i) =
      dataOf true (dp (rebase s₀ x) + BitVec.ofNat 64 (512 * (i - 1))) := by
    simp only [dataOf, ite_true, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  refine (body_ok true (hp.rebase x) (t := i) (by simp; omega) hx (w := 512 * (i - 1))
    (by simp; omega) hb hax).mono fun v ⟨⟨hv, h5⟩, hav⟩ => ?_
  rw [rebase_rebase] at hv
  simp only [dp_rebase] at hav
  rw [absorb_join (by rw [Poly1305.length_bytesAt]; omega), bytesAt_join,
    show 512 * (i - 1) + 512 = 512 * (i + 1 - 1) by omega] at hav
  have p1 := prefix_ct hx.toLInv (n := 512 * (i + 1 - 1)) (by omega)
  have p2 := prefix_ct hv.toLInv (n := 512 * (i + 1 - 1)) (by omega)
  simp only [dp_rebase, D0_rebase, KS_rebase] at p1 p2
  rw [p1, ← p2] at hav
  rw [L_rebase] at h5
  have hc := eval_zero5 h5
  by_cases he : L s₀ - 512 * (i + 1) < 512
  · left
    rw [decide_eq_false (show ¬ 512 ≤ L s₀ - 512 * (i + 1) by omega)] at hc
    exact ⟨hc, i + 1, he, by omega, hv, hav⟩
  · right
    rw [decide_eq_true (show 512 ≤ L s₀ - 512 * (i + 1) by omega)] at hc
    exact ⟨hc, L s₀ - 512 * (i + 1), by omega, i + 1, rfl, by omega, by omega, hv, hav⟩

/-- `leave` only loads. -/
theorem leave_mem (s : State)
    (hi : ∀ d n, d + n ≤ 320 → InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 d) n) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.leave) s fun u => u.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Impl.ChaCha20.AArch64.Mixed8.leave,
    VG.Impl.ChaCha20.AArch64.Mixed5.leave, List.cons_append, List.nil_append, runBlock_cons,
    runBlock_nil, exec, addr, Size.bytes, Size.bits, ite_true, ite_false, State.load,
    hi 128 16 (by decide), hi 144 16 (by decide), hi 256 8 (by decide), hi 264 8 (by decide),
    hi 272 8 (by decide), RegUpd.gpr_write, BitVec.setWidth_eq, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.mem_write, State.setV, Option.bind_some, Option.map_some, isa, runStep_some,
    Option.some.injEq, exists_eq_left']

theorem rebase_self {s₀ u : State} (h : ∀ r ∈ accRegs, u.gpr r = s₀.gpr r) : rebase s₀ u = s₀ := by
  simp only [rebase]
  cases s₀
  congr 1
  funext r
  by_cases hr : r ∈ accRegs <;> simp only [hr, ite_true, ite_false, h r]

/-- What the bulk leaves: `T` chunks done, and the bytes absorbed. -/
structure Bulked (enc : Bool) (R a : Nat) (s₀ : State) (T : Nat) (u : State) : Prop where
  pos : 1 ≤ T
  rest : L s₀ - 512 * T < 512
  inv : LInv (rebase s₀ u) T u
  cs : ∀ r ∈ preserved, u.gpr r = (rebase s₀ u).gpr r
  v8 : u.v .v8 = s₀.v .v8
  v9 : u.v .v9 = s₀.v .v9
  acc : Acc R (absorbAll R a (if enc then bytesAt u.mem (dp s₀) (512 * (T - 1))
    else bytesAt s₀.mem (dp s₀) (512 * T))) u

/-- Leaving, after the chunks. -/
theorem leave_bulk {enc : Bool} {s₀ : State} (hp : BPre s₀) {R a : Nat} {u : State} {T : Nat}
    (hT : 1 ≤ T) (hr : L s₀ - 512 * T < 512) (h : BulkInv (rebase s₀ u) T u)
    (ha : Acc R (absorbAll R a (if enc then bytesAt u.mem (dp s₀) (512 * (T - 1))
      else bytesAt s₀.mem (dp s₀) (512 * T))) u) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.leave) u (Bulked enc R a s₀ T) := by
  have hi : ∀ d n, d + n ≤ 320 → InRegions (u.rd ++ u.wr) (u.gpr .x3 + BitVec.ofNat 64 d) n := by
    intro d n hd
    rw [h.rd, h.wr, h.x3]
    simp only [rebase_rd, rebase_wr, bp_rebase, hp.rd, hp.wr]
    exact ⟨bR s₀, by simp, Offset.contains_base _ hd (by omega)⟩
  refine (WP.both (leave_ok (hp.rebase u).toXPre h) (leave_mem u hi)).mono
    fun v ⟨⟨hl, hcs, h8, h9⟩, hm⟩ => ?_
  have hacc : ∀ r ∈ accRegs, v.gpr r = u.gpr r := fun r hr =>
    (hcs r (acc_preserved r hr).1).trans (rebase_acc hr)
  have e := rebase_congr s₀ hacc
  refine ⟨hT, hr, e ▸ hl, fun r hr => by rw [e]; exact hcs r hr, by simpa using h8,
    by simpa using h9, ?_⟩
  rw [hm]
  exact ha.frame (acc_regs_keep hacc) fun d _ => by
    simp only [Poly.rword, hm, hl.x0, h.x0]

theorem bytesAt_zero (m : Mem) (p : Addr) : bytesAt m p 0 = [] := rfl

theorem bulk_ok (enc : Bool) {s₀ : State} (hp : BPre s₀) (hL : 512 ≤ L s₀) {R a : Nat}
    (ha : Acc R a s₀) :
    WP isa (bulk sve enc) s₀ fun u => ∃ T, Bulked enc R a s₀ T u := by
  have ho : ∀ d n, d + n ≤ 320 → InRegions s₀.wr (s₀.gpr .x3 + BitVec.ofNat 64 d) n := by
    intro d n hd
    rw [hp.wr]
    exact ⟨bR s₀, by simp, Offset.contains_base _ hd (by omega)⟩
  have nil (m : Mem) (k : Nat) (hk : k = 0) :
      absorbAll R a (bytesAt m (dp s₀) (512 * k)) = a := by
    rw [hk, Nat.mul_zero, bytesAt_zero, Poly1305.absorbAll_nil]
  unfold bulk
  apply WP.seq
  refine (WP.both (enter_ok hp.toXPre (linv0 s₀) (fun _ _ => rfl) rfl) (enter_frame s₀ ho)).mono
    fun s₁ ⟨h₁, f₁⟩ => ?_
  have acc₁ : ∀ r ∈ accRegs, s₁.gpr r = s₀.gpr r := fun r hr =>
    h₁.cs r (acc_preserved r hr).1 (acc_preserved r hr).2.2.2 (acc_preserved r hr).2.1
      (acc_preserved r hr).2.2.1
  have rw₁ := rword_eq f₁ h₁.x0 (key_enter hp)
  have ha₁ : Acc R a s₁ := ha.frame (acc_regs_keep acc₁) rw₁
  have hb₁ : BulkInv (rebase s₀ s₁) 0 s₁ := by rw [rebase_self acc₁]; exact h₁
  apply WP.seq
  cases enc
  · -- Decrypting: every chunk absorbs itself.
    simp only [Bool.false_eq_true, ite_false]
    refine (chunks_open hp (R := R) (a := a) (t := 0) (by omega) hb₁
      (by rw [nil _ _ rfl]; exact ha₁)).mono fun u ⟨T, hr, hT, hu, hau⟩ => ?_
    exact (leave_bulk (enc := false) hp (by omega) hr hu (by simpa using hau)).mono
      fun w hw => ⟨T, hw⟩
  · -- Encrypting: the first chunk is the kernel's.
    simp only [ite_true]
    apply WP.seq
    apply WP.seq
    refine (VG.Proof.ChaCha20.AArch64.Mixed8.chunk_ok s₁ (cp_of_inv hp.toXPre h₁ (by omega))).mono
      fun g hg => ?_
    refine (next_after hp.toXPre (t := 0) (by omega) h₁ hg).mono fun v ⟨⟨hv, h5⟩, hkeep, hf⟩ => ?_
    have accv : ∀ r ∈ accRegs, v.gpr r = s₀.gpr r := fun r hr =>
      (hkeep r (by intro he; rw [he] at hr; exact absurd hr (by decide))
        (by intro he; rw [he] at hr; exact absurd hr (by decide))
        (by intro he; rw [he] at hr; exact absurd hr (by decide))
        (by intro he; rw [he] at hr; exact absurd hr (by decide))).trans
      ((hg.cs r (acc_preserved r hr).1 (acc_preserved r hr).2.1 (acc_preserved r hr).2.2.1).trans
        (acc₁ r hr))
    have hfv : Frame (enterR s₀ ++ [sr s₁, scalarBuf s₁, dr s₁] ++ [stR s₀]) s₀.mem v.mem :=
      ((f₁.mono (by simp)).trans (hg.frame.mono (by simp))).trans (hf.mono (by simp))
    have hx0v : v.gpr .x0 = s₀.gpr .x0 :=
      (hkeep _ (by decide) (by decide) (by decide) (by decide)).trans (hg.x0.trans h₁.x0)
    have rwv := rword_eq hfv hx0v (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_append.mp hr with hr | hr
        · exact key_enter hp r hr
        · exact key_chunk hp h₁.toLInv (by omega) r hr
      · rw [List.mem_singleton.mp hr]; exact (hp.st_b.symm.sub_left hp.key_sub))
    have hav : Acc R (absorbAll R a (bytesAt v.mem (dp s₀) (512 * (1 - 1)))) v := by
      rw [nil _ _ rfl]; exact ha.frame (acc_regs_keep accv) rwv
    have hbv : BulkInv (rebase s₀ v) 1 v := by rw [rebase_self accv]; exact hv
    apply WP.ite (decide (L s₀ - 512 * (0 + 1) < 512))
      (VG.Proof.ChaCha20.AArch64.Mixed8.nonzero_short h5)
    · intro hs
      have hs' := of_decide_eq_true hs
      exact WP.block_nil ((leave_bulk (enc := true) hp (Nat.le_refl 1) (by omega) hbv
        (by simpa using hav)).mono fun w hw => ⟨1, hw⟩)
    · intro hs
      have hs' := of_decide_eq_false hs
      refine (chunks_seal hp (t := 1) (Nat.le_refl 1) (by omega) hbv hav).mono
        fun u ⟨T, hr, hT, hu, hau⟩ => ?_
      exact (leave_bulk (enc := true) hp (by omega) hr hu (by simpa using hau)).mono
        fun w hw => ⟨T, hw⟩

end VG.Proof.ChaCha20Poly1305.AArch64.Stitch
