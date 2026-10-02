import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Hash
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# ML-DSA verification on x86-64: the sponge leaks only addresses

Untrusted: everything here is checked by Lean. Two runs in the same layout
(`LRel`: layouts whose registers and stack pointer agree) stay in it across
code that keeps the layout (`LRel.step`), and `hash2` leaks the same in both
(`hash2_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt stateAt rates Repr squeezeFrom)

/-- Two runs in the layout, with the same layout registers and stack pointer. -/
def LRel (rbs wbs : List (Reg × Nat)) (x y : State) : Prop := Lay rbs wbs x ∧ Lay rbs wbs y ∧ SameB x y

theorem SameB.post {x y x' y' : State} {W₁ W₂ : List Region} (h : SameB x y) (hx : PostB x x' W₁)
    (hy : PostB y y' W₂) : SameB x' y' :=
  ⟨fun r hr => by rw [hx.bs r hr, hy.bs r hr, h.1 r hr], by rw [hx.rsp, hy.rsp, h.2]⟩

theorem LRel.post {rbs wbs : List (Reg × Nat)} {x y x' y' : State} {W₁ W₂ : List Region} (h : LRel rbs wbs x y)
    (hx : PostB x x' W₁) (hy : PostB y y' W₂) : LRel rbs wbs x' y' :=
  ⟨h.1.post hx, h.2.1.post hy, h.2.2.post hx hy⟩

/-- A piece of code that keeps the layout, from two runs in it, leaves two runs in it. -/
theorem LRel.step {rbs wbs : List (Reg × Nat)} {c : Prog isa}
    (htr : RelCT isa (LRel rbs wbs) c fun _ _ => True)
    (hok : ∀ x, Lay rbs wbs x → WP isa c x fun x' => ∃ W, PostB x x' W) :
    RelCT isa (LRel rbs wbs) c (LRel rbs wbs) :=
  RelCT.postDep htr (F := fun x x' => ∃ W, PostB x x' W) (fun x y h => ⟨hok x h.1, hok y h.2.1⟩)
    fun _ _ _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => h.post hx hy

theorem nil_tr {P : State → State → Prop} : RelCT isa P (.block []) P :=
  RelCT.postDep (block_nomem_tr fun _ hi => absurd hi List.not_mem_nil) (F := fun x x' => x' = x)
    (fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) fun _ _ _ _ h hx hy => hx ▸ hy ▸ h

theorem kzero_tr {P : State → State → Prop} (h : ∀ x y, P x y → x.gpr .rbx = y.gpr .rbx) :
    RelCT isa P (.block kzero) fun _ _ => True :=
  taintRel [.rbx] (fun x y hp r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h x y hp)
    (by taint_decide)

/-! ## The calls -/

theorem k_in {bs wbs : List (Reg × Nat)} (hk : kChk bs wbs = true) :
    inB bs (sc 0) 200 = true ∧ inB bs (sc 200) 640 = true := by
  simp only [kChk, Bool.and_eq_true] at hk; exact ⟨hk.1.1.1.2, hk.1.1.2⟩

theorem kk16 {s s1 : State} (hsp : s1.gpr .rsp = s.gpr .rsp) {R : Region} (h : (below (s.gpr .rsp) 32).Disjoint R) :
    (below (s1.gpr .rsp) 16).Disjoint R := by
  rw [hsp]; exact h.sub_left (below_sub (by omega) (by omega))

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) (hk : kChk (rbs ++ wbs) wbs = true)
include L hk

theorem kabs_args {src : Ptr} {len pos : Nat} (hp : pieceChk (rbs ++ wbs) src len = true) (hpos : pos < 136)
    {s1 : State} (h1 : Args (kabsArgs src len 136 pos) s s1) :
    AbsorbArgs s1 (pa s (sc 0)) (pa s src) (pa s (sc 200)) 136 pos len := by
  obtain ⟨d1, k1, k2, _, _⟩ := kChk_spec L hk
  simp only [pieceChk, Bool.and_eq_true] at hp
  obtain ⟨⟨p1, p2⟩, p3⟩ := hp
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := inB_spec p3; have := (L.ok _ hn).1; omega
  exact ⟨h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, by decide, hpos, by omega, d1, L.disj p1, L.disj p2,
    kk16 h1.rsp k1, kk16 h1.rsp (L.stkD p3), kk16 h1.rsp k2⟩

theorem kpad_args {pos : Nat} (hpos : pos < 136) {s1 : State} (h1 : Args (kpadArgs 136 pos 0x1f) s s1) :
    PadArgs s1 (pa s (sc 0)) (pa s (sc 200)) 136 pos := by
  obtain ⟨d1, k1, k2, _, _⟩ := kChk_spec L hk
  exact ⟨h1.r0, h1.r1, h1.r2, h1.r4, by decide, hpos, d1, kk16 h1.rsp k1, kk16 h1.rsp k2⟩

theorem ksqz_args {out : Ptr} {len : Nat} (ho : outChk (rbs ++ wbs) wbs out len = true) {s1 : State}
    (h1 : Args (ksqzArgs 136 out len) s s1) :
    SqueezeArgs s1 (pa s (sc 0)) (pa s out) (pa s (sc 200)) 136 0 len := by
  obtain ⟨d1, k1, k2, _, _⟩ := kChk_spec L hk
  simp only [outChk, Bool.and_eq_true] at ho
  obtain ⟨⟨⟨o1, o2⟩, o3⟩, _⟩ := ho
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := inB_spec o3; have := (L.ok _ hn).1; omega
  exact ⟨h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, by decide, by decide, by omega, (L.disj o1).symm, d1,
    L.disj o2, kk16 h1.rsp k1, kk16 h1.rsp (L.stkD o3), kk16 h1.rsp k2⟩

end


/-- A pointer's value agrees in two runs in the same layout. -/
theorem LRel.val {rbs wbs : List (Reg × Nat)} {x y : State} (h : LRel rbs wbs x y) {p : Ptr} {l : Nat}
    (hin : inB (rbs ++ wbs) p l = true) : (Arg.ptr p).val x = (Arg.ptr p).val y :=
  h.2.2.pa (ptr_bs h.1.ok hin)

theorem kabs_aok {bs wbs : List (Reg × Nat)} (hS : LayOk bs) (hk : kChk bs wbs = true) {src : Ptr} {len pos : Nat}
    (hp : pieceChk bs src len = true) (hpos : pos < 136) : ∀ a ∈ kabsArgs src len 136 pos, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [pieceChk, Bool.and_eq_true] at hp
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := inB_spec hp.2; have := (hS _ hn).1; omega
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok hS (k_in hk).1, by decide⟩, ⟨show 136 < 2 ^ 31 by decide, by decide⟩,
    ⟨show pos < 2 ^ 31 by omega, by decide⟩, ⟨ptr_ok hS hp.2, by decide⟩, ⟨hlen, by decide⟩,
    ⟨ptr_ok hS (k_in hk).2, by decide⟩⟩

theorem kpad_aok {bs wbs : List (Reg × Nat)} (hS : LayOk bs) (hk : kChk bs wbs = true) {pos : Nat} (hpos : pos < 136) :
    ∀ a ∈ kpadArgs 136 pos 0x1f, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok hS (k_in hk).1, by decide⟩, ⟨show 136 < 2 ^ 31 by decide, by decide⟩,
    ⟨show pos < 2 ^ 31 by omega, by decide⟩, ⟨show 0x1f < 2 ^ 31 by decide, by decide⟩,
    ⟨ptr_ok hS (k_in hk).2, by decide⟩⟩

theorem ksqz_aok {bs wbs : List (Reg × Nat)} (hS : LayOk bs) (hk : kChk bs wbs = true) {out : Ptr} {len : Nat}
    (ho : outChk bs wbs out len = true) : ∀ a ∈ ksqzArgs 136 out len, a.2.Ok ∧ a.1 ∈ argRegs := by
  simp only [outChk, Bool.and_eq_true] at ho
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := inB_spec ho.1.2; have := (hS _ hn).1; omega
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok hS (k_in hk).1, by decide⟩, ⟨show 136 < 2 ^ 31 by decide, by decide⟩,
    ⟨show 0 < 2 ^ 31 by decide, by decide⟩, ⟨ptr_ok hS ho.1.2, by decide⟩, ⟨hlen, by decide⟩,
    ⟨ptr_ok hS (k_in hk).2, by decide⟩⟩

theorem kabs_tr {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) (hk : kChk (rbs ++ wbs) wbs = true) {src : Ptr} {len pos : Nat}
    (hp : pieceChk (rbs ++ wbs) src len = true) (hpos : pos < 136) :
    RelCT isa (LRel rbs wbs) (kabs src len 136 pos) fun _ _ => True := by
  have hp' := hp
  simp only [pieceChk, Bool.and_eq_true] at hp'
  have p3 := hp'.2
  refine callAt_tr (k := Proof.Sha3.absorbX86_64) Proof.Sha3.X86_64.Stream.Absorb.absorb_correct
    Proof.Sha3.X86_64.Stream.Absorb.absorb_ct (kabs_aok hS hk hp hpos)
    (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 h h1 h2 => ?_
  · obtain ⟨_, _, _, w1, w2⟩ := kChk_spec h.1 hk
    obtain ⟨_, _, _, w1', w2'⟩ := kChk_spec h.2.1 hk
    refine ⟨_, _, _, _, absorb_pre (kabs_args h.1 hk hp hpos h1), absorb_pre (kabs_args h.2.1 hk hp hpos h2), ?_,
      covers_append (h.1.cR p3) (covers_wr (covers_cons w1 w2)), covers_cons w1 w2,
      covers_append (h.2.1.cR p3) (covers_wr (covers_cons w1' w2')), covers_cons w1' w2', h.2.2.2⟩
    simp only [Proof.Sha3.absorbX86_64, State.withRegions_gpr, State.callEntry_rsp,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide)]
    rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, h2.r0, h2.r1, h2.r2, h2.r3, h2.r4, h2.r5, h1.rsp, h2.rsp,
      h.val (k_in hk).1, h.val (k_in hk).2, h.val p3, h.2.2.2]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


theorem kpad_tr {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) (hk : kChk (rbs ++ wbs) wbs = true) {pos : Nat}
    (hpos : pos < 136) : RelCT isa (LRel rbs wbs) (kpad 136 pos 0x1f) fun _ _ => True := by
  refine callAt_tr (k := Proof.Sha3.padX86_64) Proof.Sha3.X86_64.Stream.Pad.pad_correct
    Proof.Sha3.X86_64.Stream.Pad.pad_ct (kpad_aok hS hk hpos)
    (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 h h1 h2 => ?_
  obtain ⟨_, _, _, w1, w2⟩ := kChk_spec h.1 hk
  obtain ⟨_, _, _, w1', w2'⟩ := kChk_spec h.2.1 hk
  refine ⟨_, _, _, _, pad_pre (kpad_args h.1 hk hpos h1), pad_pre (kpad_args h.2.1 hk hpos h2), ?_,
    covers_append covers_nil (covers_wr (covers_cons w1 w2)), covers_cons w1 w2,
    covers_append covers_nil (covers_wr (covers_cons w1' w2')), covers_cons w1' w2', h.2.2.2⟩
  simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide)]
  rw [h1.r0, h1.r1, h1.r2, h1.r4, h2.r0, h2.r1, h2.r2, h2.r4, h1.rsp, h2.rsp,
    h.val (k_in hk).1, h.val (k_in hk).2, h.2.2.2]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ksqz_tr {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) (hk : kChk (rbs ++ wbs) wbs = true)
    {out : Ptr} {len : Nat} (ho : outChk (rbs ++ wbs) wbs out len = true) :
    RelCT isa (LRel rbs wbs) (ksqz 136 out len) fun _ _ => True := by
  have ho' := ho
  simp only [outChk, Bool.and_eq_true] at ho'
  obtain ⟨⟨⟨_, _⟩, o3⟩, o4⟩ := ho'
  refine callAt_tr (k := Proof.Sha3.squeezeX86_64) Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct
    Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct (ksqz_aok hS hk ho)
    (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 h h1 h2 => ?_
  obtain ⟨_, _, _, w1, w2⟩ := kChk_spec h.1 hk
  obtain ⟨_, _, _, w1', w2'⟩ := kChk_spec h.2.1 hk
  refine ⟨_, _, _, _, squeeze_pre (ksqz_args h.1 hk ho h1), squeeze_pre (ksqz_args h.2.1 hk ho h2), ?_,
    covers_append covers_nil (covers_wr (covers_cons w1 (covers_cons (h.1.cW o4) w2))),
    covers_cons w1 (covers_cons (h.1.cW o4) w2),
    covers_append covers_nil (covers_wr (covers_cons w1' (covers_cons (h.2.1.cW o4) w2'))),
    covers_cons w1' (covers_cons (h.2.1.cW o4) w2'), h.2.2.2⟩
  simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide)]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, h2.r0, h2.r1, h2.r2, h2.r3, h2.r4, h2.r5, h1.rsp, h2.rsp,
    h.val (k_in hk).1, h.val (k_in hk).2, h.val o3, h.2.2.2]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hash2_tr {rbs wbs : List (Reg × Nat)} (hS : LayOk (rbs ++ wbs)) {a b out : Ptr} {la lb len : Nat}
    (hc : hashChk (rbs ++ wbs) wbs a la b lb out len = true) :
    RelCT isa (LRel rbs wbs) (hash2 a la b lb out len) fun _ _ => True := by
  have hc' := hc
  simp only [hashChk, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, pa'⟩, pb⟩, ho⟩, _⟩, _⟩, _⟩, hla⟩, _⟩ := hc'
  unfold hash2
  refine RelCT.seq (LRel.step (kzero_tr fun x y h => h.2.2.1 _ (by decide))
    fun x Lx => WP.mono (kzero_ok x (kChk_spec Lx hk).2.2.2.1) fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (LRel.step (kabs_tr hS hk pa' (by decide))
    fun x Lx => WP.mono (kabs_ok Lx hk pa' (by decide)) fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (LRel.step (kabs_tr hS hk pb (Nat.mod_lt _ (by decide)))
    fun x Lx => WP.mono (kabs_ok Lx hk pb (Nat.mod_lt _ (by decide))) fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (LRel.step (kpad_tr hS hk (Nat.mod_lt _ (by decide)))
    fun x Lx => WP.mono (kpad_ok Lx hk (Nat.mod_lt _ (by decide))) fun _ h => ⟨_, h.1⟩) ?_
  exact ksqz_tr hS hk ho

end VG.Proof.MlDsa.X86_64.Verify
