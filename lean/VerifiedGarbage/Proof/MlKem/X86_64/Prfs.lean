import VerifiedGarbage.Proof.MlKem.X86_64.TopBase
import VerifiedGarbage.Proof.MlKem.X86_64.PrfBatch

/-!
# ML-KEM on x86-64: several outputs of `PRF₂`

Untrusted: everything here is checked by Lean. In a layout:
`PRF₂(σ, N₀ + i)` to `scratch + o + 128 i` for each `i < n`, with `σ` at
`G + 32` (`PrfsPost`), one at a time (`prfsScalar_ok`, `prfsScalar_tr`) or
four at a time with AVX2, but for the first `prfsLead n`, one at a time
(`prfsAvx2_ok`, `prfsAvx2_tr`), whichever
implementation of `vg_mlkem_sample_ntt4` the top-level functions call goes
with (`Callee4.prfs`). Both write within `prfsW` and need what `prfsChk`
checks of the layout.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {rbs wbs : List (Reg × Nat)}

/-! ## Properties of every instruction, piece by piece -/

theorem ctlOk_seq {a b : Prog isa} (ha : ctlOk a = true) (hb : ctlOk b = true) : ctlOk (.seq a b) = true := by
  simp only [ctlOk, ha, hb, Bool.and_self, Bool.or_true]

theorem ctlOk_call {n : String} {c : Prog isa} (h : ctlOk c = true) : ctlOk (.call n c) = true := h

theorem all_call {p : Instr → Bool} {n : String} {c : Prog isa} (h : c.all p = true) :
    (Code.call n c : Prog isa).all p = true := h

theorem ctlOk_ite {c : Cond} {t e : Prog isa} (ht : ctlOk t = true) (he : ctlOk e = true) :
    ctlOk (.ite c t e) = true := by
  simp only [ctlOk, ht, he, Bool.and_self]

theorem all_ite {p : Instr → Bool} {c : Cond} {t e : Prog isa} (ht : t.all p = true) (he : e.all p = true) :
    (Code.ite c t e : Prog isa).all p = true := by
  simp only [Code.all, ht, he, Bool.and_self]

theorem all_seq {p : Instr → Bool} {a b : Prog isa} (ha : a.all p = true) (hb : b.all p = true) :
    (Code.seq a b : Prog isa).all p = true := by
  simp only [Code.all, ha, hb, Bool.and_self]


/-! ## What a piece writes, weakened -/

/-- `PPost` for larger regions. -/
theorem PPost.weaken {s s' : State} {ws ws' : List (Ptr × Nat)} (h : PPost s s' ws)
    (hs : ∀ w ∈ ws, ∃ w' ∈ ws', Region.Sub (toR s w) (toR s w')) : PPost s s' ws' :=
  ⟨h.rd, h.wr, h.cs, h.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      obtain ⟨w', hw', hsub⟩ := hs w hw
      exact ⟨toR s w', List.mem_append_left _ (List.mem_map_of_mem hw'), hsub⟩
    · exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩⟩

/-! ## One output -/

/-- What `prf1 N out` writes. -/
abbrev prf1W (out : Ptr) : List (Ptr × Nat) := [(sc oNB, 1), (sc 0, 200), (sc 200, 640), (out, 128)]

def prf1Chk (bs wbs : List (Reg × Nat)) (out : Ptr) : Bool :=
  inB bs (sc oNB) 1 && inB wbs (sc oNB) 1 && hashChk bs wbs [(sigP, 32), (sc oNB, 1)] 136 out 128 &&
    keepB bs [(sc oNB, 1)] sigP 32

theorem prf1Chk_spec {bs wbs : List (Reg × Nat)} {out : Ptr} (h : prf1Chk bs wbs out = true) :
    inB bs (sc oNB) 1 = true ∧ inB wbs (sc oNB) 1 = true ∧
      hashChk bs wbs [(sigP, 32), (sc oNB, 1)] 136 out 128 = true ∧ keepB bs [(sc oNB, 1)] sigP 32 = true := by
  simp only [prf1Chk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  exact ⟨h0, h1, h2, h3⟩

theorem prf1_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N : Nat} (hN : N < 256)
    {out : Ptr} (hc : prf1Chk (rbs ++ wbs) wbs out = true) :
    WP isa (prf1 N out) s fun s' => PPost s s' (prf1W out) ∧
      bytesAt s'.mem (pa s out) 128 = prf 2 (bytesAt s.mem (pa s sigP) 32) (BitVec.ofNat 8 N) := by
  obtain ⟨_, hNB, hh, hk⟩ := prf1Chk_spec hc
  have hocs : out.1 ∈ calleeSaved := (hashChk_spec hh).2.2.2.2.2
  unfold prf1
  refine WP.seq (WP.mono (setB_okL L (by decide) hN hNB) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have L₁ := L.post hP₁.b hcs
  refine WP.mono (hash_ok hcs hh (by decide) L₁) fun s₂ ⟨hP₂, ho₂⟩ =>
    ⟨PPost.app hP₁ hP₂ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro w (rfl | rfl | rfl) <;>
      first | decide | exact hocs), ?_⟩
  have e1 : pa s₁ (sc oNB) = pa s (sc oNB) := hP₁.pa rbx_cs
  have eo : pa s₁ out = pa s out := hP₁.pa hocs
  have hσ : bytesAt s₁.mem (pa s₁ sigP) 32 = bytesAt s.mem (pa s sigP) 32 := L.keepBytes hP₁.b hk
  rw [← eo, ho₂, prf_pieces (by rw [e1]; exact hb₁), hσ, shake31]
  exact (prf_eq 2 _ _).symm

theorem setNB_taint (N : Nat) :
    (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (setB (sc oNB) N)) (.block [])).isSome = true := by
  kernel_rfl

theorem prf1_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N : Nat} (hN : N < 256) {out : Ptr}
    (hc : prf1Chk (rbs ++ wbs) wbs out = true) : RelCT isa (LRel rbs wbs) (prf1 N out) (LRel rbs wbs) := by
  obtain ⟨hin, hNB, hh, _⟩ := prf1Chk_spec hc
  unfold prf1
  exact RelCT.seq (LRel.step hcs (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq hin) (setNB_taint N))
    fun x Lx => WP.mono (setB_okL Lx (by decide) hN hNB) fun _ h => ⟨_, h.1⟩)
    (LRel.step hcs (hash_tr hcs hh (by decide)) fun x Lx => WP.mono (hash_ok hcs hh (by decide) Lx) fun _ h => ⟨_, h.1⟩)

theorem prf1_ctl (N : Nat) (out : Ptr) : ctlOk (prf1 N out) = true := by kernel_rfl

theorem prf1_sp (N : Nat) (out : Ptr) : (prf1 N out).all (fun i => !isa.writesSp i) = true := by kernel_rfl

/-! ## Several outputs -/

/-- What `prfs N₀ n o wl` writes, of either implementation: the index `N`,
the Keccak state and the sponge functions' working space, 2368 bytes of
working space from lane `wl`, and the outputs. -/
abbrev prfsW (n o wl : Nat) : List (Ptr × Nat) :=
  [(sc oNB, 1), (sc 0, 200), (sc 200, 640), (sc (32 * wl), 2368), (sc o, 128 * n)]

/-- What `prfs N₀ n o wl` needs of the layout, of either implementation:
for each output, what computing it on its own needs, and that this keeps `σ`
and the outputs before it; and that the working space, the outputs and `σ`
are apart. -/
def prfsChk (bs wbs : List (Reg × Nat)) (n o wl : Nat) : Bool :=
  (List.range n).all (fun i => prf1Chk bs wbs (sc (o + 128 * i)) && keepB bs (prf1W (sc (o + 128 * i))) sigP 32 &&
    (List.range i).all fun j => keepB bs (prf1W (sc (o + 128 * i))) (sc (o + 128 * j)) 128) &&
  wrOk bs wbs (sc (32 * wl)) 2368 && wrOk bs wbs (sc o) (128 * n) && rdOk bs sigP 32 &&
  sepB bs (sc (32 * wl)) 2368 (sc o) (128 * n) && sepB bs (sc (32 * wl)) 2368 sigP 32 &&
  sepB bs (sc o) (128 * n) sigP 32 && decide (32 * wl + 2368 < 2 ^ 31)

theorem prfsChk_spec {bs wbs : List (Reg × Nat)} {n o wl : Nat} (h : prfsChk bs wbs n o wl = true) :
    (∀ i < n, prf1Chk bs wbs (sc (o + 128 * i)) = true ∧ keepB bs (prf1W (sc (o + 128 * i))) sigP 32 = true ∧
      ∀ j < i, keepB bs (prf1W (sc (o + 128 * i))) (sc (o + 128 * j)) 128 = true) ∧
    wrOk bs wbs (sc (32 * wl)) 2368 = true ∧ wrOk bs wbs (sc o) (128 * n) = true ∧ rdOk bs sigP 32 = true ∧
    sepB bs (sc (32 * wl)) 2368 (sc o) (128 * n) = true ∧ sepB bs (sc (32 * wl)) 2368 sigP 32 = true ∧
    sepB bs (sc o) (128 * n) sigP 32 = true ∧ 32 * wl + 2368 < 2 ^ 31 := by
  simp only [prfsChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨fun i hi => ⟨(h0 i hi).1.1, (h0 i hi).1.2, (h0 i hi).2⟩, h1, h2, h3, h4, h5, h6, h7⟩

/-- What `prfs N₀ n o wl` leaves, from `s`. -/
def PrfsPost (s : State) (N₀ n o wl : Nat) (s' : State) : Prop :=
  PPost s s' (prfsW n o wl) ∧
    ∀ i < n, bytesAt s'.mem (pa s (sc (o + 128 * i))) 128 =
      prf 2 (bytesAt s.mem (pa s sigP) 32) (BitVec.ofNat 8 (N₀ + i))

/-! ## One at a time -/

/-- Output `i` lies within the outputs. -/
theorem out_sub (s : State) {n o i : Nat} (hi : i < n) :
    Region.Sub (toR s (sc (o + 128 * i), 128)) (toR s (sc o, 128 * n)) :=
  show Region.Sub ⟨s.gpr .rbx + BitVec.ofNat 64 (o + 128 * i), 128⟩ ⟨s.gpr .rbx + BitVec.ofNat 64 o, 128 * n⟩ from
    Offset.sub _ (by omega) (by omega)

/-- After the first `k` outputs. -/
structure ScInv (s : State) (N₀ n o wl k : Nat) (s' : State) : Prop where
  post : PPost s s' (prfsW n o wl)
  sig : bytesAt s'.mem (pa s' sigP) 32 = bytesAt s.mem (pa s sigP) 32
  outs : ∀ j < k, bytesAt s'.mem (pa s (sc (o + 128 * j))) 128 =
    prf 2 (bytesAt s.mem (pa s sigP) 32) (BitVec.ofNat 8 (N₀ + j))

/-- The first `r` of `n` outputs, one at a time. -/
theorem prfsScalar_lead {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ r n o wl : Nat}
    (hN : N₀ + r ≤ 256) (hr : r ≤ n)
    (hs : ∀ i < r, prf1Chk (rbs ++ wbs) wbs (sc (o + 128 * i)) = true ∧
      keepB (rbs ++ wbs) (prf1W (sc (o + 128 * i))) sigP 32 = true ∧
      ∀ j < i, keepB (rbs ++ wbs) (prf1W (sc (o + 128 * i))) (sc (o + 128 * j)) 128 = true) :
    WP isa (prfsScalar N₀ r o wl) s (ScInv s N₀ n o wl r) := by
  have h := seqR_ok (f := fun i => prf1 (N₀ + i) (sc (o + 128 * i))) (I := ScInv s N₀ n o wl) r 0
    (fun k _ hk s₁ h₁ => by
      obtain ⟨c1, cs, cj⟩ := hs k (by omega)
      have L₁ := L.post h₁.post.b hcs
      refine WP.mono (prf1_ok L₁ hcs (by omega) c1) fun s₂ ⟨hP, hb⟩ => ?_
      have e₁ : ∀ x, pa s₁ (sc x) = pa s (sc x) := fun x => h₁.post.pa rbx_cs
      refine ⟨PPost.trans h₁.post (hP.weaken fun w hw => ?_) (fun w hw => by
          simp only [prfsW, List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact rbx_cs) (fun w hw => hw) (fun w hw => hw),
        by rw [L₁.keepBytes hP.b cs]; exact h₁.sig, fun j hj => ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
        · exact ⟨_, by simp, out_sub s₁ (o := o) (show k < n by omega)⟩
      · rcases (by omega : j < k ∨ j = k) with hj | rfl
        · rw [← e₁, ← hP.pa rbx_cs, L₁.keepBytes hP.b (cj j hj), e₁]; exact h₁.outs j hj
        · rw [← e₁, hb, h₁.sig])
    s ⟨Post.refl _ _, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact WP.mono h fun s' h' => by rwa [Nat.zero_add] at h'

theorem prfsScalar_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ n o wl : Nat}
    (hN : N₀ + n + 4 ≤ 256) (hc : prfsChk (rbs ++ wbs) wbs n o wl = true) :
    WP isa (prfsScalar N₀ n o wl) s (PrfsPost s N₀ n o wl) :=
  WP.mono (prfsScalar_lead L hcs (by omega) (Nat.le_refl n) (prfsChk_spec hc).1) fun _ h' => ⟨h'.post, h'.outs⟩

theorem prfsScalar_trL (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ r o wl : Nat} (hN : N₀ + r ≤ 256)
    (hs : ∀ i < r, prf1Chk (rbs ++ wbs) wbs (sc (o + 128 * i)) = true) :
    RelCT isa (LRel rbs wbs) (prfsScalar N₀ r o wl) (LRel rbs wbs) := by
  have := seqR_tr (f := fun i => prf1 (N₀ + i) (sc (o + 128 * i))) (R := fun _ => LRel rbs wbs) r 0 fun k _ hk =>
    prf1_tr hcs (by omega) (hs k (by omega))
  exact this

theorem prfsScalar_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ n o wl : Nat} (hN : N₀ + n + 4 ≤ 256)
    (hc : prfsChk (rbs ++ wbs) wbs n o wl = true) :
    RelCT isa (LRel rbs wbs) (prfsScalar N₀ n o wl) fun _ _ => True :=
  RelCT.mono (prfsScalar_trL hcs (by omega) fun i hi => ((prfsChk_spec hc).1 i hi).1) (fun _ _ h => h)
    fun _ _ _ => trivial

theorem ctlOk_seqR {f : Nat → Prog isa} (h : ∀ k, ctlOk (f k) = true) : ∀ n a, ctlOk (seqR f a n) = true
  | 0, _ => rfl
  | n + 1, a => ctlOk_seq (h a) (ctlOk_seqR h n (a + 1))

theorem all_seqR {p : Instr → Bool} {f : Nat → Prog isa} (h : ∀ k, (f k).all p = true) :
    ∀ n a, (seqR f a n).all p = true
  | 0, _ => rfl
  | n + 1, a => all_seq (h a) (all_seqR h n (a + 1))

theorem prfsScalar_ctl (N₀ n o wl : Nat) : ctlOk (prfsScalar N₀ n o wl) = true :=
  ctlOk_seqR (fun _ => prf1_ctl _ _) n 0

theorem prfsScalar_sp (N₀ n o wl : Nat) : (prfsScalar N₀ n o wl).all (fun i => !isa.writesSp i) = true :=
  all_seqR (fun _ => prf1_sp _ _) n 0

/-! ## Four at a time -/

namespace Prf4

open VG.Impl.MlKem.X86_64.Prf4

/-- What `prfsX4 N₀ n o wl` needs, with `scratch` at `b`. -/
structure RawPre (b : Addr) (n o wl : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = b
  w : InRegions s.wr (sP b wl) 2368
  out : InRegions s.wr (b + BitVec.ofNat 64 o) (128 * n)
  sig : InRegions (s.rd ++ s.wr) (sS b) 32
  dWO : (wR b wl).Disjoint (oR b o n)
  dWS : (wR b wl).Disjoint (sR b)
  dOS : (oR b o n).Disjoint (sR b)
  small : 32 * wl + 2368 < 2 ^ 31
  so : o + 128 * n < 2 ^ 32

theorem lt64 {a o : Nat} (h : o + a < 2 ^ 32) : a < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_trans h (by decide))

theorem RawPre.bpre {b : Addr} {n o wl : Nat} {s : State} (h : RawPre b n o wl s) {m : Nat} (hm : m ≤ 4)
    (hmn : m ≤ n) : BPre b wl o m s := by
  have hs : Region.Sub (oR b o m) (oR b o n) := Region.sub_prefix (by omega)
  refine ⟨h.rbx, h.w, ?_, h.sig, h.dWO.sub_right hs, h.dWS, h.dOS.sub_left hs, hm, h.small⟩
  have := inRegions_sub h.out (off := 0) (l := 128 * m) (by omega) (lt64 h.so)
  rwa [add_ofNat_zero] at this

theorem prfsX4_raw {b : Addr} {wl : Nat} :
    ∀ (n N₀ o : Nat) (s : State), RawPre b n o wl s → N₀ + n + 4 ≤ 256 →
      WP isa (prfsX4 N₀ n o wl) s fun s' => BEnv b wl o n s s' ∧
        ∀ k < n, bytesAt s'.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 =
          prf 2 (sig b s) (BitVec.ofNat 8 (N₀ + k))
  | 0, _, _, _, _, _ => WP.block_nil ⟨BEnv.refl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | 1, N₀, o, s, h, hN =>
    show WP isa (batch N₀ 1 o wl) s _ from batch_ok (h.bpre (m := 1) (by decide) (by decide)) (by omega)
  | 2, N₀, o, s, h, hN =>
    show WP isa (batch N₀ 2 o wl) s _ from batch_ok (h.bpre (m := 2) (by decide) (by decide)) (by omega)
  | 3, N₀, o, s, h, hN =>
    show WP isa (batch N₀ 3 o wl) s _ from batch_ok (h.bpre (m := 3) (by decide) (by decide)) (by omega)
  | n + 4, N₀, o, s, h, hN => by
    show WP isa (.seq (batch N₀ 4 o wl) (prfsX4 (N₀ + 4) n (o + 512) wl)) s _
    have so := h.so
    have hs4 : Region.Sub (oR b o 4) (oR b o (n + 4)) := Region.sub_prefix (by omega)
    have hsn : Region.Sub (oR b (o + 512) n) (oR b o (n + 4)) := Offset.sub _ (by omega) (by omega)
    refine WP.seq (WP.mono (batch_ok (h.bpre (by decide) (by omega)) (by omega)) fun s₁ ⟨e₁, r₁⟩ => ?_)
    have hsig : sig b s₁ = sig b s := bytesAt_frame e₁.frame (by
      simpa using ⟨h.dWS.symm, (h.dOS.sub_left hs4).symm⟩) (by decide)
    have h₁ : RawPre b n (o + 512) wl s₁ := by
      refine ⟨(e₁.cs .rbx (by decide)).trans h.rbx, by rw [e₁.wr]; exact h.w, ?_, by rw [e₁.rd, e₁.wr]; exact h.sig,
        h.dWO.sub_right hsn, h.dWS, h.dOS.sub_left hsn, h.small, by omega⟩
      have := inRegions_sub h.out (off := 512) (l := 128 * n) (by omega) (lt64 h.so)
      rw [e₁.wr, ← Offset.add_add]; exact this
    refine WP.mono (prfsX4_raw n (N₀ + 4) (o + 512) s₁ h₁ (by omega)) fun s₂ ⟨e₂, r₂⟩ =>
      ⟨⟨e₂.rd.trans e₁.rd, e₂.wr.trans e₁.wr, fun r hr => (e₂.cs r hr).trans (e₁.cs r hr),
        (e₁.frame.sub ?_).trans (e₂.frame.sub ?_)⟩, fun k hk => ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), hs4⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), hsn⟩
    · rcases (by omega : k < 4 ∨ 4 ≤ k) with hk' | hk'
      · rw [bytesAt_frame e₂.frame (by
          have hk4 : Region.Sub ⟨b + BitVec.ofNat 64 (o + 128 * k), 128⟩ (oR b o (n + 4)) :=
            Offset.sub _ (by omega) (by omega)
          have hd : Region.Disjoint ⟨b + BitVec.ofNat 64 (o + 128 * k), 128⟩ (oR b (o + 512) n) :=
            Offset.disjoint _ (by omega) (by omega) (by omega)
          simpa using ⟨(h.dWO.sub_right hk4).symm, hd⟩) (by decide)]
        exact r₁ k hk'
      · have := r₂ (k - 4) (by omega)
        rwa [hsig, show o + 512 + 128 * (k - 4) = o + 128 * k by omega, show N₀ + 4 + (k - 4) = N₀ + k by omega]
          at this

theorem prfsX4_rtr {wl : Nat} : ∀ (n N₀ o : Nat),
    RelCT isa (fun x y => x.gpr .rbx = y.gpr .rbx) (prfsX4 N₀ n o wl) fun x y => x.gpr .rbx = y.gpr .rbx
  | 0, _, _ => nil_tr
  | 1, _, _ => batch_tr (m := 1) (fun _ _ h => h) _ _ _ (by decide)
  | 2, _, _ => batch_tr (m := 2) (fun _ _ h => h) _ _ _ (by decide)
  | 3, _, _ => batch_tr (m := 3) (fun _ _ h => h) _ _ _ (by decide)
  | n + 4, N₀, o => RelCT.seq (batch_tr (m := 4) (fun _ _ h => h) _ _ _ (by decide)) (prfsX4_rtr n (N₀ + 4) (o + 512))

theorem prfsX4_ctl {wl : Nat} : ∀ (n N₀ o : Nat), ctlOk (prfsX4 N₀ n o wl) = true
  | 0, _, _ => rfl
  | 1, _, _ => by kernel_rfl
  | 2, _, _ => by kernel_rfl
  | 3, _, _ => by kernel_rfl
  | n + 4, N₀, o => ctlOk_seq (by kernel_rfl) (prfsX4_ctl n (N₀ + 4) (o + 512))

theorem prfsX4_sp {wl : Nat} : ∀ (n N₀ o : Nat), (prfsX4 N₀ n o wl).all (fun i => !isa.writesSp i) = true
  | 0, _, _ => rfl
  | 1, _, _ => by kernel_rfl
  | 2, _, _ => by kernel_rfl
  | 3, _, _ => by kernel_rfl
  | n + 4, N₀, o => all_seq (by kernel_rfl) (prfsX4_sp n (N₀ + 4) (o + 512))

end Prf4

theorem cover_in {X : List Region} {a : Addr} {n : Nat} (h : Covers [⟨a, n⟩] X) : InRegions X a n :=
  h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem prfsLead_le (n : Nat) : prfsLead n ≤ n := by
  unfold prfsLead; split <;> omega

theorem prfsAvx2_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ n o wl : Nat}
    (hN : N₀ + n + 4 ≤ 256) (hc : prfsChk (rbs ++ wbs) wbs n o wl = true) :
    WP isa (prfsAvx2 N₀ n o wl) s (PrfsPost s N₀ n o wl) := by
  obtain ⟨hs, hw, ho, hsg, dwo, dws, dos, hsm⟩ := prfsChk_spec hc
  have hw' : inB wbs (sc (32 * wl)) 2368 = true := ((Bool.and_eq_true _ _).mp hw).2
  have ho' : inB wbs (sc o) (128 * n) = true := ((Bool.and_eq_true _ _).mp ho).2
  obtain ⟨n₀, hn₀, hl⟩ := inB_spec (rdOk_in ((Bool.and_eq_true _ _).mp ho).1)
  have := L.small _ hn₀
  have hb : o + 128 * n < 2 ^ 32 := Nat.lt_of_le_of_lt (show o + 128 * n ≤ n₀ from hl) this
  have i1 := cover_in (L.cW hw')
  have i2 := cover_in (L.cW ho')
  have i3 := cover_in (L.cR (rdOk_in hsg))
  have d1 := L.disj dwo
  have d2 := L.disj dws
  have d3 := L.disj dos
  have hr := prfsLead_le n
  unfold prfsAvx2
  generalize prfsLead n = r at hr ⊢
  refine WP.seq (WP.mono (prfsScalar_lead L hcs (by omega) hr fun i hi => hs i (by omega)) fun s₁ h₁ => ?_)
  have e₁ : s₁.gpr .rbx = s.gpr .rbx := h₁.post.cs .rbx (by decide)
  have hsub : Region.Sub (Prf4.oR (s.gpr .rbx) (o + 128 * r) (n - r)) (Prf4.oR (s.gpr .rbx) o n) :=
    Offset.sub _ (by omega) (by omega)
  have raw : Prf4.RawPre (s.gpr .rbx) (n - r) (o + 128 * r) wl s₁ := by
    refine ⟨e₁, by rw [h₁.post.wr]; exact i1, ?_, by rw [h₁.post.rd, h₁.post.wr]; exact i3, d1.sub_right hsub, d2,
      d3.sub_left hsub, hsm, by omega⟩
    have := inRegions_sub i2 (off := 128 * r) (l := 128 * (n - r)) (by omega) (Prf4.lt64 hb)
    rw [h₁.post.wr, ← Offset.add_add]; exact this
  have hsig : Prf4.sig (s.gpr .rbx) s₁ = bytesAt s.mem (pa s sigP) 32 := by
    rw [← h₁.sig]; simp only [Prf4.sig, Prf4.sS, pa, e₁]
  refine WP.mono (Prf4.prfsX4_raw (n - r) (N₀ + r) (o + 128 * r) s₁ raw (by omega)) fun s' ⟨e, out⟩ =>
    ⟨PPost.trans h₁.post ⟨e.rd, e.wr, e.cs, e.frame.sub fun r' hr' => ?_⟩ (fun w hw => by
      simp only [prfsW, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact rbx_cs) (fun w hw => hw) (fun w hw => hw), fun i hi => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · refine ⟨toR s₁ (sc (32 * wl), 2368), List.mem_append_left _ (List.mem_map_of_mem
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))), ?_⟩
      simp only [toR, pa, e₁]; exact fun _ h => h
    · refine ⟨toR s₁ (sc o, 128 * n), List.mem_append_left _ (List.mem_map_of_mem
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_singleton_self _)))))), ?_⟩
      simp only [toR, pa, e₁]; exact hsub
  · rcases (by omega : i < r ∨ r ≤ i) with hi' | hi'
    · rw [bytesAt_frame e.frame (by
        have hk : Region.Sub ⟨s.gpr .rbx + BitVec.ofNat 64 (o + 128 * i), 128⟩ (Prf4.oR (s.gpr .rbx) o n) :=
          Offset.sub _ (by omega) (by omega)
        have hd : Region.Disjoint ⟨s.gpr .rbx + BitVec.ofNat 64 (o + 128 * i), 128⟩
            (Prf4.oR (s.gpr .rbx) (o + 128 * r) (n - r)) := Offset.disjoint _ (by omega) (by omega) (by omega)
        simpa using ⟨(d1.sub_right hk).symm, hd⟩) (by decide)]
      exact h₁.outs i hi'
    · have := out (i - r) (by omega)
      rwa [hsig, show o + 128 * r + 128 * (i - r) = o + 128 * i by omega,
        show N₀ + r + (i - r) = N₀ + i by omega] at this

theorem prfsAvx2_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ n o wl : Nat} (hN : N₀ + n + 4 ≤ 256)
    (hc : prfsChk (rbs ++ wbs) wbs n o wl = true) :
    RelCT isa (LRel rbs wbs) (prfsAvx2 N₀ n o wl) fun _ _ => True := by
  obtain ⟨hs, -, -, hsg, -⟩ := prfsChk_spec hc
  have hr := prfsLead_le n
  unfold prfsAvx2
  generalize prfsLead n = r at hr ⊢
  exact RelCT.seq (prfsScalar_trL hcs (by omega) fun i hi => (hs i (by omega)).1)
    (RelCT.mono (Prf4.prfsX4_rtr _ _ _) (fun _ _ h => h.eq (rdOk_in hsg)) fun _ _ _ => trivial)

theorem prfsAvx2_ctl (N₀ n o wl : Nat) : ctlOk (prfsAvx2 N₀ n o wl) = true :=
  ctlOk_seq (prfsScalar_ctl _ _ _ _) (Prf4.prfsX4_ctl _ _ _)

theorem prfsAvx2_sp (N₀ n o wl : Nat) : (prfsAvx2 N₀ n o wl).all (fun i => !isa.writesSp i) = true :=
  all_seq (prfsScalar_sp _ _ _ _) (Prf4.prfsX4_sp _ _ _)

end VG.Proof.MlKem.X86_64
