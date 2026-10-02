import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Finish

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Rows6 (Data)

structure Same (s u : State) : Prop where
  gpr : u.gpr = s.gpr
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp

theorem Same.trans {s a u : State} (h : Same s a) (h' : Same a u) : Same s u :=
  ⟨h'.gpr.trans h.gpr,h'.rd.trans h.rd,h'.wr.trans h.wr,h'.sp.trans h.sp⟩

theorem xorScalarRow_ok (s : State) (k : Fin 8)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * k.val)) 16)
    (hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16) :
    WP isa (.block (xorScalarRow k)) s fun u =>
      u.mem = s.mem.write (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16
        (s.mem.read (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16 ^^^
          s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * k.val)) 16) ∧ Same s u := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16 := by
    obtain ⟨q,hq,hc⟩ := hout; exact ⟨q,List.mem_append_right _ hq,hc⟩
  have ha : (16 * k.val) % 16 = 0 ∧ 16 * k.val < 4096 * 16 := by omega
  have hb : (384 + 16 * k.val) % 16 = 0 ∧ 384 + 16 * k.val < 4096 * 16 := by omega
  apply WP.of_runBlock
  simp (config := {decide := true}) only [xorScalarRow,runBlock_cons,runBlock_nil,exec,addr,
    ha,hb,and_self,ite_true,State.load,hin,hi,State.setV,VOp.eval,State.store,hout,
    Option.bind_some,Option.map_some,isa,runStep_some,Option.some.injEq,exists_eq_left']
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem data_frame128 {m₀ m : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat}
    (h : Data m₀ m p out done) (hd : ∀ k ∈ done, k < 8) : Frame [⟨p,128⟩] m₀ m := by
  intro x hx
  have hn : ¬ (x - p).toNat < 128 := by
    have hh := hx ⟨p,128⟩ (by simp)
    simp only [Region.Contains] at hh
    omega
  rw [h x,ite_eq_right]
  intro hh
  have := hd _ hh.1
  omega

theorem xorScalarList_ok (ks : List (Fin 8)) (hn : ks.Nodup)
    {m₀ : Mem} {p b : Addr} {done : List Nat} {s : State}
    (h : Data m₀ s.mem p (fun k => m₀.read (b + BitVec.ofNat 64 (16 * k)) 16) done)
    (hd : ∀ k ∈ done, k < 8) (hp : s.gpr .x1 + BitVec.ofNat 64 384 = p) (hbp : s.gpr .x3 = b)
    (hdis : (⟨b,128⟩ : Region).Disjoint ⟨p,128⟩)
    (hf : ∀ k ∈ ks, k.val ∉ done)
    (hin : ∀ k : Fin 8, InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * k.val)) 16)
    (hout : ∀ k : Fin 8, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val)) 16) :
    WP isa (.block (ks.flatMap xorScalarRow)) s fun u =>
      Data m₀ u.mem p (fun k => m₀.read (b + BitVec.ofNat 64 (16 * k)) 16)
        (ks.map Fin.val ++ done) ∧ Same s u := by
  induction ks generalizing s done with
  | nil => exact WP.block_nil ⟨h,⟨rfl,rfl,rfl,rfl⟩⟩
  | cons k ks ih =>
    apply WP.block_append
    refine (xorScalarRow_ok s k (hin k) (hout k)).mono fun a ⟨hm,hs⟩ => ?_
    have he : s.gpr .x1 + BitVec.ofNat 64 (384 + 16 * k.val) =
        p + BitVec.ofNat 64 (16 * k.val) := by rw [BitVec.ofNat_add,← BitVec.add_assoc,hp]
    have hr : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * k.val)) 16 =
        m₀.read (b + BitVec.ofNat 64 (16 * k.val)) 16 := by
      rw [hbp]
      exact (data_frame128 h hd).read (r := ⟨b,128⟩) (Offset.contains_base _ (by omega) (by omega))
        (by intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hdis) (by decide)
    have ha : Data m₀ a.mem p (fun k => m₀.read (b + BitVec.ofNat 64 (16 * k)) 16) (k.val :: done) := by
      rw [hm,he,hr]
      exact h.store (by omega) (hf k (List.mem_cons_self ..))
    have hf' : ∀ l ∈ ks, l.val ∉ k.val :: done := by
      intro l hl
      simp only [List.mem_cons,not_or]
      exact ⟨fun he => (List.nodup_cons.mp hn).1 ((Fin.ext he) ▸ hl),
        hf l (List.mem_cons_of_mem _ hl)⟩
    have hin' : ∀ l : Fin 8, InRegions (a.rd ++ a.wr) (a.gpr .x3 + BitVec.ofNat 64 (16 * l.val)) 16 := by
      intro l; rw [hs.rd,hs.wr,hs.gpr]; exact hin l
    have hout' : ∀ l : Fin 8, InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (384 + 16 * l.val)) 16 := by
      intro l; rw [hs.wr,hs.gpr]; exact hout l
    refine (ih (List.nodup_cons.mp hn).2 ha (by
      intro l hl; simp only [List.mem_cons] at hl; rcases hl with rfl | hl
      · exact k.isLt
      · exact hd l hl) (by rw [hs.gpr]; exact hp) (by rw [hs.gpr]; exact hbp)
      hf' hin' hout').mono fun u ⟨hu,hsu⟩ => ⟨?_,hs.trans hsu⟩
    intro x
    simpa only [VG.Proof.ChaCha20.AArch64.Rows6.Data,List.map_cons,List.cons_append,
      List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hu x

end VG.Proof.ChaCha20.AArch64.Mixed8
